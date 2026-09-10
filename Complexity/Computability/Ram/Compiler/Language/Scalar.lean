/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Encoding
import Complexity.Computability.Ram.Compiler.Expr.Basic

/-!
# Compiling high-level scalar operations

The high-level values and operations have their own mathematical meaning. This
module lowers their Nat/Bool fragment to existing RAM expressions and reuses the
verified expression compiler. Range conditions concern the actual operands and
intermediate result, not only a function's eventual output.

The register map belongs to the backend and indexes every actual value field.
Scalar operations select their sole field; Unit bindings have no field and are
not accepted as one-word operands. The final theorem supplies actual
machine execution, its emitted-code length, the mathematical result and the
existing frame guarantee; no source cost table is assumed.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Source types represented by one word in this fragment. -/
inductive Scalar : Ty → Prop where
  | nat : Scalar .nat
  | bool : Scalar .bool

namespace Scalar

/-- Scalar observations are available only for actual one-word source types. -/
def toNat : {τ : Ty} → Scalar τ → Value τ → Nat
  | .nat, _, value => value
  | .bool, _, value => if value then 1 else 0
  | .unit, impossible, _ => nomatch impossible
  | .buffer _, impossible, _ => nomatch impossible
  | .prod _ _, impossible, _ => nomatch impossible
  | .option _, impossible, _ => nomatch impossible

/-- Every supported object cell has its ordinary scalar source type. -/
def cell (kind : CellTy) : Scalar kind.toTy :=
  match kind with
  | .nat => .nat
  | .bool => .bool

/-- A scalar operation selects the sole actual field of its operand. -/
def index {τ : Ty} (scalar : Scalar τ) : Fin (fieldCount τ) :=
  ⟨0, by cases scalar <;> decide⟩

@[simp] theorem index_val {τ : Ty} (scalar : Scalar τ) : scalar.index.val = 0 := rfl

/-- Scalar qualifications identify one-word types, not a second layout. -/
theorem fieldCount_eq_one {τ : Ty} (scalar : Scalar τ) : fieldCount τ = 1 := by
  cases scalar <;> rfl

/-- Every field of a scalar is its usual unsigned observation. -/
theorem valueField {τ : Ty} (scalar : Scalar τ) (placement : Nat → Word w) (value : Value τ)
    (i : Fin (fieldCount τ)) :
    LanguageCompiler.valueField placement value i = scalar.toNat value := by
  cases scalar <;> rfl

/-- The scalar range condition is exactly its field range condition. -/
theorem fits_iff {τ : Ty} (scalar : Scalar τ) (value : Value τ) :
    ValueFits w value ↔ scalar.toNat value < 2 ^ w := by
  cases scalar <;> rfl

end Scalar

/-- A represented scalar occupies an actual word. -/
theorem fieldCount_pos (scalar : Scalar τ) : 0 < fieldCount τ := by
  rw [scalar.fieldCount_eq_one]
  decide

/-- A backend assignment for every field of each lexical binding. -/
abbrev RegisterMap (Γ : List Ty) := ∀ {τ}, Var Γ τ → Fin (fieldCount τ) → Reg

namespace RegisterMap

/-- Every actual field has its exact mathematical value. -/
def Matches (layout : RegisterMap Γ) (placement : Nat → Word w)
    (env : Env Γ) (regs : Reg → Word w) : Prop :=
  ∀ {τ} (v : Var Γ τ) (i : Fin (fieldCount τ)),
    (regs (layout v i)).toNat = valueField placement (env.get v) i

/-- Source slots lie below the expression compiler's scratch register. -/
def Bounded (layout : RegisterMap Γ) (bound : Reg) : Prop :=
  ∀ {τ} (v : Var Γ τ) (i : Fin (fieldCount τ)), layout v i < bound

/-- Scalar expression proofs project the one field from the common relation. -/
theorem Matches.scalar {layout : RegisterMap Γ} {env : Env Γ} {regs : Reg → Word w}
    {placement : Nat → Word w} (matched : layout.Matches placement env regs)
    (scalar : Scalar τ) (v : Var Γ τ) :
    (regs (layout v scalar.index)).toNat = scalar.toNat (env.get v) :=
  (matched v scalar.index).trans (scalar.valueField placement (env.get v) scalar.index)

/-- Scalar expressions use the same inferred register bound as other fields. -/
theorem Bounded.scalar {layout : RegisterMap Γ} (bounded : layout.Bounded bound)
    (scalar : Scalar τ) (v : Var Γ τ) : layout v scalar.index < bound :=
  bounded v scalar.index

end RegisterMap

/-- Materialize one actual field. Object placement is not part of the code. -/
def atomFieldExpr (layout : RegisterMap Γ) :
    {τ : Ty} → Atom Γ τ → Fin (fieldCount τ) → Expr
  | _, .var v, i => .var (layout v i)
  | _, .nat n, _ => .const n
  | _, .bool b, _ => .const (if b then 1 else 0)
  | _, .unit, impossible => Fin.elim0 impossible

/-- Every atom field is represented exactly under the common value range. -/
theorem atomFieldExpr_toNat (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    {placement : Nat → Word w} (matched : layout.Matches placement env regs)
    (fits : ValueFits w (atom.eval env)) (i : Fin (fieldCount τ)) :
    ((atomFieldExpr layout atom i).eval regs mem).toNat =
      valueField placement (atom.eval env) i := by
  cases atom with
  | var v => exact matched v i
  | nat n => exact Word.ofNat_toNat_of_lt fits
  | bool b => exact Word.ofNat_toNat_of_lt fits
  | unit => exact Fin.elim0 i

/-- All fields obey the same inferred layout bound. -/
theorem atomFieldExpr_bounded (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (bounded : layout.Bounded dst) (i : Fin (fieldCount τ)) :
    (atomFieldExpr layout atom i).Bounded dst := by
  cases atom with
  | var v => exact bounded v i
  | nat | bool => trivial
  | unit => exact Fin.elim0 i

/-- Materializing an atom field executes one expression instruction. -/
@[simp] theorem atomFieldExpr_compile_length (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (i : Fin (fieldCount τ)) (dst : Reg) :
    ((atomFieldExpr layout atom i).compile dst).length = 1 := by
  cases atom with
  | var | nat | bool => rfl
  | unit => exact Fin.elim0 i

/-- Scalar operations use the sole field of the common atom materialization. -/
def atomExpr (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ) : Expr :=
  atomFieldExpr layout atom scalar.index

/-- An in-range atom is decoded exactly after lowering. -/
theorem atomExpr_toNat (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    (hw : 0 < w) {placement : Nat → Word w} (matched : layout.Matches placement env regs)
    (fits : ValueFits w (atom.eval env)) :
    ((atomExpr layout atom scalar).eval regs mem).toNat = scalar.toNat (atom.eval env) := by
  cases atom with
  | var v => exact matched.scalar scalar v
  | nat n => exact Word.ofNat_toNat_of_lt fits
  | bool b =>
      cases b <;>
        simp [atomExpr, atomFieldExpr, Expr.eval, Atom.eval, Scalar.toNat, BitVec.toNat_one hw]
  | unit => cases scalar

/-- Atom lowering respects the backend's inferred register bound. -/
theorem atomExpr_bounded (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (bounded : layout.Bounded dst) : (atomExpr layout atom scalar).Bounded dst := by
  cases atom with
  | var v => exact bounded.scalar scalar v
  | nat => trivial
  | bool => trivial
  | unit => cases scalar

/-- Scalar operations reuse the fixed word instruction vocabulary. A comparison
mask turns wrapping word subtraction into saturating natural subtraction. -/
def primExpr (layout : RegisterMap Γ) : {τ : Ty} → Prim Γ τ → Scalar τ → Expr
  | _, .atom a, scalar => atomExpr layout a scalar
  | _, .add a b, _ => .bin .add (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .mul a b, _ => .bin .mul (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .sub a b, _ =>
      .bin .mul (.bin .sub (atomExpr layout a .nat) (atomExpr layout b .nat))
        (.bin .ule (atomExpr layout b .nat) (atomExpr layout a .nat))
  | _, .div a b, _ => .bin .udiv (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .mod a b, _ => .bin .umod (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .eq a b, _ => .bin .eq (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .lt a b, _ => .bin .ult (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .le a b, _ => .bin .ule (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .length buffer, _ => atomFieldExpr layout buffer ⟨1, by change 1 < 2; decide⟩
  | _, .fst pair, scalar =>
      atomFieldExpr layout pair (scalar.index.castAdd _)
  | _, .snd pair, scalar =>
      atomFieldExpr layout pair (scalar.index.natAdd _)
  | _, .pair _ _, impossible => nomatch impossible
  | _, .none _, impossible => nomatch impossible
  | _, .some _, impossible => nomatch impossible

/-- Materialize a primitive's actual fields. Structured constructors and
projections copy existing fields; no heap traversal or inverse encoding occurs. -/
def primFieldExpr (layout : RegisterMap Γ) :
    {τ : Ty} → Prim Γ τ → Fin (fieldCount τ) → Expr
  | _, .atom atom, i => atomFieldExpr layout atom i
  | _, .add a b, _ => primExpr layout (.add a b) .nat
  | _, .mul a b, _ => primExpr layout (.mul a b) .nat
  | _, .sub a b, _ => primExpr layout (.sub a b) .nat
  | _, .div a b, _ => primExpr layout (.div a b) .nat
  | _, .mod a b, _ => primExpr layout (.mod a b) .nat
  | _, .eq a b, _ => primExpr layout (.eq a b) .bool
  | _, .lt a b, _ => primExpr layout (.lt a b) .bool
  | _, .le a b, _ => primExpr layout (.le a b) .bool
  | _, .length buffer, _ => primExpr layout (.length buffer) .nat
  | _, .pair left right, i =>
      Fin.addCases (atomFieldExpr layout left) (atomFieldExpr layout right) i
  | _, .fst pair, i => atomFieldExpr layout pair (i.castAdd _)
  | _, .snd pair, i => atomFieldExpr layout pair (i.natAdd _)
  | _, .none _, _ => .const 0
  | _, .some value, i => Fin.cases (.const 1) (atomFieldExpr layout value) i

/-- Ordered expressions for every field in one primitive result. -/
def primExprs (layout : RegisterMap Γ) (prim : Prim Γ τ) : List Expr :=
  List.ofFn (primFieldExpr layout prim)

@[simp] theorem primExprs_length (layout : RegisterMap Γ) (prim : Prim Γ τ) :
    (primExprs layout prim).length = fieldCount τ := List.length_ofFn

/-- The real option tag is stored before its fixed-width payload. -/
def optionTagExpr (layout : RegisterMap Γ) (value : Atom Γ (.option τ)) : Expr :=
  atomFieldExpr layout value ⟨0, Nat.zero_lt_succ _⟩

/-- Optional payload fields are only exposed by the selected `some` branch. -/
def optionPayloadExprs (layout : RegisterMap Γ) (value : Atom Γ (.option τ)) : List Expr :=
  List.ofFn fun i : Fin (fieldCount τ) => atomFieldExpr layout value i.succ

@[simp] theorem optionPayloadExprs_length (layout : RegisterMap Γ)
    (value : Atom Γ (.option τ)) :
    (optionPayloadExprs layout value).length = fieldCount τ := List.length_ofFn

@[simp] theorem optionTagExpr_compile_length (layout : RegisterMap Γ)
    (value : Atom Γ (.option τ)) (dst : Reg) :
    ((optionTagExpr layout value).compile dst).length = 1 :=
  atomFieldExpr_compile_length layout value ⟨0, Nat.zero_lt_succ _⟩ dst

/-- Source-level sufficient ranges for an operation. Addition and multiplication
include their actual results, even if later code returns a smaller value. Other
natural operations only require their operands to fit; subtraction and division
retain their entire mathematical domains, including underflow and zero divisors. -/
def PrimFits (w : Nat) (env : Env Γ) : {τ : Ty} → Prim Γ τ → Prop
  | _, .atom a => ValueFits w (a.eval env)
  | _, .add a b =>
      a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w ∧ a.eval env + b.eval env < 2 ^ w
  | _, .mul a b =>
      a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w ∧ a.eval env * b.eval env < 2 ^ w
  | _, .sub a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .div a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .mod a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .eq a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .lt a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .le a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .length buffer => (buffer.eval env).length < 2 ^ w
  | _, .pair left right => ValueFits w (left.eval env) ∧ ValueFits w (right.eval env)
  | _, .fst pair | _, .snd pair => ValueFits w (pair.eval env)
  | _, .none _ => True
  | _, .some value => 1 < 2 ^ w ∧ ValueFits w (value.eval env)

/-- The fixed lowering implements mathematical Nat/Bool semantics, not merely
equality modulo the word width. -/
theorem primExpr_toNat (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    (hw : 0 < w) {placement : Nat → Word w} (matched : layout.Matches placement env regs)
    (fits : PrimFits w env prim) :
    ((primExpr layout prim scalar).eval regs mem).toNat = scalar.toNat (prim.eval env) := by
  cases prim with
  | atom atom => exact atomExpr_toNat layout atom scalar env regs mem hw matched fits
  | add a b =>
      change (BinOp.eval .add _ _).toNat = a.eval env + b.eval env
      rw [BinOp.eval_add_toNat,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2.1]
      exact Nat.mod_eq_of_lt fits.2.2
  | mul a b =>
      change (BinOp.eval .mul _ _).toNat = a.eval env * b.eval env
      rw [BinOp.eval_mul_toNat,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2.1]
      exact Nat.mod_eq_of_lt fits.2.2
  | sub a b =>
      have saturated (x y : Word w) :
          (BinOp.eval .mul (BinOp.eval .sub x y) (BinOp.eval .ule y x)).toNat =
            x.toNat - y.toNat := by
        by_cases h : y.toNat ≤ x.toNat
        · simpa only [BinOp.eval_ule, if_pos h, BinOp.eval_mul,
            BitVec.ofNat_eq_ofNat, BitVec.mul_one] using
            BinOp.eval_sub_toNat_of_le x y h
        · simp only [BinOp.eval_ule, if_neg h, BinOp.eval_mul,
            BitVec.ofNat_eq_ofNat, BitVec.mul_zero,
            BitVec.toNat_zero, Nat.sub_eq_zero_of_le (Nat.le_of_not_le h)]
      change (BinOp.eval .mul (BinOp.eval .sub _ _) (BinOp.eval .ule _ _)).toNat =
        a.eval env - b.eval env
      simp only [saturated,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2, Scalar.toNat]
  | div a b =>
      change (BinOp.eval .udiv _ _).toNat = a.eval env / b.eval env
      simp only [BinOp.eval_udiv_toNat,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2, Scalar.toNat]
  | mod a b =>
      change (BinOp.eval .umod _ _).toNat = a.eval env % b.eval env
      simp only [BinOp.eval_umod_toNat,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2, Scalar.toNat]
  | eq a b =>
      change (BinOp.eval .eq _ _).toNat = Scalar.bool.toNat (Prim.eval (.eq a b) env)
      rw [BinOp.eval_eq_toNat hw]
      simp [BitVec.toNat_eq,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2, Prim.eval, Scalar.toNat]
  | lt a b =>
      change (BinOp.eval .ult _ _).toNat = Scalar.bool.toNat (Prim.eval (.lt a b) env)
      rw [BinOp.eval_ult_toNat hw,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2]
      simp [Prim.eval, Scalar.toNat]
  | le a b =>
      change (BinOp.eval .ule _ _).toNat = Scalar.bool.toNat (Prim.eval (.le a b) env)
      rw [BinOp.eval_ule_toNat hw,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2]
      simp [Prim.eval, Scalar.toNat]
  | length buffer =>
      exact atomFieldExpr_toNat layout buffer env regs mem matched fits
        ⟨1, by change 1 < 2; decide⟩
  | fst pair =>
      exact (atomFieldExpr_toNat layout pair env regs mem matched fits
        (scalar.index.castAdd _)).trans
          ((valueField_prod_left placement (pair.eval env) scalar.index).trans
            (scalar.valueField placement (pair.eval env).1 scalar.index))
  | snd pair =>
      exact (atomFieldExpr_toNat layout pair env regs mem matched fits
        (scalar.index.natAdd _)).trans
          ((valueField_prod_right placement (pair.eval env) scalar.index).trans
            (scalar.valueField placement (pair.eval env).2 scalar.index))
  | pair | none | some => cases scalar

/-- Scalar lowering requires no additional live source registers. -/
theorem primExpr_bounded (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (bounded : layout.Bounded dst) : (primExpr layout prim scalar).Bounded dst := by
  cases prim with
  | atom atom => exact atomExpr_bounded layout atom scalar bounded
  | add a b | mul a b | div a b | mod a b | eq a b | lt a b | le a b =>
      exact ⟨atomExpr_bounded layout a .nat bounded, atomExpr_bounded layout b .nat bounded⟩
  | sub a b =>
      exact ⟨⟨atomExpr_bounded layout a .nat bounded, atomExpr_bounded layout b .nat bounded⟩,
        ⟨atomExpr_bounded layout b .nat bounded, atomExpr_bounded layout a .nat bounded⟩⟩
  | length buffer =>
      exact atomFieldExpr_bounded layout buffer bounded ⟨1, by change 1 < 2; decide⟩
  | fst pair => exact atomFieldExpr_bounded layout pair bounded _
  | snd pair => exact atomFieldExpr_bounded layout pair bounded _
  | pair | none | some => cases scalar

/-- Atom materialization executes one emitted instruction, including variables. -/
@[simp] theorem atomExpr_compile_length (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (scalar : Scalar τ) (dst : Reg) : ((atomExpr layout atom scalar).compile dst).length = 1 := by
  cases atom with
  | var => rfl
  | nat => rfl
  | bool => rfl
  | unit => cases scalar

/-- These constants are consequences of the emitted expression code, not
user-supplied prices. Both operands are materialized before the binary operation. -/
theorem primExpr_compile_length (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (scalar : Scalar τ) (dst : Reg) :
    ((primExpr layout prim scalar).compile dst).length =
      match prim with
      | .atom _ | .length _ | .fst _ | .snd _ | .pair _ _ | .none _ | .some _ => 1
      | .add _ _ | .mul _ _ | .div _ _ | .mod _ _ | .eq _ _ | .lt _ _ | .le _ _ => 3
      | .sub _ _ => 7 := by
  cases prim <;> try cases scalar
  all_goals simp [primExpr, Expr.compile]

/-- Every primitive field denotes its ordinary mathematical component. -/
theorem primFieldExpr_toNat (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    (hw : 0 < w) {placement : Nat → Word w} (matched : layout.Matches placement env regs)
    (fits : PrimFits w env prim) (i : Fin (fieldCount τ)) :
    ((primFieldExpr layout prim i).eval regs mem).toNat =
      valueField placement (prim.eval env) i := by
  cases prim with
  | atom atom => exact atomFieldExpr_toNat layout atom env regs mem matched fits i
  | add a b | mul a b | sub a b | div a b | mod a b | length a =>
      exact primExpr_toNat layout _ .nat env regs mem hw matched fits
  | eq a b | lt a b | le a b =>
      exact primExpr_toNat layout _ .bool env regs mem hw matched fits
  | pair left right =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left, Prim.eval, valueField_prod_left] using
          atomFieldExpr_toNat layout left env regs mem matched fits.1 j
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right, Prim.eval, valueField_prod_right] using
          atomFieldExpr_toNat layout right env regs mem matched fits.2 j
  | fst pair =>
      exact (atomFieldExpr_toNat layout pair env regs mem matched fits (i.castAdd _)).trans
        (valueField_prod_left placement (pair.eval env) i)
  | snd pair =>
      exact (atomFieldExpr_toNat layout pair env regs mem matched fits (i.natAdd _)).trans
        (valueField_prod_right placement (pair.eval env) i)
  | none τ => exact Word.ofNat_toNat_of_lt (Nat.two_pow_pos w)
  | some value =>
      refine Fin.cases ?_ ?_ i
      · exact Word.ofNat_toNat_of_lt fits.1
      · intro j
        exact atomFieldExpr_toNat layout value env regs mem matched fits.2 j

/-- Field materialization preserves the same inferred scratch-register bound. -/
theorem primFieldExpr_bounded (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (bounded : layout.Bounded dst) (i : Fin (fieldCount τ)) :
    (primFieldExpr layout prim i).Bounded dst := by
  cases prim with
  | atom atom => exact atomFieldExpr_bounded layout atom bounded i
  | add a b => exact primExpr_bounded layout (.add a b) .nat bounded
  | mul a b => exact primExpr_bounded layout (.mul a b) .nat bounded
  | sub a b => exact primExpr_bounded layout (.sub a b) .nat bounded
  | div a b => exact primExpr_bounded layout (.div a b) .nat bounded
  | mod a b => exact primExpr_bounded layout (.mod a b) .nat bounded
  | length a => exact primExpr_bounded layout (.length a) .nat bounded
  | eq a b => exact primExpr_bounded layout (.eq a b) .bool bounded
  | lt a b => exact primExpr_bounded layout (.lt a b) .bool bounded
  | le a b => exact primExpr_bounded layout (.le a b) .bool bounded
  | pair left right =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left] using
          atomFieldExpr_bounded layout left bounded j
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right] using
          atomFieldExpr_bounded layout right bounded j
  | fst pair | snd pair => exact atomFieldExpr_bounded layout pair bounded _
  | none τ => trivial
  | some value =>
      refine Fin.cases True.intro ?_ i
      intro j
      exact atomFieldExpr_bounded layout value bounded j

/-- Field materialization costs come from the existing expression compiler.
Structured construction and projection each materialize one instruction per field. -/
theorem primFieldExpr_compile_length (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (i : Fin (fieldCount τ)) (dst : Reg) :
    ((primFieldExpr layout prim i).compile dst).length =
      match prim with
      | .add .. | .mul .. | .div .. | .mod .. | .eq .. | .lt .. | .le .. => 3
      | .sub .. => 7
      | _ => 1 := by
  cases prim with
  | atom atom => exact atomFieldExpr_compile_length layout atom i dst
  | add a b => exact primExpr_compile_length layout (.add a b) .nat dst
  | mul a b => exact primExpr_compile_length layout (.mul a b) .nat dst
  | sub a b => exact primExpr_compile_length layout (.sub a b) .nat dst
  | div a b => exact primExpr_compile_length layout (.div a b) .nat dst
  | mod a b => exact primExpr_compile_length layout (.mod a b) .nat dst
  | length a => exact primExpr_compile_length layout (.length a) .nat dst
  | eq a b => exact primExpr_compile_length layout (.eq a b) .bool dst
  | lt a b => exact primExpr_compile_length layout (.lt a b) .bool dst
  | le a b => exact primExpr_compile_length layout (.le a b) .bool dst
  | pair left right =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left] using
          atomFieldExpr_compile_length layout left j dst
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right] using
          atomFieldExpr_compile_length layout right j dst
  | fst pair | snd pair => exact atomFieldExpr_compile_length layout pair _ dst
  | none τ => rfl
  | some value =>
      refine Fin.cases rfl ?_ i
      intro j
      exact atomFieldExpr_compile_length layout value j dst

/-- A high-level scalar operation refines an actual, counted RAM execution.
The existing `Expr.Compiled` conclusion preserves live slots, heap, I/O and
status. This is the scalar fragment, not yet a whole-function lowering theorem. -/
theorem prim_refines (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (s : State w) (hw : 0 < w)
    {placement : Nat → Word w} (matched : layout.Matches placement env s.regs)
    (fits : PrimFits w env prim)
    (bounded : layout.Bounded dst)
    (placed : CodeAt code s.pc ((primExpr layout prim scalar).compile dst))
    (running : s.status = .running) :
    ∃ t, Exec code ((primExpr layout prim scalar).compile dst).length s t ∧
      (t.regs dst).toNat = scalar.toNat (prim.eval env) ∧
      Expr.Compiled (primExpr layout prim scalar) dst s t ∧
      t.pc = s.pc + ((primExpr layout prim scalar).compile dst).length := by
  obtain ⟨t, execution, compiled, pc⟩ :=
    Expr.compile_refines (primExpr_bounded layout prim scalar bounded) placed running
  refine ⟨t, execution, ?_, compiled, pc⟩
  rw [compiled.value]
  exact primExpr_toNat layout prim scalar env s.regs s.mem hw matched fits

end Ram.LanguageCompiler
