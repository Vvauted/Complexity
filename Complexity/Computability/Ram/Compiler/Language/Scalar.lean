/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Computability.Ram.Compiler.Expr.Basic

/-!
# Compiling high-level scalar operations

The high-level values and operations have their own mathematical meaning. This
module lowers their Nat/Bool fragment to existing RAM expressions and reuses the
verified expression compiler. Range conditions concern the actual operands and
intermediate result, not only a function's eventual output.

The register map belongs to the backend. Unit bindings require no scalar slot
and are not accepted as one-word operands. The final theorem supplies actual
machine execution, its emitted-code length, the mathematical result and the
existing frame guarantee; no source cost table is assumed.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Source types represented by one word in this fragment. -/
inductive Scalar : Ty → Prop where
  | nat : Scalar .nat
  | bool : Scalar .bool

/-- The mathematical unsigned observation used by the scalar representation.
The Unit case is only a total definition of the observation, not a word encoding. -/
def valueToNat : {τ : Ty} → Value τ → Nat
  | .nat, n => n
  | .bool, b => if b then 1 else 0
  | .unit, _ => 0

/-- A backend assignment for scalar lexical bindings; Unit has no entry. -/
abbrev RegisterMap (Γ : List Ty) := ∀ {τ}, Scalar τ → Var Γ τ → Reg

namespace RegisterMap

/-- Every represented source scalar has its exact mathematical value. -/
def Matches (layout : RegisterMap Γ) (env : Env Γ) (regs : Reg → Word w) : Prop :=
  ∀ {τ} (scalar : Scalar τ) (v : Var Γ τ),
    (regs (layout scalar v)).toNat = valueToNat (env.get v)

/-- Source slots lie below the expression compiler's scratch register. -/
def Bounded (layout : RegisterMap Γ) (bound : Reg) : Prop :=
  ∀ {τ} (scalar : Scalar τ) (v : Var Γ τ), layout scalar v < bound

end RegisterMap

/-- Lower an atom without adding computations to its source meaning. -/
def atomExpr (layout : RegisterMap Γ) : {τ : Ty} → Atom Γ τ → Scalar τ → Expr
  | _, .var v, scalar => .var (layout scalar v)
  | _, .nat n, _ => .const n
  | _, .bool b, _ => .const (if b then 1 else 0)
  | _, .unit, impossible => nomatch impossible

/-- An in-range atom is decoded exactly after lowering. -/
theorem atomExpr_toNat (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    (hw : 0 < w) (matched : layout.Matches env regs)
    (fits : valueToNat (atom.eval env) < 2 ^ w) :
    ((atomExpr layout atom scalar).eval regs mem).toNat = valueToNat (atom.eval env) := by
  cases atom with
  | var v => exact matched scalar v
  | nat n => exact Word.ofNat_toNat_of_lt fits
  | bool b =>
      cases b <;> simp [atomExpr, Expr.eval, Atom.eval, valueToNat, BitVec.toNat_one hw]
  | unit => cases scalar

/-- Atom lowering respects the backend's inferred register bound. -/
theorem atomExpr_bounded (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (bounded : layout.Bounded dst) : (atomExpr layout atom scalar).Bounded dst := by
  cases atom with
  | var v => exact bounded scalar v
  | nat => trivial
  | bool => trivial
  | unit => cases scalar

/-- Scalar operations reuse the fixed word instruction vocabulary. -/
def primExpr (layout : RegisterMap Γ) : {τ : Ty} → Prim Γ τ → Scalar τ → Expr
  | _, .atom a, scalar => atomExpr layout a scalar
  | _, .add a b, _ => .bin .add (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .lt a b, _ => .bin .ult (atomExpr layout a .nat) (atomExpr layout b .nat)
  | _, .le a b, _ => .bin .ule (atomExpr layout a .nat) (atomExpr layout b .nat)

/-- Source-level sufficient ranges for an operation. Addition includes its
actual intermediate sum, even if later code returns a smaller value. -/
def PrimFits (w : Nat) (env : Env Γ) : {τ : Ty} → Prim Γ τ → Prop
  | _, .atom a => valueToNat (a.eval env) < 2 ^ w
  | _, .add a b =>
      a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w ∧ a.eval env + b.eval env < 2 ^ w
  | _, .lt a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w
  | _, .le a b => a.eval env < 2 ^ w ∧ b.eval env < 2 ^ w

/-- The fixed lowering implements mathematical Nat/Bool semantics, not merely
equality modulo the word width. -/
theorem primExpr_toNat (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (regs : Reg → Word w) (mem : Word w → Word w)
    (hw : 0 < w) (matched : layout.Matches env regs) (fits : PrimFits w env prim) :
    ((primExpr layout prim scalar).eval regs mem).toNat = valueToNat (prim.eval env) := by
  cases prim with
  | atom atom => exact atomExpr_toNat layout atom scalar env regs mem hw matched fits
  | add a b =>
      change (BinOp.eval .add _ _).toNat = a.eval env + b.eval env
      rw [BinOp.eval_add_toNat,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2.1]
      exact Nat.mod_eq_of_lt fits.2.2
  | lt a b =>
      change (BinOp.eval .ult _ _).toNat = valueToNat (Prim.eval (.lt a b) env)
      rw [BinOp.eval_ult_toNat hw,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2]
      simp [Prim.eval, valueToNat]
  | le a b =>
      change (BinOp.eval .ule _ _).toNat = valueToNat (Prim.eval (.le a b) env)
      rw [BinOp.eval_ule_toNat hw,
        atomExpr_toNat layout a .nat env regs mem hw matched fits.1,
        atomExpr_toNat layout b .nat env regs mem hw matched fits.2]
      simp [Prim.eval, valueToNat]

/-- Scalar lowering requires no additional live source registers. -/
theorem primExpr_bounded (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (bounded : layout.Bounded dst) : (primExpr layout prim scalar).Bounded dst := by
  cases prim with
  | atom atom => exact atomExpr_bounded layout atom scalar bounded
  | add a b | lt a b | le a b =>
      exact ⟨atomExpr_bounded layout a .nat bounded, atomExpr_bounded layout b .nat bounded⟩

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
      | .atom _ => 1
      | .add _ _ | .lt _ _ | .le _ _ => 3 := by
  cases prim <;> simp [primExpr, Expr.compile]

/-- A high-level scalar operation refines an actual, counted RAM execution.
The existing `Expr.Compiled` conclusion preserves live slots, heap, I/O and
status. This is the scalar fragment, not yet a whole-function lowering theorem. -/
theorem prim_refines (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (s : State w) (hw : 0 < w)
    (matched : layout.Matches env s.regs) (fits : PrimFits w env prim)
    (bounded : layout.Bounded dst)
    (placed : CodeAt code s.pc ((primExpr layout prim scalar).compile dst))
    (running : s.status = .running) :
    ∃ t, Exec code ((primExpr layout prim scalar).compile dst).length s t ∧
      (t.regs dst).toNat = valueToNat (prim.eval env) ∧
      Expr.Compiled (primExpr layout prim scalar) dst s t ∧
      t.pc = s.pc + ((primExpr layout prim scalar).compile dst).length := by
  obtain ⟨t, execution, compiled, pc⟩ :=
    Expr.compile_refines (primExpr_bounded layout prim scalar bounded) placed running
  refine ⟨t, execution, ?_, compiled, pc⟩
  rw [compiled.value]
  exact primExpr_toNat layout prim scalar env s.regs s.mem hw matched fits

end Ram.LanguageCompiler
