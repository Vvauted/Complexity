/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Scalar
import Complexity.Computability.Ram.Source.Function.Basic

/-!
# Scalar layouts and parameter representation

The backend represents natural numbers and booleans by one word and Unit by no
words. Parameter layouts follow lexical parameter order without reserving dummy
slots for Unit. The same field lists serve argument encoding and real call
receivers. Exact representation requires the source values to fit the chosen
word width; the encoding alone makes no non-wrapping arithmetic claim.

The register correspondence composes through fresh lexical bindings and caller
restoration. Restoration preserves caller locals while retaining the callee's
actual shared effects; it does not assume that memory or I/O stayed unchanged.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The number of actual words used by a source value. -/
@[simp] def fieldCount : Ty → Nat
  | .nat | .bool => 1
  | .unit => 0

/-- The size of the compact parameter frame. -/
@[simp] def contextSize : List Ty → Nat
  | [] => 0
  | τ :: Γ => fieldCount τ + contextSize Γ

/-- A represented scalar occupies an actual word. -/
theorem fieldCount_pos (scalar : Scalar τ) : 0 < fieldCount τ := by
  cases scalar <;> decide

/-- Destinations for one source value; a Unit receiver performs no assignment. -/
@[simp] def valueRegs (τ : Ty) (dst : Reg) : List Reg :=
  match τ with
  | .nat | .bool => [dst]
  | .unit => []

@[simp] theorem valueRegs_length (τ : Ty) (dst : Reg) :
    (valueRegs τ dst).length = fieldCount τ := by
  cases τ <;> rfl

/-- Encode the actual fields of a value, without fabricating a Unit word. -/
@[simp] def valueWords (w : Nat) : {τ : Ty} → Value τ → List (Word w)
  | .nat, value => [BitVec.ofNat w value]
  | .bool, value => [BitVec.ofNat w (if value then 1 else 0)]
  | .unit, _ => []

@[simp] theorem valueWords_length (w : Nat) {τ : Ty} (value : Value τ) :
    (valueWords w value).length = fieldCount τ := by
  cases τ <;> rfl

/-- Encode the parameter environment in its declared order. -/
def envWords (w : Nat) : {Γ : List Ty} → Env Γ → List (Word w)
  | [], _ => []
  | _ :: _, env => valueWords w env.head ++ envWords w env.tail

@[simp] theorem envWords_nil (w : Nat) (env : Env []) : envWords w env = [] := rfl

@[simp] theorem envWords_cons (w : Nat) {τ : Ty} (value : Value τ) (env : Env Γ) :
    envWords w (Env.cons value env) = valueWords w value ++ envWords w env := rfl

@[simp] theorem envWords_length (w : Nat) (env : Env Γ) :
    (envWords w env).length = contextSize Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simp only [envWords, List.length_append, valueWords_length, ih, contextSize]

/-- Every represented lexical scalar is in range. Unit has no range obligation. -/
def EnvFits (w : Nat) (env : Env Γ) : Prop :=
  ∀ {τ} (_scalar : Scalar τ) (v : Var Γ τ), valueToNat (env.get v) < 2 ^ w

namespace EnvFits

/-- An empty parameter environment has no scalar range obligations. -/
@[simp] theorem empty (w : Nat) : EnvFits w Env.empty := by
  intro τ scalar v
  cases v

/-- Extend the source range facts by an actual newly computed value. -/
theorem cons {env : Env Γ} (fits : EnvFits w env) (value : Value τ)
    (fitsValue : ∀ _scalar : Scalar τ, valueToNat value < 2 ^ w) :
    EnvFits w (Env.cons value env) := by
  intro σ scalar v
  cases v with
  | here => exact fitsValue scalar
  | there v => exact fits scalar v

/-- Leaving a lexical scope retains all outer range facts. -/
theorem tail {env : Env (τ :: Γ)} (fits : EnvFits w env) : EnvFits w env.tail :=
  fun scalar v => fits scalar (.there v)

/-- Parameter ranges decompose into the actual head value and outer environment. -/
@[simp] theorem cons_iff (value : Value τ) (env : Env Γ) :
    EnvFits w (Env.cons value env) ↔
      (∀ _scalar : Scalar τ, valueToNat value < 2 ^ w) ∧ EnvFits w env := by
  constructor
  · intro fits
    exact ⟨fun scalar => fits scalar .here, fits.tail⟩
  · rintro ⟨fitsValue, fits⟩
    exact fits.cons value fitsValue

/-- A natural parameter contributes its ordinary unsigned range condition. -/
@[simp] theorem cons_nat_iff (value : Nat) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .nat) value env) ↔ value < 2 ^ w ∧ EnvFits w env := by
  rw [cons_iff]
  constructor
  · intro fits
    exact ⟨fits.1 .nat, fits.2⟩
  · intro fits
    exact ⟨fun _ => fits.1, fits.2⟩

/-- A Boolean parameter contributes the range of its actual zero-or-one encoding. -/
@[simp] theorem cons_bool_iff (value : Bool) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .bool) value env) ↔
      (if value then 1 else 0) < 2 ^ w ∧ EnvFits w env := by
  rw [cons_iff]
  constructor
  · intro fits
    exact ⟨fits.1 .bool, fits.2⟩
  · intro fits
    exact ⟨fun _ => fits.1, fits.2⟩

/-- A Unit parameter occupies no word and adds no range condition. -/
@[simp] theorem cons_unit_iff (value : Unit) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .unit) value env) ↔ EnvFits w env := by
  rw [cons_iff]
  constructor
  · exact fun fits => fits.2
  · intro fits
    exact ⟨(fun scalar => nomatch scalar), fits⟩

end EnvFits

namespace RegisterMap

/-- Bind a fresh source variable. Unit cannot be queried through a scalar map. -/
def extend (layout : RegisterMap Γ) (τ : Ty) (dst : Reg) : RegisterMap (τ :: Γ) :=
  fun scalar v => match v with
    | .here => dst
    | .there v => layout scalar v

@[simp] theorem extend_here (layout : RegisterMap Γ) (scalar : Scalar τ) (dst : Reg) :
    RegisterMap.extend layout τ dst scalar .here = dst := rfl

@[simp] theorem extend_there (layout : RegisterMap Γ) (τ : Ty) (dst : Reg)
    (scalar : Scalar σ) (v : Var Γ σ) :
    RegisterMap.extend layout τ dst scalar (.there v) = layout scalar v := rfl

/-- Fresh allocation uses precisely the new value's number of fields. -/
theorem extend_bounded {layout : RegisterMap Γ} (bounded : layout.Bounded next) :
    RegisterMap.Bounded (RegisterMap.extend layout τ next) (next + fieldCount τ) := by
  intro σ scalar v
  cases v with
  | here =>
      exact Nat.lt_add_of_pos_right (fieldCount_pos scalar)
  | there v =>
      exact Nat.lt_of_lt_of_le (bounded scalar v) (Nat.le_add_right _ _)

end RegisterMap

/-- Assign parameter slots in declared order, omitting Unit fields. -/
def parameterMap : (Γ : List Ty) → (base : Reg := 0) → RegisterMap Γ
  | [], _ => fun _ v => nomatch v
  | τ :: Γ, base => RegisterMap.extend (parameterMap Γ (base + fieldCount τ)) τ base

@[simp] theorem parameterMap_here (scalar : Scalar τ) (base : Reg) :
    parameterMap (τ :: Γ) base scalar .here = base := rfl

@[simp] theorem parameterMap_there (τ : Ty) (base : Reg) (scalar : Scalar σ)
    (v : Var Γ σ) :
    parameterMap (τ :: Γ) base scalar (.there v) =
      parameterMap Γ (base + fieldCount τ) scalar v := rfl

/-- Relocating a compact parameter frame translates every represented slot. -/
theorem parameterMap_add (Γ : List Ty) (base : Reg) (scalar : Scalar τ)
    (v : Var Γ τ) :
    parameterMap Γ base scalar v = base + parameterMap Γ 0 scalar v := by
  induction v generalizing base with
  | here => simp only [parameterMap_here, Nat.add_zero]
  | @there Γ τ σ v ih =>
      simp only [parameterMap_there, Nat.zero_add]
      rw [ih (base + fieldCount σ) scalar, ih (fieldCount σ) scalar]
      exact Nat.add_assoc _ _ _

/-- Compact parameter slots fit their exact frame extent. -/
theorem parameterMap_bounded (Γ : List Ty) (base : Reg := 0) :
    RegisterMap.Bounded (parameterMap Γ base) (base + contextSize Γ) := by
  induction Γ generalizing base with
  | nil => intro τ scalar v; cases v
  | cons τ Γ ih =>
      intro σ scalar v
      cases v with
      | here =>
          change base < base + (fieldCount τ + contextSize Γ)
          exact Nat.lt_add_of_pos_right
            (Nat.lt_of_lt_of_le (fieldCount_pos scalar) (Nat.le_add_right _ _))
      | there v =>
          simpa only [parameterMap_there, contextSize, Nat.add_assoc] using
            ih (base + fieldCount τ) scalar v

/-- Each scalar parameter has an actual field at its compact slot. The optional
lookup returns `some`, so the frame's out-of-range default is never used here. -/
theorem envWords_getElem? (w : Nat) (env : Env Γ) (scalar : Scalar τ) (v : Var Γ τ) :
    (envWords w env)[parameterMap Γ 0 scalar v]? =
      some (BitVec.ofNat w (valueToNat (env.get v))) := by
  induction v with
  | here =>
      cases scalar <;>
        simp only [envWords, parameterMap_here, valueWords, valueToNat,
          List.singleton_append, List.getElem?_cons_zero, Env.head]
  | @there Γ τ σ v ih =>
      simp only [envWords, parameterMap_there, Nat.zero_add]
      rw [parameterMap_add Γ (fieldCount σ) scalar v]
      cases σ <;>
        simp only [fieldCount, valueWords, List.singleton_append, List.nil_append,
          Nat.zero_add, Nat.add_comm 1, List.getElem?_cons_succ]
      all_goals exact ih env.tail scalar

/-- Entering an actual argument list establishes exact source-variable
representation when its source values are in range. -/
theorem parameterMap_matches_enter (entry : Source.State w) (env : Env Γ)
    (fits : EnvFits w env) :
    RegisterMap.Matches (parameterMap Γ) env (entry.enter (envWords w env)).regs := by
  intro τ scalar v
  rw [Source.State.enter_regs, envWords_getElem?, Option.getD_some]
  exact Word.ofNat_toNat_of_lt (fits scalar v)

namespace RegisterMap.Matches

/-- Leaving a lexical scope restricts the correspondence to its outer bindings. -/
theorem tail {layout : RegisterMap Γ} {finish : Env (τ :: Γ)} {regs : Reg → Word w}
    (matched : RegisterMap.Matches (RegisterMap.extend layout τ dst) finish regs) :
    layout.Matches finish.tail regs := fun scalar v => matched scalar (.there v)

/-- A represented value and preservation of outer slots establish the lexical
correspondence after a binding, independently of the chosen state update. -/
theorem extend {layout : RegisterMap Γ} {env : Env Γ} {regs regs' : Reg → Word w}
    {value : Value τ} (matched : layout.Matches env regs)
    (preserved : ∀ {σ} (scalar : Scalar σ) (v : Var Γ σ),
      regs' (layout scalar v) = regs (layout scalar v))
    (represented : ∀ _scalar : Scalar τ, (regs' dst).toNat = valueToNat value) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) (Env.cons value env) regs' := by
  intro σ scalar v
  cases v with
  | here => exact represented scalar
  | there v =>
      change (regs' (layout scalar v)).toNat = valueToNat (env.get v)
      rw [preserved scalar v]
      exact matched scalar v

/-- Fresh receiver assignment installs exactly the encoded fields. Unit adds a
lexical binding but performs no register write. -/
theorem setRegs {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    (matched : layout.Matches env entry.regs) (bounded : layout.Bounded dst)
    (value : Value τ) (fits : ∀ _scalar : Scalar τ, valueToNat value < 2 ^ w) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) (Env.cons value env)
      (entry.setRegs (valueRegs τ dst) (valueWords w value)).regs := by
  apply matched.extend
  · intro σ scalar v
    apply Source.State.setRegs_ne
    have fresh := Nat.ne_of_lt (bounded scalar v)
    cases τ with
    | nat | bool => simpa only [valueRegs, List.mem_singleton] using fresh
    | unit => simp only [valueRegs, List.not_mem_nil, not_false_eq_true]
  · intro scalar
    cases scalar with
    | nat =>
        simpa only [valueRegs, valueWords, Source.State.setRegs_singleton,
          Source.State.setReg_same, valueToNat] using Word.ofNat_toNat_of_lt (fits .nat)
    | bool =>
        simpa only [valueRegs, valueWords, Source.State.setRegs_singleton,
          Source.State.setReg_same, valueToNat] using Word.ofNat_toNat_of_lt (fits .bool)

/-- Caller restoration retains the lexical environment while preserving the
callee's actual shared state. No heap or I/O frame premise is needed. -/
theorem restore {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    (matched : layout.Matches env entry.regs) (callee : Source.State w) :
    layout.Matches env (entry.restore callee).regs := matched

end RegisterMap.Matches

end Ram.LanguageCompiler
