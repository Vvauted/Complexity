/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Scalar
import Complexity.Computability.Ram.Source.Function.Basic
import Init.Data.List.Nat.Range

/-!
# Field layouts and parameter representation

The backend represents natural numbers and booleans by one word, borrowed
buffers by address and length, and Unit by no words. Parameter layouts follow
lexical parameter order without reserving dummy slots for Unit. The same field
lists serve argument encoding and real call
receivers. Exact representation requires the source values to fit the chosen
word width; the encoding alone makes no non-wrapping arithmetic claim.

The register correspondence composes through fresh lexical bindings and caller
restoration. Restoration preserves caller locals while retaining the callee's
actual shared effects; it does not assume that memory or I/O stayed unchanged.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The size of the compact parameter frame. -/
@[simp] def contextSize : List Ty → Nat
  | [] => 0
  | τ :: Γ => fieldCount τ + contextSize Γ

/-- Destinations for one source value; a Unit receiver performs no assignment. -/
def valueRegs (τ : Ty) (dst : Reg) : List Reg := List.range' dst (fieldCount τ)

@[simp] theorem valueRegs_length (τ : Ty) (dst : Reg) :
    (valueRegs τ dst).length = fieldCount τ := List.length_range'

/-- The generated receiver occupies precisely its contiguous field interval. -/
@[simp] theorem mem_valueRegs {τ : Ty} {dst r : Reg} :
    r ∈ valueRegs τ dst ↔ dst ≤ r ∧ r < dst + fieldCount τ := List.mem_range'_1

@[simp] theorem valueRegs_getElem (τ : Ty) (dst : Reg) (i : Fin (fieldCount τ)) :
    (valueRegs τ dst)[i.val]'(by simp) = dst + i.val := by
  simp only [valueRegs, List.getElem_range', Nat.one_mul]

/-- Distinctness belongs to this generated receiver, not to general assignment. -/
theorem valueRegs_nodup (τ : Ty) (dst : Reg) : (valueRegs τ dst).Nodup := List.nodup_range'

@[simp] theorem valueRegs_nat (dst : Reg) : valueRegs .nat dst = [dst] := rfl

@[simp] theorem valueRegs_bool (dst : Reg) : valueRegs .bool dst = [dst] := rfl

@[simp] theorem valueRegs_unit (dst : Reg) : valueRegs .unit dst = [] := rfl

@[simp] theorem valueRegs_buffer (kind : CellTy) (dst : Reg) :
    valueRegs (.buffer kind) dst = [dst, dst + 1] := rfl

/-- Encode the parameter environment in its declared order. -/
def envWords (placement : Nat → Word w) : {Γ : List Ty} → Env Γ → List (Word w)
  | [], _ => []
  | _ :: _, env => valueWords placement env.head ++ envWords placement env.tail

@[simp] theorem envWords_nil (placement : Nat → Word w) (env : Env []) :
    envWords placement env = [] := rfl

@[simp] theorem envWords_cons (placement : Nat → Word w) {τ : Ty}
    (value : Value τ) (env : Env Γ) :
    envWords placement (Env.cons value env) =
      valueWords placement value ++ envWords placement env := rfl

@[simp] theorem envWords_length (placement : Nat → Word w) (env : Env Γ) :
    (envWords placement env).length = contextSize Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simp only [envWords, List.length_append, valueWords_length, ih, contextSize]

/-- Source value ranges do not depend on physical object placement. -/
def EnvFits (w : Nat) (env : Env Γ) : Prop :=
  ∀ {τ} (v : Var Γ τ), ValueFits w (env.get v)

namespace EnvFits

/-- An empty parameter environment has no field range obligations. -/
@[simp] theorem empty (w : Nat) : EnvFits w Env.empty := by
  intro τ v
  cases v

/-- Any placement represents the actual fields within the selected word width. -/
theorem fields {env : Env Γ} (fits : EnvFits w env) (placement : Nat → Word w)
    (v : Var Γ τ) (i : Fin (fieldCount τ)) :
    valueField placement (env.get v) i < 2 ^ w := (fits v).fields placement i

/-- Scalar arithmetic uses the one-field consequence of the common range facts. -/
theorem scalar {env : Env Γ} (fits : EnvFits w env) (scalar : Scalar τ) (v : Var Γ τ) :
    scalar.toNat (env.get v) < 2 ^ w := (scalar.fits_iff (env.get v)).mp (fits v)

/-- Extend the source range facts by an actual newly computed value. -/
theorem cons {env : Env Γ} (fits : EnvFits w env) (value : Value τ)
    (fitsValue : ValueFits w value) :
    EnvFits w (Env.cons value env) := by
  intro σ v
  cases v with
  | here => exact fitsValue
  | there v => exact fits v

/-- Leaving a lexical scope retains all outer range facts. -/
theorem tail {env : Env (τ :: Γ)} (fits : EnvFits w env) : EnvFits w env.tail :=
  fun v => fits (.there v)

/-- Parameter ranges decompose into the actual head value and outer environment. -/
@[simp] theorem cons_iff (value : Value τ) (env : Env Γ) :
    EnvFits w (Env.cons value env) ↔
      ValueFits w value ∧ EnvFits w env := by
  constructor
  · intro fits
    exact ⟨fits .here, fits.tail⟩
  · rintro ⟨fitsValue, fits⟩
    exact fits.cons value fitsValue

/-- A natural parameter contributes its ordinary unsigned range condition. -/
@[simp] theorem cons_nat_iff (value : Nat) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .nat) value env) ↔ value < 2 ^ w ∧ EnvFits w env := by
  rw [cons_iff, Scalar.fits_iff .nat value]
  rfl

/-- A Boolean parameter contributes the range of its actual zero-or-one encoding. -/
@[simp] theorem cons_bool_iff (value : Bool) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .bool) value env) ↔
      (if value then 1 else 0) < 2 ^ w ∧ EnvFits w env := by
  rw [cons_iff, Scalar.fits_iff .bool value]
  rfl

/-- A Unit parameter occupies no word and adds no range condition. -/
@[simp] theorem cons_unit_iff (value : Unit) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .unit) value env) ↔ EnvFits w env := by
  rw [cons_iff]
  constructor
  · exact fun fits => fits.2
  · intro fits
    exact ⟨True.intro, fits⟩

/-- A buffer contributes its length range, independently of its placed address. -/
@[simp] theorem cons_buffer_iff (value : Buffer kind) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .buffer kind) value env) ↔
      value.length < 2 ^ w ∧ EnvFits w env := by
  rw [cons_iff]
  rfl

end EnvFits

namespace RegisterMap

/-- Every live source field lies outside a contiguous destination interval. -/
def AvoidsRange (layout : RegisterMap Γ) (dst count : Reg) : Prop :=
  ∀ {τ} (v : Var Γ τ) (i : Fin (fieldCount τ)),
    layout v i < dst ∨ dst + count ≤ layout v i

/-- A fresh interval lies after all currently represented fields. -/
theorem Bounded.avoidsRange {layout : RegisterMap Γ} (bounded : layout.Bounded dst)
    (count : Nat) : layout.AvoidsRange dst count := fun v i => Or.inl (bounded v i)

/-- Separation concerns the actual fields in the generated destination list. -/
theorem AvoidsRange.not_mem {layout : RegisterMap Γ}
    (separate : layout.AvoidsRange dst count) (v : Var Γ τ) (i : Fin (fieldCount τ)) :
    layout v i ∉ List.range' dst count := by
  intro member
  have interval := List.mem_range'_1.mp member
  rcases separate v i with before | after
  · exact Nat.not_le_of_gt before interval.1
  · exact Nat.not_le_of_gt interval.2 after

/-- Bind a fresh variable to all its actual consecutive fields. -/
def extend (layout : RegisterMap Γ) (τ : Ty) (dst : Reg) : RegisterMap (τ :: Γ) :=
  fun v i => match v with
    | .here => dst + i.val
    | .there v => layout v i

@[simp] theorem extend_here (layout : RegisterMap Γ) (dst : Reg)
    (i : Fin (fieldCount τ)) : RegisterMap.extend layout τ dst .here i = dst + i.val := rfl

@[simp] theorem extend_there (layout : RegisterMap Γ) (τ : Ty) (dst : Reg)
    (v : Var Γ σ) (i : Fin (fieldCount σ)) :
    RegisterMap.extend layout τ dst (.there v) i = layout v i := rfl

/-- Fresh allocation uses precisely the new value's number of fields. -/
theorem extend_bounded {layout : RegisterMap Γ} (bounded : layout.Bounded next) :
    RegisterMap.Bounded (RegisterMap.extend layout τ next) (next + fieldCount τ) := by
  intro σ v i
  cases v with
  | here => exact Nat.add_lt_add_left i.isLt next
  | there v =>
      exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_add_right _ _)

/-- Fresh fields beyond a protected interval retain its separation. -/
theorem AvoidsRange.extend {layout : RegisterMap Γ}
    (separate : layout.AvoidsRange dst count) (fresh : dst + count ≤ next) :
    AvoidsRange (RegisterMap.extend layout τ next) dst count := by
  intro σ v i
  cases v with
  | here => exact Or.inr (Nat.le_trans fresh (Nat.le_add_right _ _))
  | there v => exact separate v i

end RegisterMap

/-- Assign parameter slots in declared order, omitting Unit fields. -/
def parameterMap : (Γ : List Ty) → (base : Reg := 0) → RegisterMap Γ
  | [], _ => fun v _ => nomatch v
  | τ :: Γ, base => RegisterMap.extend (parameterMap Γ (base + fieldCount τ)) τ base

@[simp] theorem parameterMap_here (base : Reg) (i : Fin (fieldCount τ)) :
    parameterMap (τ :: Γ) base .here i = base + i.val := rfl

@[simp] theorem parameterMap_there (τ : Ty) (base : Reg)
    (v : Var Γ σ) (i : Fin (fieldCount σ)) :
    parameterMap (τ :: Γ) base (.there v) i =
      parameterMap Γ (base + fieldCount τ) v i := rfl

/-- Relocating a compact parameter frame translates every represented slot. -/
theorem parameterMap_add (Γ : List Ty) (base : Reg)
    (v : Var Γ τ) (i : Fin (fieldCount τ)) :
    parameterMap Γ base v i = base + parameterMap Γ 0 v i := by
  induction v generalizing base with
  | here => simp only [parameterMap_here, Nat.zero_add]
  | @there Γ τ σ v ih =>
      simp only [parameterMap_there, Nat.zero_add]
      rw [ih (base + fieldCount σ) i, ih (fieldCount σ) i]
      exact Nat.add_assoc _ _ _

/-- Compact parameter slots fit their exact frame extent. -/
theorem parameterMap_bounded (Γ : List Ty) (base : Reg := 0) :
    RegisterMap.Bounded (parameterMap Γ base) (base + contextSize Γ) := by
  induction Γ generalizing base with
  | nil => intro τ v i; cases v
  | cons τ Γ ih =>
      intro σ v i
      cases v with
      | here =>
          change base + i.val < base + (fieldCount τ + contextSize Γ)
          exact Nat.add_lt_add_left
            (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)) base
      | there v =>
          simpa only [parameterMap_there, contextSize, Nat.add_assoc] using
            ih (base + fieldCount τ) v i

/-- Each parameter field has an actual entry at its compact slot. The optional
lookup returns `some`, so the frame's out-of-range default is never used here. -/
theorem envWords_getElem? (placement : Nat → Word w) (env : Env Γ) (v : Var Γ τ)
    (i : Fin (fieldCount τ)) :
    (envWords placement env)[parameterMap Γ 0 v i]? =
      some (BitVec.ofNat w (valueField placement (env.get v) i)) := by
  induction v with
  | here =>
      rw [envWords, parameterMap_here, Nat.zero_add,
        List.getElem?_append_left (by simp)]
      exact valueWords_getElem? placement env.head i
  | @there Γ τ σ v ih =>
      simp only [envWords, parameterMap_there, Nat.zero_add]
      rw [parameterMap_add Γ (fieldCount σ) v i,
        List.getElem?_append_right (by simp only [valueWords_length]; omega),
        valueWords_length, Nat.add_sub_cancel_left]
      exact ih env.tail i

/-- Entering an actual argument list establishes exact source-variable
representation when its source values are in range. -/
theorem parameterMap_matches_enter (entry : Source.State w) (placement : Nat → Word w) (env : Env Γ)
    (fits : EnvFits w env) :
    RegisterMap.Matches (parameterMap Γ) placement env
      (entry.enter (envWords placement env)).regs := by
  intro τ v i
  rw [Source.State.enter_regs, envWords_getElem?, Option.getD_some]
  exact Word.ofNat_toNat_of_lt (fits.fields placement v i)

namespace RegisterMap.Matches

/-- Leaving a lexical scope restricts the correspondence to its outer bindings. -/
theorem tail {layout : RegisterMap Γ} {finish : Env (τ :: Γ)} {regs : Reg → Word w}
    {placement : Nat → Word w}
    (matched : RegisterMap.Matches (RegisterMap.extend layout τ dst) placement finish regs) :
    layout.Matches placement finish.tail regs := fun v i => matched (.there v) i

/-- A represented value and preservation of outer slots establish the lexical
correspondence after a binding, independently of the chosen state update. -/
theorem extend {layout : RegisterMap Γ} {env : Env Γ} {regs regs' : Reg → Word w}
    {placement : Nat → Word w} {value : Value τ} (matched : layout.Matches placement env regs)
    (preserved : ∀ {σ} (v : Var Γ σ) (i : Fin (fieldCount σ)),
      regs' (layout v i) = regs (layout v i))
    (represented : ∀ i : Fin (fieldCount τ),
      (regs' (dst + i.val)).toNat = valueField placement value i) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) placement (Env.cons value env) regs' := by
  intro σ v i
  cases v with
  | here => exact represented i
  | there v =>
      change (regs' (layout v i)).toNat = valueField placement (env.get v) i
      rw [preserved v i]
      exact matched v i

/-- Fresh receiver assignment installs exactly the encoded fields. Unit adds a
lexical binding but performs no register write. -/
theorem setRegs {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    {placement : Nat → Word w} (matched : layout.Matches placement env entry.regs)
    (bounded : layout.Bounded dst) (value : Value τ) (fits : ValueFits w value) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) placement (Env.cons value env)
      (entry.setRegs (valueRegs τ dst) (valueWords placement value)).regs := by
  apply matched.extend
  · intro σ v i
    exact Source.State.setRegs_ne entry (valueRegs τ dst) (valueWords placement value) (layout v i)
      (fun member => Nat.not_le_of_gt (bounded v i) (mem_valueRegs.mp member).1)
  · intro i
    have assigned :
        (entry.setRegs (valueRegs τ dst) (valueWords placement value)).regs (dst + i.val) =
          BitVec.ofNat w (valueField placement value i) := by
      simpa only [valueRegs_getElem, valueWords_getElem] using
        Source.State.setRegs_getElem entry (valueRegs τ dst) (valueWords placement value)
          (valueRegs_nodup τ dst) (by simp) i.val (by simp)
    rw [assigned]
    exact Word.ofNat_toNat_of_lt (fits.fields placement i)

/-- Caller restoration retains the lexical environment while preserving the
callee's actual shared state. No heap or I/O frame premise is needed. -/
theorem restore {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    {placement : Nat → Word w} (matched : layout.Matches placement env entry.regs)
    (callee : Source.State w) : layout.Matches placement env (entry.restore callee).regs := matched

end RegisterMap.Matches

end Ram.LanguageCompiler
