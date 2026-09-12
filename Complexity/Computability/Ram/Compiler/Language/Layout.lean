/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Scalar
import Complexity.Computability.Ram.Source.Function.Basic
import Complexity.Language.State
import Init.Data.List.Nat.Range

/-!
# Field layouts and parameter representation

The backend represents natural numbers and booleans by one word, node references
by one placed address, borrowed buffers by address and length, and Unit by no words.
Products concatenate their
fields; options reserve a tag followed by the payload's fixed field region.
Parameter layouts follow lexical parameter order without reserving dummy slots
for Unit. The same field
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

@[simp] theorem valueRegs_node (kind : CellTy) (dst : Reg) :
    valueRegs (.node kind) dst = [dst] := rfl

/-- Product reception concatenates both actual field regions. -/
@[simp] theorem valueRegs_prod (left right : Ty) (dst : Reg) :
    valueRegs (.prod left right) dst =
      valueRegs left dst ++ valueRegs right (dst + fieldCount left) :=
  List.range'_append_1.symm

/-- Option reception places the tag before the fixed-size payload region. -/
@[simp] theorem valueRegs_option (τ : Ty) (dst : Reg) :
    valueRegs (.option τ) dst = dst :: valueRegs τ (dst + 1) := rfl

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

/-- Updating an existing variable preserves all source value range facts. -/
theorem set {env : Env Γ} (fits : EnvFits w env) (target : Var Γ τ)
    (value : Value τ) (fitsValue : ValueFits w value) : EnvFits w (env.set target value) := by
  induction target with
  | here => exact EnvFits.cons (EnvFits.tail fits) value fitsValue
  | there target ih =>
      exact EnvFits.cons (ih (EnvFits.tail fits) value fitsValue) env.head (fits .here)

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

/-- A node reference carries a placed word address, not a word-sized object
identifier. Existing-object and node-validity conditions are separate. -/
@[simp] theorem cons_node_iff (value : NodeRef kind) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .node kind) value env) ↔ EnvFits w env := by
  simp only [cons_iff, ValueFits, true_and]

/-- Product parameter ranges are precisely the ranges of their two components. -/
@[simp] theorem cons_prod_iff (value : Value (.prod left right)) (env : Env Γ) :
    EnvFits w (Env.cons value env) ↔
      (ValueFits w value.1 ∧ ValueFits w value.2) ∧ EnvFits w env := by
  rw [cons_iff]
  rfl

/-- An absent payload uses only zero-filled fields, at every word width. -/
@[simp] theorem cons_none_iff (τ : Ty) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .option τ) none env) ↔ EnvFits w env := by
  simp only [cons_iff, ValueFits, true_and]

/-- A present payload requires its actual fields and the nonzero tag to fit. -/
@[simp] theorem cons_some_iff (value : Value τ) (env : Env Γ) :
    EnvFits w (Env.cons (τ := .option τ) (some value) env) ↔
      (1 < 2 ^ w ∧ ValueFits w value) ∧ EnvFits w env := by
  rw [cons_iff]
  rfl

end EnvFits

namespace RegisterMap

/-- The first actual field of a variable. A fieldless Unit needs no destination. -/
def base (layout : RegisterMap Γ) (target : Var Γ τ) : Reg :=
  if positive : 0 < fieldCount τ then layout target ⟨0, positive⟩ else 0

/-- A represented variable's base is its zero-indexed field. -/
theorem base_of_pos (layout : RegisterMap Γ) (target : Var Γ τ)
    (positive : 0 < fieldCount τ) :
    base layout target = layout target ⟨0, positive⟩ := by
  simp only [base, dif_pos positive]

/-- Generated layouts give each variable consecutive fields and never identify
fields belonging to different typed variables. No heap separation is asserted. -/
structure Regular (layout : RegisterMap Γ) : Prop where
  fields : ∀ {τ} (target : Var Γ τ) (i : Fin (fieldCount τ)),
    layout target i = base layout target + i.val
  injective : ∀ {τ σ} (target : Var Γ τ) (other : Var Γ σ)
    (i : Fin (fieldCount τ)) (j : Fin (fieldCount σ)),
    layout target i = layout other j →
      (⟨τ, target⟩ : Sigma (Var Γ)) = ⟨σ, other⟩

/-- A distinct variable's fields avoid the complete receiver of the target. -/
theorem Regular.other {layout : RegisterMap Γ} (regular : Regular layout)
    (target : Var Γ τ) (source : Var Γ σ) (different : ¬HEq target source)
    (i : Fin (fieldCount σ)) :
    layout source i < base layout target ∨
      base layout target + fieldCount τ ≤ layout source i := by
  by_cases before : layout source i < base layout target
  · exact Or.inl before
  · apply Or.inr
    by_contra after
    have lower : base layout target ≤ layout source i := Nat.le_of_not_gt before
    have upper : layout source i < base layout target + fieldCount τ := Nat.lt_of_not_ge after
    let j : Fin (fieldCount τ) :=
      ⟨layout source i - base layout target, (Nat.sub_lt_iff_lt_add' lower).mpr upper⟩
    have equal : layout target j = layout source i := by
      rw [regular.fields target j]
      exact Nat.add_sub_of_le lower
    exact different (Sigma.mk.inj (regular.injective target source j i equal)).2

/-- Variables of different source types occupy disjoint field regions. A
fieldless target needs no additional positivity or register-allocation premise. -/
theorem Regular.other_type {layout : RegisterMap Γ} (regular : Regular layout)
    (target : Var Γ τ) (source : Var Γ σ) (different : τ ≠ σ)
    (i : Fin (fieldCount σ)) :
    layout source i < base layout target ∨
      base layout target + fieldCount τ ≤ layout source i := by
  by_cases before : layout source i < base layout target
  · exact Or.inl before
  · apply Or.inr
    by_contra after
    have lower : base layout target ≤ layout source i := Nat.le_of_not_gt before
    have upper : layout source i < base layout target + fieldCount τ := Nat.lt_of_not_ge after
    let j : Fin (fieldCount τ) :=
      ⟨layout source i - base layout target, (Nat.sub_lt_iff_lt_add' lower).mpr upper⟩
    have equal : layout target j = layout source i := by
      rw [regular.fields target j]
      exact Nat.add_sub_of_le lower
    exact different (congrArg Sigma.fst (regular.injective target source j i equal))

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

/-- A nonempty fresh binding starts at its allocated destination. -/
@[simp] theorem base_extend_here (layout : RegisterMap Γ) (dst : Reg)
    (positive : 0 < fieldCount τ) : base (extend layout τ dst) .here = dst := by
  rw [base_of_pos _ _ positive, extend_here, Nat.add_zero]

/-- A fresh binding does not relocate any existing variable. -/
@[simp] theorem base_extend_there (layout : RegisterMap Γ) (τ : Ty) (dst : Reg)
    (target : Var Γ σ) : base (extend layout τ dst) (.there target) = base layout target := by
  simp only [base, extend_there]

/-- Fresh allocation automatically preserves the layout discipline needed by
updates of existing variables. -/
theorem Regular.extend {layout : RegisterMap Γ} (regular : Regular layout)
    (bounded : layout.Bounded next) : Regular (RegisterMap.extend layout τ next) := by
  constructor
  · intro σ target i
    cases target with
    | here =>
        rw [extend_here, base_extend_here layout next (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)]
    | there target =>
        simpa only [extend_there, base_extend_there] using regular.fields target i
  · intro σ υ target other i j equal
    cases target with
    | here =>
        cases other with
        | here => rfl
        | there other =>
            change next + i.val = layout other j at equal
            exact False.elim (Nat.not_le_of_gt (bounded other j)
              (equal ▸ Nat.le_add_right next i.val))
    | there target =>
        cases other with
        | here =>
            change layout target i = next + j.val at equal
            exact False.elim (Nat.not_le_of_gt (bounded target i)
              (equal.symm ▸ Nat.le_add_right next j.val))
        | there other =>
            exact congrArg
              (fun v : Sigma (Var Γ) => (⟨v.1, Var.there v.2⟩ : Sigma (Var (τ :: Γ))))
              (regular.injective target other i j equal)

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

/-- Compact parameter allocation is regular, including zero-field parameters. -/
theorem parameterMap_regular (Γ : List Ty) (base : Reg := 0) :
    RegisterMap.Regular (parameterMap Γ base) := by
  induction Γ generalizing base with
  | nil =>
      constructor
      · intro τ target i; cases target
      · intro τ σ target other i j equal; cases target
  | cons τ Γ ih =>
      constructor
      · intro σ target i
        cases target with
        | here =>
            change base + i.val =
              RegisterMap.base (RegisterMap.extend (parameterMap Γ (base + fieldCount τ)) τ base)
                .here + i.val
            rw [RegisterMap.base_extend_here _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)]
        | there target =>
            simpa only [parameterMap, RegisterMap.extend_there, RegisterMap.base_extend_there]
              using (ih (base + fieldCount τ)).fields target i
      · intro σ υ target other i j equal
        cases target with
        | here =>
            cases other with
            | here => rfl
            | there other =>
                have lower : base + fieldCount τ ≤ parameterMap Γ (base + fieldCount τ) other j := by
                  rw [parameterMap_add]
                  exact Nat.le_add_right _ _
                change base + i.val = parameterMap Γ (base + fieldCount τ) other j at equal
                exact False.elim (Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt base) lower) equal)
        | there target =>
            cases other with
            | here =>
                have lower : base + fieldCount τ ≤ parameterMap Γ (base + fieldCount τ) target i := by
                  rw [parameterMap_add]
                  exact Nat.le_add_right _ _
                change parameterMap Γ (base + fieldCount τ) target i = base + j.val at equal
                exact False.elim (Nat.ne_of_lt
                  (Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt base) lower) equal.symm)
            | there other =>
                exact congrArg
                  (fun v : Sigma (Var Γ) => (⟨v.1, Var.there v.2⟩ : Sigma (Var (τ :: Γ))))
                  ((ih (base + fieldCount τ)).injective target other i j equal)

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

/-- Ordered field reception updates exactly the selected source variable.
Regularity is supplied by the generated layout, not by the source algorithm. -/
theorem set {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    {placement : Nat → Word w} (matched : layout.Matches placement env entry.regs)
    (regular : RegisterMap.Regular layout) (target : Var Γ τ) (value : Value τ)
    (fits : ValueFits w value) :
    layout.Matches placement (env.set target value)
      (entry.setRegs (valueRegs τ (RegisterMap.base layout target))
        (valueWords placement value)).regs := by
  intro σ other i
  by_cases same : (⟨τ, target⟩ : Sigma (Var Γ)) = ⟨σ, other⟩
  · have types := congrArg Sigma.fst same
    cases types
    have matchedVariables := eq_of_heq (Sigma.mk.inj same).2
    cases matchedVariables
    rw [Env.get_set_self, regular.fields target i]
    have assigned :
        (entry.setRegs (valueRegs τ (RegisterMap.base layout target))
          (valueWords placement value)).regs (RegisterMap.base layout target + i.val) =
          BitVec.ofNat w (valueField placement value i) := by
      simpa only [valueRegs_getElem, valueWords_getElem] using
        Source.State.setRegs_getElem entry (valueRegs τ (RegisterMap.base layout target))
          (valueWords placement value) (valueRegs_nodup τ _) (by simp) i.val (by simp)
    rw [assigned]
    exact Word.ofNat_toNat_of_lt (fits.fields placement i)
  · have outside : layout other i ∉ valueRegs τ (RegisterMap.base layout target) := by
      intro member
      have interval := mem_valueRegs.mp member
      let j : Fin (fieldCount τ) :=
        ⟨layout other i - RegisterMap.base layout target,
          (Nat.sub_lt_iff_lt_add' interval.1).mpr interval.2⟩
      apply same
      apply regular.injective target other j i
      rw [regular.fields target j]
      exact Nat.add_sub_of_le interval.1
    rw [Source.State.setRegs_ne entry _ _ _ outside, matched other i]
    have unchanged : (env.set target value).get other = env.get other := by
      by_cases types : τ = σ
      · cases types
        apply Env.get_set_of_ne
        intro equal
        apply same
        cases eq_of_heq equal
        rfl
      · exact Env.get_set_of_type_ne env target value other types
    rw [unchanged]

/-- Caller restoration retains the lexical environment while preserving the
callee's actual shared state. No heap or I/O frame premise is needed. -/
theorem restore {layout : RegisterMap Γ} {env : Env Γ} {entry : Source.State w}
    {placement : Nat → Word w} (matched : layout.Matches placement env entry.regs)
    (callee : Source.State w) : layout.Matches placement env (entry.restore callee).regs := matched

end RegisterMap.Matches

end Ram.LanguageCompiler
