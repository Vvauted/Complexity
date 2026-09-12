/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Computability.Ram.Array.Basic
import Init.Data.List.OfFn
import Mathlib.Data.List.OfFn

/-!
# Fields of source values

Each source type has a fixed number of actual word fields. Encoding enumerates
those fields in order using `List.ofFn`; Unit has no field or dummy word.
The encoding alone does not assert that mathematical fields fit a word.
Register layouts and their exact representation use the same field indices.
Borrowed views carry their actual word address and mathematical length. The
placement is proof-level representation data, not a compiler or runtime argument.
An empty view at an address-space endpoint may wrap its unused address field.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The number of actual words used by a source value. -/
@[simp] def fieldCount : Ty → Nat
  | .nat | .bool | .node _ => 1
  | .unit => 0
  | .buffer _ => 2
  | .prod left right => fieldCount left + fieldCount right
  | .option value => fieldCount value + 1

/-- Source value ranges, independently of any physical object placement.
Buffer validity in a source heap is a separate semantic condition. -/
@[simp] def ValueFits (w : Nat) : {τ : Ty} → Value τ → Prop
  | .nat, value => value < 2 ^ w
  | .bool, value => (if value then 1 else 0) < 2 ^ w
  | .unit, _ => True
  | .buffer _, value => value.length < 2 ^ w
  | .node _, _ => True
  | .prod _ _, value => ValueFits w value.1 ∧ ValueFits w value.2
  | .option _, none => True
  | .option _, some value => 1 < 2 ^ w ∧ ValueFits w value

/-- An optional node reference contributes only its tag range. Physical pointer
validity and placement remain separate representation conditions. -/
theorem ValueFits.option_node {kind : CellTy} {w : Nat}
    (positive : 0 < w) (root : Option (NodeRef kind)) :
    ValueFits w (τ := .option (.node kind)) root := by
  cases root with
  | none => trivial
  | some ref => exact ⟨Nat.one_lt_two_pow (Nat.ne_of_gt positive), trivial⟩

/-- The mathematical value of an actual representation field. -/
def valueField (placement : Nat → Word w) : {τ : Ty} → Value τ → Fin (fieldCount τ) → Nat
  | .nat, value, _ => value
  | .bool, value, _ => if value then 1 else 0
  | .unit, _, i => Fin.elim0 i
  | .buffer _, value, i =>
      if i.val = 0 then (arrayAddr (placement value.object) value.offset).toNat else value.length
  | .node _, value, _ => (placement value.object).toNat
  | .prod _ _, value, i =>
      Fin.addCases (valueField placement value.1) (valueField placement value.2) i
  | .option _, none, _ => 0
  | .option _, some value, i => Fin.cases 1 (valueField placement value) i

@[simp] theorem valueField_prod_left (placement : Nat → Word w)
    (value : Value (.prod left right)) (i : Fin (fieldCount left)) :
    valueField placement value (i.castAdd (fieldCount right)) =
      valueField placement value.1 i := Fin.addCases_left i

@[simp] theorem valueField_prod_right (placement : Nat → Word w)
    (value : Value (.prod left right)) (i : Fin (fieldCount right)) :
    valueField placement value (i.natAdd (fieldCount left)) =
      valueField placement value.2 i := Fin.addCases_right i

@[simp] theorem valueField_none (placement : Nat → Word w) (i : Fin (fieldCount (.option τ))) :
    valueField placement (τ := .option τ) none i = 0 := rfl

@[simp] theorem valueField_some_zero (placement : Nat → Word w) (value : Value τ) :
    valueField placement (τ := .option τ) (some value) ⟨0, Nat.zero_lt_succ _⟩ = 1 := rfl

@[simp] theorem valueField_some_succ (placement : Nat → Word w) (value : Value τ)
    (i : Fin (fieldCount τ)) :
    valueField placement (τ := .option τ) (some value) i.succ =
      valueField placement value i := rfl

@[simp] theorem valueField_nat (placement : Nat → Word w) (value : Nat)
    (i : Fin (fieldCount .nat)) : valueField placement (τ := .nat) value i = value := rfl

@[simp] theorem valueField_bool (placement : Nat → Word w) (value : Bool)
    (i : Fin (fieldCount .bool)) :
    valueField placement (τ := .bool) value i = (if value then 1 else 0) := rfl

@[simp] theorem valueField_buffer_zero (placement : Nat → Word w) (value : Buffer kind) :
    valueField placement (τ := .buffer kind) value ⟨0, by change 0 < 2; decide⟩ =
      (arrayAddr (placement value.object) value.offset).toNat := rfl

@[simp] theorem valueField_buffer_one (placement : Nat → Word w) (value : Buffer kind) :
    valueField placement (τ := .buffer kind) value ⟨1, by change 1 < 2; decide⟩ =
      value.length := rfl

@[simp] theorem valueField_node (placement : Nat → Word w) (value : NodeRef kind)
    (i : Fin (fieldCount (.node kind))) :
    valueField placement (τ := .node kind) value i = (placement value.object).toNat := rfl

/-- The source range condition is exactly the range of every encoded field.
The address field is already a word, even at an unused wrapping endpoint. -/
theorem valueFits_iff (placement : Nat → Word w) {τ : Ty} (value : Value τ) :
    ValueFits w value ↔ ∀ i : Fin (fieldCount τ), valueField placement value i < 2 ^ w := by
  induction τ with
  | nat | bool =>
      constructor
      · intro fits i
        exact fits
      · intro fields
        exact fields ⟨0, by decide⟩
  | unit =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        trivial
  | buffer kind =>
      constructor
      · intro fits i
        by_cases zero : i.val = 0
        · simpa only [valueField, if_pos zero] using
            (arrayAddr (placement value.object) value.offset).isLt
        · simpa only [valueField, if_neg zero] using fits
      · intro fields
        exact fields ⟨1, by change 1 < 2; decide⟩
  | node kind =>
      constructor
      · intro _ _
        exact (placement value.object).isLt
      · intro _
        trivial
  | prod left right ihLeft ihRight =>
      constructor
      · rintro ⟨leftFits, rightFits⟩ i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simpa only [valueField_prod_left] using (ihLeft value.1).mp leftFits j
        · intro j
          simpa only [valueField_prod_right] using (ihRight value.2).mp rightFits j
      · intro fields
        exact ⟨(ihLeft value.1).mpr (fun i => by
          simpa only [valueField_prod_left] using fields (i.castAdd (fieldCount right))),
          (ihRight value.2).mpr (fun i => by
            simpa only [valueField_prod_right] using fields (i.natAdd (fieldCount left)))⟩
  | option τ ih =>
      cases value with
      | none => simp only [ValueFits, valueField_none, Nat.two_pow_pos, implies_true]
      | some value =>
          constructor
          · rintro ⟨tagFits, payloadFits⟩ i
            refine Fin.cases tagFits ?_ i
            intro j
            exact (ih value).mp payloadFits j
          · intro fields
            exact ⟨fields ⟨0, Nat.zero_lt_succ _⟩,
              (ih value).mpr (fun i => fields i.succ)⟩

/-- Any chosen placement exposes the same source-admissible field ranges. -/
theorem ValueFits.fields {τ : Ty} {value : Value τ} (fits : ValueFits w value)
    (placement : Nat → Word w) (i : Fin (fieldCount τ)) :
    valueField placement value i < 2 ^ w := (valueFits_iff placement value).mp fits i

/-- Encode every actual field, in its declared order. -/
def valueWords (placement : Nat → Word w) {τ : Ty} (value : Value τ) : List (Word w) :=
  List.ofFn fun i => BitVec.ofNat w (valueField placement value i)

@[simp] theorem valueWords_length (placement : Nat → Word w) {τ : Ty} (value : Value τ) :
    (valueWords placement value).length = fieldCount τ := List.length_ofFn

/-- Field lookup observes an actual list entry, never an out-of-range default. -/
@[simp] theorem valueWords_getElem (placement : Nat → Word w) {τ : Ty} (value : Value τ)
    (i : Fin (fieldCount τ)) :
    (valueWords placement value)[i.val]'(by simp) =
      BitVec.ofNat w (valueField placement value i) := List.getElem_ofFn _

@[simp] theorem valueWords_getElem? (placement : Nat → Word w) {τ : Ty} (value : Value τ)
    (i : Fin (fieldCount τ)) :
    (valueWords placement value)[i.val]? =
      some (BitVec.ofNat w (valueField placement value i)) := by
  simp only [valueWords, List.getElem?_ofFn, dif_pos i.isLt]

@[simp] theorem valueWords_nat (placement : Nat → Word w) (value : Nat) :
    valueWords placement (τ := .nat) value = [BitVec.ofNat w value] := by
  simp only [valueWords, fieldCount, List.ofFn_succ, List.ofFn_zero, valueField_nat]

@[simp] theorem valueWords_bool (placement : Nat → Word w) (value : Bool) :
    valueWords placement (τ := .bool) value = [BitVec.ofNat w (if value then 1 else 0)] := by
  simp only [valueWords, fieldCount, List.ofFn_succ, List.ofFn_zero, valueField_bool]

@[simp] theorem valueWords_unit (placement : Nat → Word w) (value : Unit) :
    valueWords placement (τ := .unit) value = [] := List.ofFn_zero

@[simp] theorem valueWords_buffer (placement : Nat → Word w) (value : Buffer kind) :
    valueWords placement (τ := .buffer kind) value =
      [arrayAddr (placement value.object) value.offset, BitVec.ofNat w value.length] := by
  simp [valueWords, List.ofFn_succ, valueField]

@[simp] theorem valueWords_node (placement : Nat → Word w) (value : NodeRef kind) :
    valueWords placement (τ := .node kind) value = [placement value.object] := by
  simp [valueWords, List.ofFn_succ, valueField]

/-- Product values concatenate the actual fields of their two components. -/
@[simp] theorem valueWords_prod (placement : Nat → Word w)
    (left : Value α) (right : Value β) :
    valueWords placement (τ := .prod α β) (left, right) =
      valueWords placement left ++ valueWords placement right := by
  simp only [valueWords, fieldCount, List.ofFn_add]
  congr 1 <;> congr 1 <;> funext i
  · exact congrArg (BitVec.ofNat w) (valueField_prod_left placement (left, right) i)
  · exact congrArg (BitVec.ofNat w) (valueField_prod_right placement (left, right) i)

/-- An absent optional value has a zero tag and a canonical zero-filled payload. -/
@[simp] theorem valueWords_none (placement : Nat → Word w) (τ : Ty) :
    valueWords placement (τ := .option τ) none =
      List.replicate (fieldCount τ + 1) (0 : Word w) := by
  exact List.ofFn_const (fieldCount τ + 1) (0 : Word w)

/-- A present optional value preserves every payload field after its tag. -/
@[simp] theorem valueWords_some (placement : Nat → Word w) (value : Value τ) :
    valueWords placement (τ := .option τ) (some value) =
      BitVec.ofNat w 1 :: valueWords placement value := by
  unfold valueWords
  rw [List.ofFn_succ]
  rfl

end Ram.LanguageCompiler
