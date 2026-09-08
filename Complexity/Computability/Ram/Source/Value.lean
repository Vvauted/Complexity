/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Ref

/-!
# Typed views of source value fields

Word, array-reference and unit values are represented by one, two and zero
words respectively. Encoding and decoding identify those same fields; they
neither allocate arrays nor load mathematical data into source memory.
The source syntax and callable-function proof interfaces share this representation.
-/

namespace Ram.DSL

/-- Source value shape; arrays have two word fields and `Unit` has none. -/
inductive ValueKind where
  | word
  | array
  | unit
  deriving BEq, Inhabited

/-- Number of physical words in a source value. -/
def ValueKind.width : ValueKind → Nat
  | .word => 1
  | .array => 2
  | .unit => 0

/-- Ordinary Lean value represented by the declared result fields. -/
def ValueKind.Value (kind : ValueKind) (w : Nat) : Type :=
  match kind with
  | .word => Ram.Word w
  | .array => Ram.ArrayRef w
  | .unit => Unit

/-- The actual fields of a typed value, without allocation or memory access. -/
def ValueKind.encode {w : Nat} (kind : ValueKind) : kind.Value w → List (Ram.Word w) :=
  match kind with
  | .word => fun value => [value]
  | .array => Ram.ArrayRef.args
  | .unit => fun _ => []

@[simp] theorem ValueKind.encode_word (value : Ram.Word w) :
    ValueKind.encode .word value = [value] := rfl

@[simp] theorem ValueKind.encode_array (value : Ram.ArrayRef w) :
    ValueKind.encode .array value = [value.base, value.length] := rfl

@[simp] theorem ValueKind.encode_unit (value : Unit) :
    ValueKind.encode (w := w) .unit value = [] := rfl

/-- Each value has exactly its declared number of fields. -/
@[simp] theorem ValueKind.length_encode (kind : ValueKind) (value : kind.Value w) :
    (kind.encode value).length = kind.width := by
  cases kind <;> rfl

/-- Project actual fields with a proved shape. No missing field is replaced by a default. -/
def ValueKind.decode {w : Nat} (kind : ValueKind) (fields : List (Ram.Word w))
    (shape : fields.length = kind.width) : kind.Value w :=
  match kind with
  | .word => fields[0]'(by rw [shape]; decide)
  | .array => ⟨fields[0]'(by rw [shape]; decide), fields[1]'(by rw [shape]; decide)⟩
  | .unit => ()

@[simp] theorem ValueKind.decode_word (value : Ram.Word w)
    (shape : [value].length = ValueKind.word.width) :
    ValueKind.decode .word [value] shape = value := rfl

@[simp] theorem ValueKind.decode_array (base length : Ram.Word w)
    (shape : [base, length].length = ValueKind.array.width) :
    ValueKind.decode .array [base, length] shape = (⟨base, length⟩ : Ram.ArrayRef w) := rfl

@[simp] theorem ValueKind.decode_unit (fields : List (Ram.Word w))
    (shape : fields.length = ValueKind.unit.width) :
    ValueKind.decode .unit fields shape = () := rfl

/-- Decoding the actual representation recovers the typed value. -/
@[simp] theorem ValueKind.decode_encode (kind : ValueKind) (value : kind.Value w)
    (shape : (kind.encode value).length = kind.width) :
    kind.decode (kind.encode value) shape = value := by
  cases kind with
  | word => rfl
  | array => rfl
  | unit => cases value; rfl

/-- Typed observation retains every field of the original return value. -/
@[simp] theorem ValueKind.encode_decode (kind : ValueKind) (fields : List (Ram.Word w))
    (shape : fields.length = kind.width) :
    kind.encode (kind.decode fields shape) = fields := by
  cases kind with
  | word => exact (List.eq_getElem_of_length_eq_one fields shape).symm
  | array => exact (List.eq_getElem_of_length_eq_two fields shape).symm
  | unit => exact (List.eq_nil_of_length_eq_zero shape).symm

/-- A raw result equation transfers to a typed value without decomposing its fields. -/
theorem ValueKind.decode_eq_of_eq_encode (kind : ValueKind) {fields : List (Ram.Word w)}
    {value : kind.Value w} (shape : fields.length = kind.width)
    (equal : fields = kind.encode value) : kind.decode fields shape = value := by
  subst fields
  exact kind.decode_encode value _

/-- Distinct typed values cannot have the same actual fields. -/
theorem ValueKind.encode_injective (kind : ValueKind) :
    Function.Injective (kind.encode (w := w)) := by
  intro left right equal
  have decoded := kind.decode_eq_of_eq_encode (kind.length_encode left) equal
  simpa only [ValueKind.decode_encode] using decoded

@[simp] theorem ValueKind.encode_inj (kind : ValueKind) (left right : kind.Value w) :
    kind.encode left = kind.encode right ↔ left = right :=
  kind.encode_injective.eq_iff

end Ram.DSL
