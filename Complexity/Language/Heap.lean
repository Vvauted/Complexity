/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Shared source objects and borrowed buffers

The heap contains native arrays with a scalar type tag. A buffer is only an
object identifier, offset and length: copying a handle or taking a slice does
not copy its contents. Overlapping views of one object therefore observe the
same writes. Object identifiers are not machine addresses.

Reads and writes check the object's type, the entire view extent and the local
index. Invalid accesses return an explicit error, never a default value or a
successful no-op. Updates use Lean's array operations; their successful-access
conditions establish that the updated slots exist. Slicing checks relative
extent only; validity of the original object is a separate heap predicate.

These are mathematical operations on a shared heap, not yet statement syntax,
an execution relation or a claim about allocation or machine costs.
-/

namespace Complexity.Language

/-- Scalar element types of the initial shared objects. -/
inductive CellTy where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- Object cells use the ordinary Lean scalar types. -/
abbrev CellValue : CellTy → Type
  | .nat => Nat
  | .bool => Bool

/-- An object owns one native array and its element type. -/
abbrev HeapObject := Σ τ : CellTy, Array (CellValue τ)

/-- A borrowed view. Equal or overlapping views need not be distinct handles. -/
structure Buffer (τ : CellTy) where
  object : Nat
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- A finite collection of shared objects; handles index this array. -/
structure Heap where
  objects : Array HeapObject

namespace Heap

/-- Failed object/type lookup, an invalid whole view, or an invalid local index. -/
inductive Error where
  /-- The identifier is absent or its object has a different scalar type. -/
  | invalidObject
  | invalidView
  | outOfBounds
  deriving DecidableEq, Repr

private def objectValues? : (τ : CellTy) → HeapObject → Option (Array (CellValue τ))
  | .nat, ⟨.nat, values⟩ => some values
  | .bool, ⟨.bool, values⟩ => some values
  | _, _ => none

/-- Look up the current array, checking the stored element type. -/
def object? (heap : Heap) (τ : CellTy) (object : Nat) : Option (Array (CellValue τ)) :=
  heap.objects[object]?.bind (objectValues? τ)

/-- Typed lookup is exactly lookup of the corresponding native array object. -/
theorem object?_eq_some_iff {heap : Heap} {τ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} :
    heap.object? τ object = some values ↔ heap.objects[object]? = some ⟨τ, values⟩ := by
  cases found : heap.objects[object]? with
  | none => simp [object?, found]
  | some stored =>
      rcases stored with ⟨kind, contents⟩
      cases kind <;> cases τ <;> simp [object?, objectValues?, found]

/-- A successful typed lookup denotes an existing object slot. -/
theorem object_lt_size {heap : Heap} {τ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ object = some values) :
    object < heap.objects.size :=
  (Array.getElem?_eq_some_iff.mp (object?_eq_some_iff.mp found)).choose

/-- Mathematical replacement of an object slot. Operational writes below first
check that this slot exists and preserve its element type and length. -/
def replace (heap : Heap) (object : Nat) {τ : CellTy} (values : Array (CellValue τ)) : Heap :=
  ⟨heap.objects.setIfInBounds object ⟨τ, values⟩⟩

/-- Replacing an existing object exposes precisely its new native contents. -/
theorem object?_replace_self {heap : Heap} {object : Nat} {τ : CellTy}
    {values : Array (CellValue τ)} (bound : object < heap.objects.size) :
    (heap.replace object values).object? τ object = some values := by
  apply object?_eq_some_iff.mpr
  exact Array.getElem?_setIfInBounds_self_of_lt bound

/-- Other object slots retain their contents, also when their types differ. -/
theorem object?_replace_ne {heap : Heap} {object other : Nat} {τ σ : CellTy}
    {values : Array (CellValue τ)} (different : object ≠ other) :
    (heap.replace object values).object? σ other = heap.object? σ other := by
  simp only [object?, replace, Array.getElem?_setIfInBounds_ne different]

end Heap

namespace Buffer

/-- A valid view denotes the advertised type and lies entirely within its object. -/
def Valid {τ : CellTy} (buffer : Buffer τ) (heap : Heap) : Prop :=
  ∃ values, heap.object? τ buffer.object = some values ∧
    buffer.offset + buffer.length ≤ values.size

/-- Form a view of a view without accessing or copying the object. The original
view's object/type validity is supplied separately by `Valid`. -/
def slice {τ : CellTy} (buffer : Buffer τ) (offset length : Nat) :
    Except Heap.Error (Buffer τ) :=
  if offset + length ≤ buffer.length then
    .ok ⟨buffer.object, buffer.offset + offset, length⟩
  else .error .outOfBounds

/-- A fitting slice retains the same object and adds only its relative offset. -/
theorem slice_eq {τ : CellTy} (buffer : Buffer τ) {offset length : Nat}
    (bound : offset + length ≤ buffer.length) :
    buffer.slice offset length = .ok ⟨buffer.object, buffer.offset + offset, length⟩ := by
  simp [slice, bound]

/-- Relative slicing preserves validity of an already valid view. -/
theorem Valid.slice {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    (valid : buffer.Valid heap) {offset length : Nat}
    (bound : offset + length ≤ buffer.length) :
    (⟨buffer.object, buffer.offset + offset, length⟩ : Buffer τ).Valid heap := by
  obtain ⟨values, found, extent⟩ := valid
  exact ⟨values, found, by dsimp; omega⟩

end Buffer

namespace Heap

/-- Read the current shared cell after checking object, view and index validity. -/
def read (heap : Heap) {τ : CellTy} (buffer : Buffer τ) (index : Nat) :
    Except Error (CellValue τ) :=
  match heap.object? τ buffer.object with
  | none => .error .invalidObject
  | some values =>
      if extent : buffer.offset + buffer.length ≤ values.size then
        if bound : index < buffer.length then
          .ok (getElem values (buffer.offset + index) (by omega))
        else .error .outOfBounds
      else .error .invalidView

/-- Update one current shared cell. Both native array updates target existing
slots because the object lookup, whole view and local index were checked. -/
def write (heap : Heap) {τ : CellTy} (buffer : Buffer τ) (index : Nat)
    (value : CellValue τ) : Except Error Heap :=
  match heap.object? τ buffer.object with
  | none => .error .invalidObject
  | some values =>
      if buffer.offset + buffer.length ≤ values.size then
        if index < buffer.length then
          .ok (heap.replace buffer.object
            (values.setIfInBounds (buffer.offset + index) value))
        else .error .outOfBounds
      else .error .invalidView

/-- A valid read is ordinary native array indexing at the view's absolute index. -/
theorem read_eq {heap : Heap} {τ : CellTy} {buffer : Buffer τ} {index : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ buffer.object = some values)
    (extent : buffer.offset + buffer.length ≤ values.size) (bound : index < buffer.length) :
    heap.read buffer index = .ok (getElem values (buffer.offset + index) (by omega)) := by
  simp [read, found, extent, bound]

/-- Successful writes give the native contents, actual validity conditions and
the precise updated heap. This rules out a successful out-of-bounds no-op. -/
theorem write_eq_ok_iff {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ} :
    heap.write buffer index value = .ok finish ↔
      ∃ values, heap.object? τ buffer.object = some values ∧
        buffer.offset + buffer.length ≤ values.size ∧ index < buffer.length ∧
        finish = heap.replace buffer.object
          (values.setIfInBounds (buffer.offset + index) value) := by
  cases found : heap.object? τ buffer.object with
  | none => simp [write, found]
  | some values =>
      by_cases extent : buffer.offset + buffer.length ≤ values.size
      · by_cases bound : index < buffer.length <;> simp [write, found, extent, bound, eq_comm]
      · simp [write, found, extent]

/-- A successful source write uses actual native `Array.set` at both levels. -/
theorem write_eq_set {heap : Heap} {τ : CellTy} {buffer : Buffer τ} {index : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ buffer.object = some values)
    (extent : buffer.offset + buffer.length ≤ values.size) (bound : index < buffer.length)
    (value : CellValue τ) :
    heap.write buffer index value = .ok
      ⟨heap.objects.set buffer.object
        ⟨τ, values.set (buffer.offset + index) value (by omega)⟩ (object_lt_size found)⟩ := by
  simp [write, found, extent, bound, replace, Array.setIfInBounds_def,
    object_lt_size found, show buffer.offset + index < values.size by omega]

/-- A write preserves the complete contents of every different object. No
condition is imposed on distinct handles for the object that was written. -/
theorem object?_write_of_ne {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {index other : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (different : buffer.object ≠ other) :
    finish.object? σ other = heap.object? σ other := by
  obtain ⟨values, _, _, _, rfl⟩ := write_eq_ok_iff.mp written
  exact object?_replace_ne different

/-- Reads from another object are unchanged, including their error outcomes. -/
theorem read_write_of_ne {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {other : Buffer σ} {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (different : buffer.object ≠ other.object) :
    finish.read other otherIndex = heap.read other otherIndex := by
  simp only [read, object?_write_of_ne (σ := σ) written different]

/-- A read of another cell in the same object is unchanged, including its error
outcome. Views may overlap; only the two absolute cell indices must differ. -/
theorem read_write_of_ne_cell {heap finish : Heap} {τ : CellTy}
    {buffer other : Buffer τ} {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (sameObject : buffer.object = other.object)
    (differentCell : buffer.offset + index ≠ other.offset + otherIndex) :
    finish.read other otherIndex = heap.read other otherIndex := by
  obtain ⟨values, found, _, _, rfl⟩ := write_eq_ok_iff.mp written
  have original : heap.object? τ other.object = some values := by
    simpa only [← sameObject] using found
  have updated :
      (heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)).object?
        τ other.object = some (values.setIfInBounds (buffer.offset + index) value) := by
    rw [← sameObject]
    exact object?_replace_self (object_lt_size found)
  by_cases extent : other.offset + other.length ≤ values.size
  · by_cases bound : otherIndex < other.length
    · rw [read_eq updated (by simpa using extent) bound, read_eq original extent bound]
      exact congrArg Except.ok (Array.getElem_setIfInBounds_ne
        (xs := values) (i := buffer.offset + index) (a := value)
        (j := other.offset + otherIndex) (by omega) differentCell)
    · simp [read, updated, original, extent, bound]
  · simp [read, updated, original, extent]

/-- Any valid alias of the written cell observes its new value. Views may be
equal, differently sized or overlapping; equality is on object and cell identity. -/
theorem read_write_alias {heap finish : Heap} {τ : CellTy} {buffer other : Buffer τ}
    {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (valid : other.Valid heap) (sameObject : buffer.object = other.object)
    (bound : otherIndex < other.length)
    (sameCell : buffer.offset + index = other.offset + otherIndex) :
    finish.read other otherIndex = .ok value := by
  obtain ⟨values, found, extent, indexBound, rfl⟩ := write_eq_ok_iff.mp written
  obtain ⟨otherValues, otherFound, otherExtent⟩ := valid
  rw [← sameObject, found] at otherFound
  have sameValues : otherValues = values := (Option.some.inj otherFound).symm
  subst otherValues
  have updated :
      (heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)).object?
        τ other.object = some (values.setIfInBounds (buffer.offset + index) value) := by
    rw [← sameObject]
    exact object?_replace_self (object_lt_size found)
  rw [read_eq updated (by simpa using otherExtent) bound]
  apply congrArg Except.ok
  have cellBound : buffer.offset + index < values.size := by omega
  simpa only [← sameCell] using
    (Array.getElem_setIfInBounds_self
      (xs := values) (i := buffer.offset + index) (a := value) (by simpa using cellBound))

/-- Reading through the written handle itself returns the actual stored value. -/
theorem read_write {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    finish.read buffer index = .ok value := by
  obtain ⟨values, found, extent, bound, _⟩ := write_eq_ok_iff.mp written
  exact read_write_alias written ⟨values, found, extent⟩ rfl bound rfl

end Heap

namespace Buffer

/-- A successful write preserves every valid view's object, type and extent.
The views may be equal or overlap; no separation of their handles is required. -/
theorem Valid.write {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {other : Buffer σ} {index : Nat} {value : CellValue τ}
    (valid : other.Valid heap) (written : heap.write buffer index value = .ok finish) :
    other.Valid finish := by
  obtain ⟨values, found, _, _, rfl⟩ := Heap.write_eq_ok_iff.mp written
  obtain ⟨otherValues, otherFound, otherExtent⟩ := valid
  by_cases sameObject : buffer.object = other.object
  · have sameStored : (⟨τ, values⟩ : HeapObject) = ⟨σ, otherValues⟩ := by
      apply Option.some.inj
      exact (Heap.object?_eq_some_iff.mp found).symm.trans
        (by simpa only [← sameObject] using Heap.object?_eq_some_iff.mp otherFound)
    have sameType : τ = σ := congrArg Sigma.fst sameStored
    subst σ
    have sameValues : otherValues = values := by
      rw [← sameObject, found] at otherFound
      exact (Option.some.inj otherFound).symm
    subst otherValues
    refine ⟨values.setIfInBounds (buffer.offset + index) value, ?_, ?_⟩
    · rw [← sameObject]
      exact Heap.object?_replace_self (Heap.object_lt_size found)
    · simpa using otherExtent
  · exact ⟨otherValues, (Heap.object?_replace_ne sameObject).trans otherFound, otherExtent⟩

end Buffer

end Complexity.Language
