/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Shape

/-!
# Fresh initialized source objects

`Heap.alloc` appends one typed native array and returns its complete view. Old
object contents are unchanged, including observations through overlapping views.
The fresh object has a new identity even when its array is empty.

These are independent mathematical heap operations and preservation rules.
They do not add a source statement, a RAM allocator, a capacity check, or an
initialization-cost claim. Such a lowering must initialize the actual target
cells and connect its counted execution to this same source operation.
-/

namespace Complexity.Language

namespace Heap

/-- Append one fresh initialized object and return its full view and updated heap. -/
def alloc (heap : Heap) {τ : CellTy} (length : Nat) (initial : CellValue τ) :
    Buffer τ × Heap :=
  (⟨heap.objects.size, 0, length⟩,
    ⟨heap.objects.push ⟨τ, Array.replicate length initial⟩⟩)

@[simp] theorem alloc_object (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) : (heap.alloc length initial).1.object = heap.objects.size := rfl

@[simp] theorem alloc_offset (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) : (heap.alloc length initial).1.offset = 0 := rfl

@[simp] theorem alloc_length (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) : (heap.alloc length initial).1.length = length := rfl

@[simp] theorem alloc_objects (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).2.objects =
      heap.objects.push ⟨τ, Array.replicate length initial⟩ := rfl

/-- Allocation increases the object domain by one, independently of the cell count. -/
@[simp] theorem alloc_size (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).2.objects.size = heap.objects.size + 1 := by
  simp only [alloc_objects, Array.size_push]

/-- Every object slot other than the newly appended slot is unchanged. -/
theorem getElem?_alloc_of_ne (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) {object : Nat} (different : object ≠ heap.objects.size) :
    (heap.alloc length initial).2.objects[object]? = heap.objects[object]? := by
  simp only [alloc_objects, Array.getElem?_push, if_neg different]

/-- Typed lookup away from the fresh identifier retains its exact outcome. -/
theorem object?_alloc_of_ne (heap : Heap) {τ σ : CellTy} (length : Nat)
    (initial : CellValue τ) {object : Nat} (different : object ≠ heap.objects.size) :
    (heap.alloc length initial).2.object? σ object = heap.object? σ object := by
  unfold object?
  rw [getElem?_alloc_of_ne heap length initial different]

/-- In particular, allocation preserves every old object's complete typed contents. -/
theorem object?_alloc_of_lt (heap : Heap) {τ σ : CellTy} (length : Nat)
    (initial : CellValue τ) {object : Nat} (bound : object < heap.objects.size) :
    (heap.alloc length initial).2.object? σ object = heap.object? σ object :=
  heap.object?_alloc_of_ne length initial (Nat.ne_of_lt bound)

/-- The newly returned view denotes precisely the initialized native array. -/
theorem object?_alloc_new (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).2.object? τ (heap.alloc length initial).1.object =
      some (Array.replicate length initial) := by
  apply object?_eq_some_iff.mpr
  exact Array.getElem?_push_size

/-- Allocation extends object shape while preserving the stronger old-content facts above. -/
theorem shapeExtends_alloc (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) : heap.ShapeExtends (heap.alloc length initial).2 := by
  refine ⟨?_, ?_⟩
  · simp only [alloc_size]
    omega
  · intro σ object values found
    exact ⟨values,
      (heap.object?_alloc_of_lt length initial (object_lt_size found)).trans found, rfl⟩

/-- The returned whole-object view has the requested ordinary mathematical contents. -/
theorem alloc_contents (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).1.Contents (heap.alloc length initial).2
      (Array.replicate length initial) := by
  refine ⟨Array.replicate length initial, heap.object?_alloc_new length initial, ?_, ?_⟩
  · simp only [alloc_offset, alloc_length, Nat.zero_add, Array.size_replicate, Nat.le_refl]
  · simpa only [alloc_offset, alloc_length, Nat.zero_add, Array.size_replicate] using
      (Array.extract_size (xs := Array.replicate length initial)).symm

/-- Every newly allocated view is valid, including an empty one. -/
theorem alloc_valid (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).1.Valid (heap.alloc length initial).2 :=
  (heap.alloc_contents length initial).valid

/-- A fresh view is rooted in the extended heap. -/
theorem alloc_rooted (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).1.Rooted (heap.alloc length initial).2 :=
  (heap.alloc_valid length initial).rooted

/-- Its identifier was not present before allocation, even for length zero. -/
theorem alloc_not_rooted (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) : ¬(heap.alloc length initial).1.Rooted heap := by
  simp only [Buffer.Rooted, alloc_object, Nat.lt_irrefl, not_false_eq_true]

/-- Reading any valid index of the new object returns its initialized scalar. -/
theorem read_alloc (heap : Heap) {τ : CellTy} {length index : Nat}
    (initial : CellValue τ) (bound : index < length) :
    (heap.alloc length initial).2.read (heap.alloc length initial).1 index = .ok initial := by
  have loaded := (heap.alloc_contents length initial).read
    (index := index) (by simpa only [Array.size_replicate] using bound)
  simpa only [Array.getElem_replicate] using loaded

/-- Old rooted handles retain every read outcome, not only successful valid accesses. -/
theorem read_alloc_of_rooted (heap : Heap) {τ σ : CellTy} (length : Nat)
    (initial : CellValue τ) {buffer : Buffer σ} (rooted : buffer.Rooted heap) (index : Nat) :
    (heap.alloc length initial).2.read buffer index = heap.read buffer index := by
  simp only [read, object?_alloc_of_lt heap length initial rooted]

end Heap

namespace Buffer

/-- Allocation preserves an old handle's rootedness without a validity or alias premise. -/
theorem Rooted.alloc {heap : Heap} {τ σ : CellTy} {buffer : Buffer σ}
    (rooted : buffer.Rooted heap) (length : Nat) (initial : CellValue τ) :
    buffer.Rooted (heap.alloc length initial).2 :=
  rooted.mono (heap.shapeExtends_alloc length initial)

/-- Old valid views remain valid after a fresh allocation. -/
theorem Valid.alloc {heap : Heap} {τ σ : CellTy} {buffer : Buffer σ}
    (valid : buffer.Valid heap) (length : Nat) (initial : CellValue τ) :
    buffer.Valid (heap.alloc length initial).2 := by
  obtain ⟨values, found, extent⟩ := valid
  exact ⟨values,
    (heap.object?_alloc_of_lt length initial (Heap.object_lt_size found)).trans found, extent⟩

/-- Every old view keeps its exact current contents; old views may overlap each other. -/
theorem Contents.alloc {heap : Heap} {τ σ : CellTy} {buffer : Buffer σ}
    {contents : Array (CellValue σ)} (observed : buffer.Contents heap contents)
    (length : Nat) (initial : CellValue τ) :
    buffer.Contents (heap.alloc length initial).2 contents := by
  obtain ⟨values, found, extent, same⟩ := observed
  exact ⟨values,
    (heap.object?_alloc_of_lt length initial (Heap.object_lt_size found)).trans found,
    extent, same⟩

/-- Fresh identity separates the new view from every old rooted handle. -/
theorem Rooted.disjoint_alloc {heap : Heap} {τ σ : CellTy} {buffer : Buffer σ}
    (rooted : buffer.Rooted heap) (length : Nat) (initial : CellValue τ) :
    (heap.alloc length initial).1.Disjoint buffer :=
  Or.inl (Nat.ne_of_gt rooted)

end Buffer

end Complexity.Language
