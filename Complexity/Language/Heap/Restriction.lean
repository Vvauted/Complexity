/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Prefix

/-!
# Restricting the current heap to retained object identifiers

`Heap.take` discards an object suffix from the current heap. It does not restore
an earlier heap snapshot: retained objects keep their current values, including
updates performed since entering a scope. The operation itself does not claim
that handles to discarded objects cannot escape.

Rootedness, validity and mathematical contents transport for identifiers below
the retained count. Restricting a shape extension to its original object count
therefore preserves the original shape while retaining the current contents.
-/

namespace Complexity.Language

namespace Heap

/-- Keep the current first `count` objects, discarding only the remaining suffix. -/
def take (heap : Heap) (count : Nat) : Heap :=
  ⟨heap.objects.extract 0 count⟩

@[simp] theorem take_objects (heap : Heap) (count : Nat) :
    (heap.take count).objects = heap.objects.extract 0 count := rfl

/-- A requested count beyond the current domain retains the whole heap. -/
@[simp] theorem take_size (heap : Heap) (count : Nat) :
    (heap.take count).objects.size = min count heap.objects.size := by
  simp only [take_objects, Array.size_extract, Nat.sub_zero]

/-- Native lookup at a retained identifier has its exact current outcome. -/
theorem getElem?_take_of_lt (heap : Heap) (count : Nat) {object : Nat}
    (bound : object < count) :
    (heap.take count).objects[object]? = heap.objects[object]? := by
  simp only [take_objects, Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
  split
  · rfl
  · exact (Array.getElem?_eq_none (by omega)).symm

/-- Retained identifiers preserve exact typed lookup, including type mismatch
and absence. Existing objects retain their current arrays rather than old values. -/
theorem object?_take_of_lt (heap : Heap) (count : Nat) {τ : CellTy} {object : Nat}
    (bound : object < count) :
    (heap.take count).object? τ object = heap.object? τ object := by
  simp only [object?, getElem?_take_of_lt heap count bound]

/-- A present typed object survives whenever its identifier is retained. -/
theorem object?_take_eq_some {heap : Heap} {count object : Nat} {τ : CellTy}
    {values : Array (CellValue τ)} (found : heap.object? τ object = some values)
    (bound : object < count) :
    (heap.take count).object? τ object = some values :=
  (heap.object?_take_of_lt count bound).trans found

/-- Restriction retains an old node's exact current payload and tail lookup.
Preservation of objects reached through that tail is a separate lifecycle fact. -/
theorem node?_take_of_lt (heap : Heap) (count : Nat) {τ : CellTy} {object : Nat}
    (bound : object < count) :
    (heap.take count).node? τ object = heap.node? τ object := by
  simp only [node?, getElem?_take_of_lt heap count bound]

/-- A present immutable node survives whenever its identifier is retained. -/
theorem node?_take_eq_some {heap : Heap} {count object : Nat} {τ : CellTy}
    {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) (bound : object < count) :
    (heap.take count).node? τ object = some (head, tail) :=
  (heap.node?_take_of_lt count bound).trans found

/-- Restricting an exact object-prefix extension removes precisely its appended
objects. Unlike shape extension alone, this premise excludes changes to old values. -/
theorem take_eq_of_prefix {initial finish : Heap}
    (extension : List.IsPrefix initial.objects.toList finish.objects.toList) :
    finish.take initial.objects.size = initial := by
  change Heap.mk (finish.objects.extract 0 initial.objects.size) = Heap.mk initial.objects
  apply congrArg Heap.mk
  apply Array.toList_inj.mp
  simpa only [Array.toList_extract, List.extract_eq_drop_take, List.drop_zero,
    Nat.sub_zero, Array.length_toList] using (List.prefix_iff_eq_take.mp extension).symm

/-- Retaining every current object leaves the heap unchanged. -/
@[simp] theorem take_self (heap : Heap) : heap.take heap.objects.size = heap :=
  take_eq_of_prefix (List.prefix_refl _)

/-- Restricting an allocation to its original object count removes its fresh object. -/
@[simp] theorem take_alloc_self (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    (heap.alloc length initial).2.take heap.objects.size = heap :=
  take_eq_of_prefix (heap.objects_prefix_alloc length initial)

/-- A current typed object at an old identifier has an original object of the
same type and extent. Its contents may differ after intervening writes. -/
theorem ShapeExtends.objects_of_lt {initial finish : Heap} {τ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} (growth : initial.ShapeExtends finish)
    (bound : object < initial.objects.size)
    (found : finish.object? τ object = some values) :
    ∃ oldValues, initial.object? τ object = some oldValues ∧ values.size = oldValues.size := by
  cases stored : initial.objects[object] with
  | buffer kind oldValues =>
      have oldFound : initial.object? kind object = some oldValues := by
        apply object?_eq_some_iff.mpr
        simp only [Array.getElem?_eq_getElem bound, stored]
      obtain ⟨currentValues, currentFound, sameSize⟩ := growth.objects oldFound
      have sameStored : HeapObject.buffer kind currentValues = .buffer τ values := by
        apply Option.some.inj
        exact (object?_eq_some_iff.mp currentFound).symm.trans (object?_eq_some_iff.mp found)
      have sameType : kind = τ := congrArg HeapObject.kind sameStored
      subst kind
      have sameValues : currentValues = values := Option.some.inj (currentFound.symm.trans found)
      subst currentValues
      exact ⟨oldValues, oldFound, sameSize⟩
  | node kind head tail =>
      have oldFound : initial.node? kind object = some (head, tail) := by
        apply node?_eq_some_iff.mpr
        simp only [Array.getElem?_eq_getElem bound, stored]
      have impossible := object?_eq_none_of_node (σ := τ) (growth.nodes oldFound)
      rw [found] at impossible
      cases impossible

/-- A node observed at an old identifier is the exact original immutable node.
An existing scalar array cannot become a node during shape extension. -/
theorem ShapeExtends.nodes_of_lt {initial finish : Heap} {τ : CellTy} {object : Nat}
    {head : CellValue τ} {tail : Option (NodeRef τ)}
    (growth : initial.ShapeExtends finish) (bound : object < initial.objects.size)
    (found : finish.node? τ object = some (head, tail)) :
    initial.node? τ object = some (head, tail) := by
  cases stored : initial.objects[object] with
  | buffer kind oldValues =>
      have oldFound : initial.object? kind object = some oldValues := by
        apply object?_eq_some_iff.mpr
        simp only [Array.getElem?_eq_getElem bound, stored]
      obtain ⟨currentValues, currentFound, _⟩ := growth.objects oldFound
      have impossible := node?_eq_none_of_object (σ := τ) currentFound
      rw [found] at impossible
      cases impossible
  | node kind oldHead oldTail =>
      have oldFound : initial.node? kind object = some (oldHead, oldTail) := by
        apply node?_eq_some_iff.mpr
        simp only [Array.getElem?_eq_getElem bound, stored]
      have currentFound := growth.nodes oldFound
      have sameStored : HeapObject.node kind oldHead oldTail = .node τ head tail := by
        apply Option.some.inj
        exact (node?_eq_some_iff.mp currentFound).symm.trans (node?_eq_some_iff.mp found)
      have sameType : kind = τ := congrArg HeapObject.kind sameStored
      subst kind
      have sameValues : (oldHead, oldTail) = (head, tail) :=
        Option.some.inj (currentFound.symm.trans found)
      exact oldFound.trans (congrArg some sameValues)

/-- Discarding a shape extension's fresh suffix retains the original shape.
The surviving arrays are taken from `finish`, so their intervening writes remain. -/
theorem ShapeExtends.take {initial finish : Heap} (growth : initial.ShapeExtends finish) :
    initial.ShapeExtends (finish.take initial.objects.size) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [take_size, Nat.min_eq_left growth.size_le] using
      Nat.le_refl initial.objects.size
  · intro τ object values found
    obtain ⟨currentValues, currentFound, sameSize⟩ := growth.objects found
    exact ⟨currentValues, object?_take_eq_some currentFound (object_lt_size found), sameSize⟩
  · intro τ object head tail found
    exact node?_take_eq_some (growth.nodes found) (node_lt_size found)

end Heap

namespace Buffer

/-- An existing handle remains rooted if its identifier is below the cut. -/
theorem Rooted.take {τ : CellTy} {buffer : Buffer τ} {heap : Heap} {count : Nat}
    (rooted : buffer.Rooted heap) (bound : buffer.object < count) :
    buffer.Rooted (heap.take count) := by
  change buffer.object < heap.objects.size at rooted
  change buffer.object < (heap.take count).objects.size
  rw [Heap.take_size]
  omega

/-- Restriction does not change the type or extent of a retained valid view. -/
theorem Valid.take {τ : CellTy} {buffer : Buffer τ} {heap : Heap} {count : Nat}
    (valid : buffer.Valid heap) (bound : buffer.object < count) :
    buffer.Valid (heap.take count) := by
  obtain ⟨values, found, extent⟩ := valid
  exact ⟨values, Heap.object?_take_eq_some found bound, extent⟩

/-- A retained view keeps its current mathematical contents, including writes
made before restriction. No disjointness between retained views is required. -/
theorem Contents.take {τ : CellTy} {buffer : Buffer τ} {heap : Heap} {count : Nat}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents)
    (bound : buffer.object < count) :
    buffer.Contents (heap.take count) contents := by
  obtain ⟨values, found, extent, same⟩ := observed
  exact ⟨values, Heap.object?_take_eq_some found bound, extent, same⟩

end Buffer
end Complexity.Language
