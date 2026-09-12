/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Allocation
import Init.Data.List.Sublist

/-!
# Exact object preservation through heap prefixes

The standard `List.IsPrefix` relation on the native object arrays retains every
old object's full value, not only its type and extent. Allocation appends one
initialized object, so it establishes this prefix even for length zero.

Typed object lookup and borrowed contents transport along the same prefix.
These are mathematical frame facts, not a new heap operation or execution
semantics, and they impose no separation condition on overlapping old views.
-/

namespace Complexity.Language

namespace Heap

/-- Allocation appends its initialized object without changing any old object. -/
theorem objects_prefix_alloc (heap : Heap) {τ : CellTy} (length : Nat)
    (initial : CellValue τ) :
    List.IsPrefix heap.objects.toList (heap.alloc length initial).2.objects.toList := by
  simpa only [alloc_objects, Array.toList_push] using
    (List.prefix_append heap.objects.toList [.buffer τ (Array.replicate length initial)])

/-- A native object-array prefix preserves the exact typed lookup at every
old identifier, including a failed lookup caused by a different stored type. -/
theorem object?_eq_of_prefix {initial finish : Heap} {τ : CellTy} {object : Nat}
    (extension : List.IsPrefix initial.objects.toList finish.objects.toList)
    (bound : object < initial.objects.size) :
    finish.object? τ object = initial.object? τ object := by
  obtain ⟨suffix, appended⟩ := extension
  have lookup : finish.objects.toList[object]? = initial.objects.toList[object]? := by
    rw [← appended, List.getElem?_append_left (l₁ := initial.objects.toList) (by
      simpa only [Array.length_toList] using bound)]
  have same : finish.objects[object]? = initial.objects[object]? := by
    simpa only [Array.getElem?_toList] using lookup
  simp only [object?, same]

/-- An exact object prefix also preserves node lookup, including an absent
node or a stored object with a different kind. -/
theorem node?_eq_of_prefix {initial finish : Heap} {τ : CellTy} {object : Nat}
    (extension : List.IsPrefix initial.objects.toList finish.objects.toList)
    (bound : object < initial.objects.size) :
    finish.node? τ object = initial.node? τ object := by
  obtain ⟨suffix, appended⟩ := extension
  have lookup : finish.objects.toList[object]? = initial.objects.toList[object]? := by
    rw [← appended, List.getElem?_append_left (l₁ := initial.objects.toList) (by
      simpa only [Array.length_toList] using bound)]
  have same : finish.objects[object]? = initial.objects[object]? := by
    simpa only [Array.getElem?_toList] using lookup
  simp only [node?, same]

end Heap

namespace Buffer

/-- Exact object-prefix preservation retains the current mathematical contents
of every old borrowed view, without requiring different views to be disjoint. -/
theorem Contents.mono_prefix {τ : CellTy} {buffer : Buffer τ}
    {initial finish : Heap} {contents : Array (CellValue τ)}
    (observed : buffer.Contents initial contents)
    (extension : List.IsPrefix initial.objects.toList finish.objects.toList) :
    buffer.Contents finish contents := by
  obtain ⟨values, found, extent, same⟩ := observed
  exact ⟨values,
    (Heap.object?_eq_of_prefix extension (Heap.object_lt_size found)).trans found, extent, same⟩

end Buffer

end Complexity.Language
