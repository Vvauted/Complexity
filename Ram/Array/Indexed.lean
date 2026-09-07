/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Model
import Ram.Memory.Indexed
import Init.Data.List.ToArray

/-!
# Finite-function, Array and Vector views of RAM arrays

Contiguous RAM arrays can be reasoned about using ordinary finite functions,
Lean's `Array`, or mathlib's `List.Vector`. These are different mathematical
views of the existing representation, not additional runtime objects. In
particular, storing a word corresponds to the existing `Array.set` operation.

Address injectivity is derived once from the interval's no-wrap bound. The
generic indexed model then supplies function update, reindexing, and transfer
to the actual machine without repeating address arithmetic in client proofs.
-/

namespace Ram

/-- A fitting contiguous interval gives an injective finite address layout. -/
theorem arrayAddr_injective {base : Word w} {length : Nat}
    (hfit : base.toNat + length ≤ 2 ^ w) :
    Function.Injective (fun i : Fin length => arrayAddr base i.val) := by
  intro i j hij
  apply Fin.ext
  exact (arrayAddr_eq_iff (by have := i.isLt; omega)
    (by have := j.isLt; omega)).mp hij

namespace ArrayRep

/-- Standard list indexing exposes the finite-function model directly. -/
theorem indexed {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) :
    IndexedRep mem (fun i : Fin xs.length => arrayAddr base i.val) xs.get := by
  intro i
  exact h.lookup i.val i.isLt

theorem addr_injective {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) :
    Function.Injective (fun i : Fin xs.length => arrayAddr base i.val) :=
  arrayAddr_injective h.fits

/-- A list assertion is precisely its finite model together with the actual
machine's non-wrapping interval bound. -/
theorem iff_indexed {mem : Word w → Word w} {base : Word w} {xs : List (Word w)} :
    ArrayRep mem base xs ↔ base.toNat + xs.length ≤ 2 ^ w ∧
      IndexedRep mem (fun i : Fin xs.length => arrayAddr base i.val) xs.get := by
  refine ⟨fun h => ⟨h.fits, h.indexed⟩, ?_⟩
  rintro ⟨hfit, h⟩
  exact ⟨hfit, fun i hi => h ⟨i, hi⟩⟩

/-- Any finite function can be presented as its standard `List.ofFn`.
The statement does not allocate or copy the mathematical list at runtime. -/
theorem ofFn_iff_indexed {mem : Word w → Word w} {base : Word w} {length : Nat}
    {values : Fin length → Word w} :
    ArrayRep mem base (List.ofFn values) ↔ base.toNat + length ≤ 2 ^ w ∧
      IndexedRep mem (fun i : Fin length => arrayAddr base i.val) values := by
  constructor
  · intro h
    refine ⟨by simpa using h.fits, ?_⟩
    intro i
    exact (h.lookup i.val (by simp)).trans (List.getElem_ofFn _)
  · rintro ⟨hfit, h⟩
    refine ⟨by simpa using hfit, ?_⟩
    intro i hi
    simpa only [List.getElem_ofFn] using h ⟨i, by simpa using hi⟩

/-- Lean's existing `Array` is also a finite-function view of the same cells. -/
theorem toArray_indexed {mem : Word w → Word w} {base : Word w}
    {xs : Array (Word w)} (h : ArrayRep mem base xs.toList) :
    IndexedRep mem (fun i : Fin xs.size => arrayAddr base i.val)
      (fun i => xs[i.val]) := by
  intro i
  simpa only [Array.getElem_toList] using
    h.lookup i.val (by simp)

/-- An ordinary array equality transfers every existing array property. -/
theorem toArray_contents_eq {mem : Word w → Word w} {base : Word w}
    {xs : Array (Word w)} (h : ArrayRep mem base xs.toList) :
    (arrayContents mem base xs.size).toArray = xs := by
  simpa using congrArg List.toArray h.contents_eq

/-- The actual RAM store has the existing `Array.set` semantics, not a
library-specific replacement for the ordinary Lean update operation. -/
theorem store_toArray {mem : Word w → Word w} {base : Word w}
    {xs : Array (Word w)} (h : ArrayRep mem base xs.toList)
    {i : Nat} (hi : i < xs.size) (value : Word w) :
    ArrayRep (fun a => if a = arrayAddr base i then value else mem a)
      base (xs.set i value).toList := by
  simpa only [Array.toList_set] using h.store (by simpa using hi) value

/-- Mathlib's existing fixed-length lists use exactly the same finite view. -/
theorem vector_indexed {mem : Word w → Word w} {base : Word w} {length : Nat}
    {xs : List.Vector (Word w) length} (h : ArrayRep mem base xs.toList) :
    IndexedRep mem (fun i : Fin length => arrayAddr base i.val) xs.get := by
  intro i
  simpa only [List.Vector.get_eq_get_toList, List.get_eq_getElem] using
    h.lookup i.val (by simp)

theorem vector_contents_eq {mem : Word w → Word w} {base : Word w} {length : Nat}
    {xs : List.Vector (Word w) length} (h : ArrayRep mem base xs.toList) :
    (⟨arrayContents mem base length, length_arrayContents mem base length⟩ :
      List.Vector (Word w) length) = xs := by
  apply Subtype.ext
  simpa using h.contents_eq

end ArrayRep

namespace Source.ArrayAt

/-- Existing source-array assertions include the generic finite heap view. -/
theorem indexed {heapLimit : Nat} {base : Word w} {xs : List (Word w)} {s : State w}
    (h : ArrayAt heapLimit base xs s) :
    IndexedAt heapLimit (fun i : Fin xs.length => arrayAddr base i.val) xs.get s :=
  ⟨h.1.indexed, fun i => h.addr_lt i.isLt⟩

theorem toArray_contents_eq {heapLimit : Nat} {base : Word w}
    {xs : Array (Word w)} {s : State w} (h : ArrayAt heapLimit base xs.toList s) :
    (arrayContents s.mem base xs.size).toArray = xs := h.1.toArray_contents_eq

/-- A source store retains the heap assertion with standard Lean `Array.set`.
Its existing total and measured contracts can use this result unchanged. -/
theorem setMem_toArray {heapLimit : Nat} {base : Word w} {xs : Array (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs.toList s) {i : Nat}
    (hi : i < xs.size) (value : Word w) :
    ArrayAt heapLimit base (xs.set i value).toList (s.setMem (arrayAddr base i) value) := by
  simpa only [Array.toList_set] using h.setMem (by simpa using hi) value

end Source.ArrayAt
end Ram
