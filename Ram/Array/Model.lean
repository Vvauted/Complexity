/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Contents
import Mathlib.Data.Vector.Basic

/-!
# Ordinary list models of RAM arrays

`arrayContents` observes a finite memory interval as the ordinary Lean `List`.
It is ghost data, not an allocation or a machine operation. `ArrayRep.contents_eq`
turns an existing representation assertion into a list equality, so functional
specifications and mathlib list properties can be used by rewriting. The store
law is inherited from the existing single-word RAM update theorem.

The actual equivalence is mathlib's `Equiv.vectorEquivFin`: fixed-length lists
and finite functions have the same information. An entire heap is not in
bijection with one list, since memory outside the interval is unobserved.
-/

namespace Ram

/-- The mathematical contents of a memory interval. A non-wrapping bound is
required by `ArrayRep`, not to form this finite ghost observation. -/
def arrayContents (mem : Word w → Word w) (base : Word w) (length : Nat) :
    List (Word w) :=
  List.ofFn fun i : Fin length => mem (arrayAddr base i.val)

@[simp]
theorem length_arrayContents (mem : Word w → Word w) (base : Word w) (length : Nat) :
    (arrayContents mem base length).length = length := List.length_ofFn

@[simp]
theorem getElem_arrayContents {mem : Word w → Word w} {base : Word w} {length i : Nat}
    (hi : i < (arrayContents mem base length).length) :
    (arrayContents mem base length)[i] = mem (arrayAddr base i) := by
  simp only [arrayContents, List.getElem_ofFn]

/-- Only the observed cells matter; no equality of complete heaps is needed. -/
theorem arrayContents_congr {before after : Word w → Word w} {base : Word w}
    {length : Nat}
    (h : ∀ i, i < length → before (arrayAddr base i) = after (arrayAddr base i)) :
    arrayContents before base length = arrayContents after base length := by
  apply List.ext_getElem (by simp)
  intro i hi _
  simpa only [getElem_arrayContents] using h i (by simpa using hi)

/-- Mathlib's existing equivalence identifies the finite view with its
fixed-length list, without inventing a new representation type. -/
theorem arrayContents_vectorEquivFin (mem : Word w → Word w) (base : Word w)
    (length : Nat) :
    (Equiv.vectorEquivFin (Word w) length).symm
        (fun i : Fin length => mem (arrayAddr base i.val)) =
      (⟨arrayContents mem base length, length_arrayContents mem base length⟩ :
        List.Vector (Word w) length) := by
  apply Subtype.ext
  change (List.Vector.ofFn (fun i : Fin length => mem (arrayAddr base i.val))).toList = _
  exact List.Vector.toList_ofFn _

namespace ArrayRep

/-- A represented list is exactly the ordinary list observed in memory. -/
theorem contents_eq {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) : arrayContents mem base xs.length = xs := by
  apply List.ext_getElem (by simp)
  intro i _ hi
  exact (getElem_arrayContents _).trans (h.lookup i hi)

/-- Recover the existing representation assertion from a list-view equation.
The explicit bound remains the real machine's no-wrap requirement. -/
theorem of_contents_eq {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hfit : base.toNat + xs.length ≤ 2 ^ w)
    (h : arrayContents mem base xs.length = xs) : ArrayRep mem base xs := by
  have represented : ArrayRep mem base (arrayContents mem base xs.length) := ofFn hfit
  exact h ▸ represented

theorem iff_contents_eq {mem : Word w → Word w} {base : Word w} {xs : List (Word w)} :
    ArrayRep mem base xs ↔
      base.toNat + xs.length ≤ 2 ^ w ∧ arrayContents mem base xs.length = xs :=
  ⟨fun h => ⟨h.fits, h.contents_eq⟩, fun h => of_contents_eq h.1 h.2⟩

/-- At a fixed extent the logical contents are unique. The length premise
cannot be dropped: the same memory also represents every fitting prefix. -/
theorem eq_of_length_eq {mem : Word w → Word w} {base : Word w}
    {xs ys : List (Word w)} (hx : ArrayRep mem base xs) (hy : ArrayRep mem base ys)
    (hlen : xs.length = ys.length) : xs = ys := by
  rw [← hx.contents_eq, hlen, hy.contents_eq]

/-- Any ordinary list predicate transfers without another elementwise proof.
This includes mathlib predicates such as permutation, sortedness and `Nodup`. -/
theorem predicate_iff {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) (P : List (Word w) → Prop) :
    P (arrayContents mem base xs.length) ↔ P xs := by
  rw [h.contents_eq]

/-- Relational functional specifications transfer at both actual endpoints.
The two represented intervals may have different lengths or base addresses. -/
theorem relation_iff {before after : Word w → Word w} {base other : Word w}
    {xs ys : List (Word w)} (hx : ArrayRep before base xs) (hy : ArrayRep after other ys)
    (R : List (Word w) → List (Word w) → Prop) :
    R (arrayContents before base xs.length) (arrayContents after other ys.length) ↔
      R xs ys := by
  rw [hx.contents_eq, hy.contents_eq]

end ArrayRep

/-- The actual one-word memory update is ordinary `List.set` on the model.
This is a representation theorem, not an extra executable array primitive. -/
theorem arrayContents_store {mem : Word w → Word w} {base : Word w} {length i : Nat}
    (hfit : base.toNat + length ≤ 2 ^ w) (hi : i < length) (value : Word w) :
    arrayContents (fun address => if address = arrayAddr base i then value else mem address)
        base length = (arrayContents mem base length).set i value := by
  have represented : ArrayRep mem base (arrayContents mem base length) := ArrayRep.ofFn hfit
  have updated := represented.store (by simpa using hi) value
  simpa only [List.length_set, length_arrayContents] using updated.contents_eq

namespace Source.ArrayAt

/-- Heap-array assertions expose the same ordinary list model directly. -/
theorem contents_eq {heapLimit : Nat} {base : Word w} {xs : List (Word w)} {s : State w}
    (h : ArrayAt heapLimit base xs s) : arrayContents s.mem base xs.length = xs :=
  h.1.contents_eq

/-- Source stores and target stores share this one-word update, hence the
same standard `List.set` model equation. -/
theorem contents_setMem {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {i : Nat} (hi : i < xs.length)
    (value : Word w) :
    arrayContents (s.setMem (arrayAddr base i) value).mem base xs.length = xs.set i value := by
  simpa only [List.length_set] using (h.setMem hi value).contents_eq

end Source.ArrayAt
end Ram
