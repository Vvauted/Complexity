/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Ordering

/-!
# Standard merge specifications for RAM arrays

`unsignedMerge` is only an abbreviation for the standard `List.merge`, with
unsigned word comparisons and left priority for equal heads. The step lemmas
do not require sorted inputs. Sortedness is used only to derive `SortedPerm`
and equality with the standard sorting functions.

These are mathematical specifications, not uncharged RAM operations.
-/

namespace Ram.Source.Array

/-- Standard merge with the unsigned comparison used by the RAM program. -/
abbrev unsignedMerge (xs ys : List (Word w)) : List (Word w) :=
  List.merge xs ys (fun a b => decide (unsignedLE a b))

attribute [local instance] unsignedLE_total unsignedLE_trans

@[simp] theorem unsignedMerge_nil_left (ys : List (Word w)) :
    unsignedMerge [] ys = ys := List.nil_merge ys

@[simp] theorem unsignedMerge_nil_right (xs : List (Word w)) :
    unsignedMerge xs [] = xs := List.merge_right xs

/-- Equal heads are emitted from the left input first. -/
theorem unsignedMerge_cons_left {a b : Word w} {xs ys : List (Word w)}
    (h : unsignedLE a b) :
    unsignedMerge (a :: xs) (b :: ys) = a :: unsignedMerge xs (b :: ys) := by
  exact List.cons_merge_cons_pos _ _ _ (by simpa using h)

/-- The right head is emitted only when it is strictly smaller. -/
theorem unsignedMerge_cons_right {a b : Word w} {xs ys : List (Word w)}
    (h : b.toNat < a.toNat) :
    unsignedMerge (a :: xs) (b :: ys) = b :: unsignedMerge (a :: xs) ys := by
  exact List.cons_merge_cons_neg _ _ _ (by simpa [unsignedLE] using Nat.not_le_of_gt h)

/-- Emit the left cursor's element. The comparison premise is vacuous when
the right cursor is past the end; no sortedness premise is needed. -/
theorem unsignedMerge_drop_left {xs ys : List (Word w)} {i j : Nat}
    (hi : i < xs.length) (hchoose : ∀ hj : j < ys.length, unsignedLE xs[i] ys[j]) :
    unsignedMerge (xs.drop i) (ys.drop j) =
      xs[i] :: unsignedMerge (xs.drop (i + 1)) (ys.drop j) := by
  by_cases hj : j < ys.length
  · rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
    exact unsignedMerge_cons_left (hchoose hj)
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt hj)]
    simpa only [unsignedMerge_nil_right] using List.drop_eq_getElem_cons hi

/-- Emit the right cursor's element. The left input may already be exhausted. -/
theorem unsignedMerge_drop_right {xs ys : List (Word w)} {i j : Nat}
    (hj : j < ys.length) (hchoose : ∀ hi : i < xs.length, ys[j].toNat < xs[i].toNat) :
    unsignedMerge (xs.drop i) (ys.drop j) =
      ys[j] :: unsignedMerge (xs.drop i) (ys.drop (j + 1)) := by
  by_cases hi : i < xs.length
  · rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
    exact unsignedMerge_cons_right (hchoose hi)
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)]
    simpa only [unsignedMerge_nil_left] using List.drop_eq_getElem_cons hj

@[simp] theorem length_unsignedMerge (xs ys : List (Word w)) :
    (unsignedMerge xs ys).length = xs.length + ys.length :=
  List.length_merge _ xs ys

/-- Standard merge preserves both input multisets, even for unsorted inputs. -/
theorem unsignedMerge_perm (xs ys : List (Word w)) :
    (unsignedMerge xs ys).Perm (xs ++ ys) := List.merge_perm_append _

/-- Sorted inputs give a sorted result by mathlib's existing merge theorem. -/
theorem pairwise_unsignedMerge {xs ys : List (Word w)}
    (hxs : xs.Pairwise unsignedLE) (hys : ys.Pairwise unsignedLE) :
    (unsignedMerge xs ys).Pairwise unsignedLE := hxs.merge hys

namespace SortedPerm

/-- Merge independently verified sorted outputs into a sorted permutation
of the concatenation of their original inputs. -/
theorem merge {xs ys left right : List (Word w)}
    (hleft : SortedPerm xs left) (hright : SortedPerm ys right) :
    SortedPerm (xs ++ ys) (unsignedMerge left right) :=
  ⟨pairwise_unsignedMerge hleft.sorted hright.sorted,
    (unsignedMerge_perm left right).trans (hleft.perm.append hright.perm)⟩

/-- The standard merge sort satisfies the same implementation-independent
sorting specification as insertion sort. -/
theorem mergeSort (xs : List (Word w)) :
    SortedPerm xs (xs.mergeSort (fun a b => decide (unsignedLE a b))) :=
  ⟨List.pairwise_mergeSort' unsignedLE xs, List.mergeSort_perm xs _⟩

/-- A verified sorted permutation also equals standard merge sort. -/
theorem eq_mergeSort {xs output : List (Word w)} (h : SortedPerm xs output) :
    output = xs.mergeSort (fun a b => decide (unsignedLE a b)) :=
  h.unique (mergeSort xs)

end SortedPerm

/-- Merging sorted lists returns the canonical sorting of their concatenation. -/
theorem unsignedMerge_eq_insertionSort {xs ys : List (Word w)}
    (hxs : xs.Pairwise unsignedLE) (hys : ys.Pairwise unsignedLE) :
    unsignedMerge xs ys = (xs ++ ys).insertionSort unsignedLE :=
  ((SortedPerm.refl hxs).merge (SortedPerm.refl hys)).eq_insertionSort

/-- The same merge result agrees with standard merge sort. -/
theorem unsignedMerge_eq_mergeSort {xs ys : List (Word w)}
    (hxs : xs.Pairwise unsignedLE) (hys : ys.Pairwise unsignedLE) :
    unsignedMerge xs ys = (xs ++ ys).mergeSort (fun a b => decide (unsignedLE a b)) :=
  ((SortedPerm.refl hxs).merge (SortedPerm.refl hys)).eq_mergeSort

end Ram.Source.Array
