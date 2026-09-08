/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Ordering

/-!
# Canonical specifications for recursive RAM merge sort

The canonical result is the existing `List.insertionSort`. The split equation
follows from sorted-permutation uniqueness, rather than another recursive
sorting definition or proof of a sorting algorithm.
-/

namespace Ram.Source.Array.MergeSort

/-- The standard mathematical sorted result, not a RAM operation. -/
abbrev sorted (xs : List (Word w)) : List (Word w) := xs.insertionSort unsignedLE

/-- Canonical sorting satisfies the shared sorted-permutation specification. -/
theorem sorted_spec (xs : List (Word w)) : SortedPerm xs (sorted xs) :=
  SortedPerm.insertionSort xs

@[simp] theorem length_sorted (xs : List (Word w)) : (sorted xs).length = xs.length :=
  (sorted_spec xs).length_eq

/-- The recursive program's empty and singleton base cases need no stores. -/
theorem sorted_eq_self_of_length_le_one {xs : List (Word w)} (h : xs.length ≤ 1) :
    sorted xs = xs := by
  have hs : xs.Pairwise unsignedLE := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    omega
  exact (SortedPerm.refl hs).eq_insertionSort.symm

/-- Sorting each half retains the original multiset before the merge call.
This holds for every split index, including indices beyond the list's end. -/
theorem sorted_split_perm (xs : List (Word w)) (p : Nat) :
    (sorted (xs.take p) ++ sorted (xs.drop p)).Perm xs := by
  simpa only [List.take_append_drop] using
    ((sorted_spec (xs.take p)).perm.append (sorted_spec (xs.drop p)).perm)

/-- Independently sorting the two halves and merging them gives the canonical
result. No pure recursive sorting algorithm is introduced by this equation. -/
theorem merge_sorted_split (xs : List (Word w)) (p : Nat) :
    unsignedMerge (sorted (xs.take p)) (sorted (xs.drop p)) = sorted xs := by
  have h := (sorted_spec (xs.take p)).merge (sorted_spec (xs.drop p))
  rw [List.take_append_drop] at h
  exact h.eq_insertionSort

end Ram.Source.Array.MergeSort
