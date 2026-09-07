/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.List.Sort
import Ram.Array.Search

/-!
# Standard sorting specifications for RAM arrays

`SortedPerm input output` combines standard `List.Pairwise` unsigned ordering
and `List.Perm`. Its canonical result is mathlib's `List.insertionSort`.
The insertion bridge connects a verified lower-bound index and the array
shift operation's `take`/`drop` result to standard `List.orderedInsert`.

These declarations are mathematical specifications and library bridges, not
new sorting algorithms or uncharged operations available to a RAM program.
-/

namespace Ram.Source.Array

/-- Unsigned word order used by the machine's comparisons. -/
abbrev unsignedLE (a b : Word w) : Prop := a.toNat ≤ b.toNat

local instance unsignedLE_total : Std.Total (@unsignedLE w) :=
  ⟨fun _ _ => Nat.le_total _ _⟩

local instance unsignedLE_trans : IsTrans (Word w) unsignedLE :=
  ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩

/-- Inserting at the verified lower-bound index is mathlib's `orderedInsert`.
No separate recursive insertion function or sortedness assumption is needed. -/
theorem LowerBoundSpec.insert_eq_orderedInsert {xs : List (Word w)} {key : Word w}
    {p : Nat} (h : LowerBoundSpec xs key p) :
    xs.take p ++ key :: xs.drop p = xs.orderedInsert unsignedLE key := by
  rw [h.eq_findIdx, List.orderedInsert_eq_take_drop,
    List.takeWhile_eq_take_findIdx_not, List.dropWhile_eq_drop_findIdx_not]
  simp only [unsignedLE, decide_not, Bool.not_not]

/-- The standard insertion permutation applies directly to a shifted RAM array. -/
theorem LowerBoundSpec.insert_perm {xs : List (Word w)} {key : Word w}
    {p : Nat} (h : LowerBoundSpec xs key p) :
    (xs.take p ++ key :: xs.drop p).Perm (key :: xs) := by
  rw [h.insert_eq_orderedInsert]
  exact List.perm_orderedInsert unsignedLE key xs

/-- The verified insertion index preserves sortedness by the standard theorem. -/
theorem LowerBoundSpec.insert_pairwise {xs : List (Word w)} {key : Word w}
    {p : Nat} (h : LowerBoundSpec xs key p) (hsorted : xs.Pairwise unsignedLE) :
    (xs.take p ++ key :: xs.drop p).Pairwise unsignedLE := by
  rw [h.insert_eq_orderedInsert]
  exact hsorted.orderedInsert key xs

/-- A sorted output with exactly the original multiset of words. -/
structure SortedPerm (input output : List (Word w)) : Prop where
  sorted : output.Pairwise unsignedLE
  perm : output.Perm input

namespace SortedPerm

variable {input output other : List (Word w)}

/-- An already sorted list satisfies its own sorting specification. -/
theorem refl (hsorted : input.Pairwise unsignedLE) : SortedPerm input input :=
  ⟨hsorted, List.Perm.refl _⟩

/-- Sorting preserves the array length. -/
theorem length_eq (h : SortedPerm input output) : output.length = input.length :=
  h.perm.length_eq

/-- Sorted permutations of the same word list are equal, including duplicates. -/
theorem unique (h : SortedPerm input output) (h' : SortedPerm input other) : output = other :=
  List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => BitVec.eq_of_toNat_eq (Nat.le_antisymm hab hba))
    h.sorted h'.sorted (h.perm.trans h'.perm.symm)

/-- Mathlib's sorting function satisfies the specification. -/
theorem insertionSort (input : List (Word w)) :
    SortedPerm input (input.insertionSort unsignedLE) :=
  ⟨List.pairwise_insertionSort unsignedLE input, List.perm_insertionSort unsignedLE input⟩

/-- Any verified sorting implementation returns the standard mathematical result. -/
theorem eq_insertionSort (h : SortedPerm input output) :
    output = input.insertionSort unsignedLE := h.unique (insertionSort input)

/-- Reuse standard insertion correctness while extending the input multiset. -/
theorem orderedInsert (h : SortedPerm input output) (key : Word w) :
    SortedPerm (key :: input) (output.orderedInsert unsignedLE key) :=
  ⟨h.sorted.orderedInsert key output,
    (List.perm_orderedInsert unsignedLE key output).trans (h.perm.cons key)⟩

/-- The append orientation matches a left-to-right growing sorted prefix. -/
theorem orderedInsert_append (h : SortedPerm input output) (key : Word w) :
    SortedPerm (input ++ [key]) (output.orderedInsert unsignedLE key) := by
  have hi := h.orderedInsert key
  refine ⟨hi.sorted, hi.perm.trans ?_⟩
  simpa only [List.singleton_append] using
    (List.perm_append_comm (l₁ := [key]) (l₂ := input))

/-- A lower-bound search followed by the specified shift extends a sorted permutation. -/
theorem insert (h : SortedPerm input output) {key : Word w} {p : Nat}
    (hp : LowerBoundSpec output key p) :
    SortedPerm (key :: input) (output.take p ++ key :: output.drop p) := by
  rw [hp.insert_eq_orderedInsert]
  exact h.orderedInsert key

/-- Prefix extension after inserting the next original element. -/
theorem insert_append (h : SortedPerm input output) {key : Word w} {p : Nat}
    (hp : LowerBoundSpec output key p) :
    SortedPerm (input ++ [key]) (output.take p ++ key :: output.drop p) := by
  rw [hp.insert_eq_orderedInsert]
  exact h.orderedInsert_append key

/-- Extend the first `i` original elements to the first `i + 1` elements. -/
theorem insert_prefix {xs output : List (Word w)} {i p : Nat} (hi : i < xs.length)
    (h : SortedPerm (xs.take i) output) (hp : LowerBoundSpec output xs[i] p) :
    SortedPerm (xs.take (i + 1)) (output.take p ++ xs[i] :: output.drop p) := by
  rw [List.take_succ_eq_append_getElem hi]
  exact h.insert_append hp

end SortedPerm

/-- Standard insertion into a standard sorted list equals sorting the extended
input. Uniqueness bridges the two directions of processing the list. -/
theorem orderedInsert_insertionSort_eq (xs : List (Word w)) (key : Word w) :
    (xs.insertionSort unsignedLE).orderedInsert unsignedLE key =
      (xs ++ [key]).insertionSort unsignedLE :=
  ((SortedPerm.insertionSort xs).orderedInsert_append key).eq_insertionSort

/-- The canonical sorted-prefix invariant advances by one original element. -/
theorem orderedInsert_insertionSort_take_succ {xs : List (Word w)} {i : Nat}
    (hi : i < xs.length) :
    ((xs.take i).insertionSort unsignedLE).orderedInsert unsignedLE xs[i] =
      (xs.take (i + 1)).insertionSort unsignedLE := by
  rw [orderedInsert_insertionSort_eq, List.take_succ_eq_append_getElem hi]

end Ram.Source.Array
