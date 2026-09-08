/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Multiset
import Mathlib.Data.Finset.Card

/-!
# Finite-set specifications of RAM arrays

Use the ordinary `List.toFinset` observation for set-valued specifications and
its standard coercion to `Set` for set-theoretic reasoning. This model forgets
both order and multiplicity. Cardinality equals the number of cells exactly
when the represented list has no duplicates; a store erases the old value from
the finite set only when its overwritten occurrence was the last one.
-/

namespace Ram

/-- Set membership is existence of an actual cell in the observed interval. -/
theorem mem_toFinset_arrayContents {mem : Word w → Word w} {base : Word w}
    {length : Nat} {value : Word w} :
    value ∈ (arrayContents mem base length).toFinset ↔
      ∃ i : Fin length, mem (arrayAddr base i.val) = value := by
  simp only [List.mem_toFinset, arrayContents, List.mem_ofFn]

/-- The finite-set view is also mathlib's ordinary range of the bounded
memory lookup function. No bespoke set representation is required. -/
theorem coe_toFinset_arrayContents (mem : Word w → Word w) (base : Word w)
    (length : Nat) :
    ((arrayContents mem base length).toFinset : Set (Word w)) =
      Set.range (fun i : Fin length => mem (arrayAddr base i.val)) := by
  ext value
  exact mem_toFinset_arrayContents

/-- Distinct values can never outnumber the observed cells. -/
theorem card_toFinset_arrayContents_le (mem : Word w → Word w) (base : Word w)
    (length : Nat) : (arrayContents mem base length).toFinset.card ≤ length := by
  simpa only [length_arrayContents] using
    (arrayContents mem base length).toFinset_card_le

namespace ArrayRep

/-- Rewrite directly into a mathlib finite-set specification. -/
theorem toFinset_eq {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) :
    (arrayContents mem base xs.length).toFinset = xs.toFinset := by
  rw [h.contents_eq]

/-- Finite-set preservation requires the same members, not a permutation.
Lists with different lengths or duplicate counts may satisfy this property. -/
theorem toFinset_eq_iff {before after : Word w → Word w} {base other : Word w}
    {xs ys : List (Word w)} (hx : ArrayRep before base xs) (hy : ArrayRep after other ys) :
    (arrayContents before base xs.length).toFinset =
        (arrayContents after other ys.length).toFinset ↔
      ∀ value, value ∈ xs ↔ value ∈ ys := by
  rw [hx.toFinset_eq, hy.toFinset_eq]
  simp only [Finset.ext_iff, List.mem_toFinset]

/-- Exact equality between distinct-value count and cell count is equivalent
to the existing `List.Nodup` property, rather than an implicit assumption. -/
theorem card_toFinset_eq_length_iff {mem : Word w → Word w} {base : Word w}
    {xs : List (Word w)} (h : ArrayRep mem base xs) :
    (arrayContents mem base xs.length).toFinset.card = xs.length ↔ xs.Nodup := by
  rw [h.toFinset_eq]
  exact Multiset.toFinset_card_eq_card_iff_nodup

end ArrayRep

private theorem toFinset_erase_eq {α : Type*} [DecidableEq α]
    (s : Multiset α) (value : α) :
    (s.erase value).toFinset =
      if s.count value = 1 then s.toFinset.erase value else s.toFinset := by
  ext query
  by_cases same : query = value
  · subst query
    by_cases one : s.count value = 1
    · simp [one, ← Multiset.count_pos]
    · simp only [one, ↓reduceIte, Multiset.mem_toFinset, ← Multiset.count_pos,
        Multiset.count_erase_self]
      omega
  · by_cases one : s.count value = 1 <;>
      simp [one, same, Multiset.mem_erase_of_ne same]

/-- Exact finite-set effect of the real store. Replacing one of several
copies retains the old value in the support; only its last copy is erased. -/
theorem toFinset_arrayContents_store {mem : Word w → Word w} {base : Word w}
    {length i : Nat} (hfit : base.toNat + length ≤ 2 ^ w) (hi : i < length)
    (value : Word w) :
    (arrayContents (fun address => if address = arrayAddr base i then value else mem address)
        base length).toFinset =
      insert value
        (if (arrayContents mem base length).count (mem (arrayAddr base i)) = 1 then
          (arrayContents mem base length).toFinset.erase (mem (arrayAddr base i))
        else (arrayContents mem base length).toFinset) := by
  have updated := congrArg Multiset.toFinset
    (multiset_arrayContents_store (mem := mem) hfit hi value)
  simpa only [List.toFinset_coe, Multiset.toFinset_cons, toFinset_erase_eq,
    Multiset.coe_count] using updated

namespace Source.ArrayAt

/-- Direct source-state version, expressed entirely in standard list and
finite-set operations after the representation assumption is supplied. -/
theorem toFinset_setMem {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {i : Nat} (hi : i < xs.length)
    (value : Word w) :
    (arrayContents (s.setMem (arrayAddr base i) value).mem base xs.length).toFinset =
      insert value
        (if xs.count xs[i] = 1 then xs.toFinset.erase xs[i] else xs.toFinset) := by
  simpa only [h.contents_eq, h.1.lookup i hi] using
    (toFinset_arrayContents_store (mem := s.mem) h.1.fits hi value)

end Source.ArrayAt
end Ram
