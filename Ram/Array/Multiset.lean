/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.AddSub
import Ram.Array.Model

/-!
# Multiset specifications of RAM arrays

The usual coercion from `List` to mathlib's `Multiset` forgets order while
retaining multiplicity. These bridges expose that model directly, without
introducing a separate RAM collection type or another executable operation.
In particular a real store removes one occurrence of the old value, even when
several cells contain that value.
-/

namespace Ram

@[simp]
theorem card_multiset_arrayContents (mem : Word w → Word w) (base : Word w)
    (length : Nat) :
    (arrayContents mem base length : Multiset (Word w)).card = length := by
  simp only [Multiset.coe_card, length_arrayContents]

namespace ArrayRep

/-- Rewrite a represented interval to its standard multiset model. -/
theorem multiset_eq {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) :
    (arrayContents mem base xs.length : Multiset (Word w)) = (xs : Multiset (Word w)) := by
  rw [h.contents_eq]

/-- A permutation proof is exactly preservation of the multiset observation.
The source and destination need not use the same heap or base address. -/
theorem multiset_eq_iff_perm {before after : Word w → Word w} {base other : Word w}
    {xs ys : List (Word w)} (hx : ArrayRep before base xs) (hy : ArrayRep after other ys) :
    (arrayContents before base xs.length : Multiset (Word w)) =
        (arrayContents after other ys.length : Multiset (Word w)) ↔ xs.Perm ys := by
  rw [hx.multiset_eq, hy.multiset_eq, Multiset.coe_eq_coe]

/-- Multiplicity goals reduce to ordinary list counts. -/
theorem multiset_count {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) (value : Word w) :
    (arrayContents mem base xs.length : Multiset (Word w)).count value = xs.count value := by
  rw [h.multiset_eq, Multiset.coe_count]

end ArrayRep

/-- The actual one-word heap update removes just the overwritten occurrence
and inserts the new value in the standard multiset model. -/
theorem multiset_arrayContents_store {mem : Word w → Word w} {base : Word w}
    {length i : Nat} (hfit : base.toNat + length ≤ 2 ^ w) (hi : i < length)
    (value : Word w) :
    (arrayContents (fun address => if address = arrayAddr base i then value else mem address)
        base length : Multiset (Word w)) =
      value ::ₘ (arrayContents mem base length : Multiset (Word w)).erase
        (mem (arrayAddr base i)) := by
  let xs := arrayContents mem base length
  have hi' : i < xs.length := by simpa only [xs, length_arrayContents] using hi
  have split : xs[i] ::ₘ (xs.eraseIdx i : Multiset (Word w)) =
      (xs : Multiset (Word w)) :=
    Multiset.coe_eq_coe.mpr (List.getElem_cons_eraseIdx_perm hi')
  have erased : (xs.eraseIdx i : Multiset (Word w)) =
      (xs : Multiset (Word w)).erase xs[i] := by
    rw [← split, Multiset.erase_cons_head]
  rw [arrayContents_store hfit hi]
  calc
    (xs.set i value : Multiset (Word w)) =
        value ::ₘ (xs.eraseIdx i : Multiset (Word w)) :=
      Multiset.coe_eq_coe.mpr (List.set_perm_cons_eraseIdx hi' value)
    _ = value ::ₘ (xs : Multiset (Word w)).erase (mem (arrayAddr base i)) := by
      rw [erased]
      simp only [xs, getElem_arrayContents]

/-- Count analysis of a real store needs only ordinary natural arithmetic.
The overwritten value and the inserted value may coincide. -/
theorem count_multiset_arrayContents_store {mem : Word w → Word w} {base : Word w}
    {length i : Nat} (hfit : base.toNat + length ≤ 2 ^ w) (hi : i < length)
    (value query : Word w) :
    (arrayContents (fun address => if address = arrayAddr base i then value else mem address)
        base length : Multiset (Word w)).count query =
      (arrayContents mem base length : Multiset (Word w)).count query -
          (if query = mem (arrayAddr base i) then 1 else 0) +
        (if query = value then 1 else 0) := by
  rw [multiset_arrayContents_store hfit hi, Multiset.count_cons]
  by_cases old : query = mem (arrayAddr base i)
  · subst query
    simp only [Multiset.count_erase_self, ite_true]
  · simp only [Multiset.count_erase_of_ne old, if_neg old, Nat.sub_zero]

namespace Source.ArrayAt

/-- A source store exposes the same multiset update, using the represented
list directly rather than asking the caller to recover memory observations. -/
theorem multiset_setMem {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {i : Nat} (hi : i < xs.length)
    (value : Word w) :
    (arrayContents (s.setMem (arrayAddr base i) value).mem base xs.length :
        Multiset (Word w)) = value ::ₘ (xs : Multiset (Word w)).erase xs[i] := by
  simpa only [h.contents_eq, h.1.lookup i hi] using
    (multiset_arrayContents_store (mem := s.mem) h.1.fits hi value)

end Source.ArrayAt
end Ram
