/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Contracts
import Init.Data.List.Nat.TakeDrop

/-!
# Prefix views and framed array replacement

These are representation lemmas, not new machine operations. A client may
borrow a prefix of an allocated array, run an existing contract on that prefix,
then recover the full array using the contract's frame. Contents use standard
`List.take`, `List.drop` and append; no copying or allocation is implicit.
-/

namespace Ram

/-- A smaller modified interval also satisfies the frame for any larger
interval at the same base. -/
theorem ArrayFrame.mono {base : Word w} {small large : Nat}
    {before after : Word w → Word w} (h : ArrayFrame base small before after)
    (hle : small ≤ large) : ArrayFrame base large before after := by
  intro address hout
  apply h address
  rcases hout with ha | ha
  · exact Or.inl ha
  · exact Or.inr (by omega)

namespace ArrayRep

/-- Any standard list prefix is represented at the same base. The requested
length is allowed to exceed the array length, just as for `List.take`. -/
theorem take {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) (length : Nat) :
    ArrayRep mem base (xs.take length) := by
  refine ⟨?_, ?_⟩
  · exact Nat.le_trans (Nat.add_le_add_left (List.length_take_le' length xs) _) h.fits
  · intro i hi
    simpa only [List.getElem_take] using
      h.lookup i (Nat.lt_of_lt_of_le hi (List.length_take_le' length xs))

/-- Replace an existing prefix by an equally sized represented prefix.
The frame supplies the unchanged suffix, including the empty-prefix case. -/
theorem replace_prefix {before after : Word w → Word w} {base : Word w}
    {xs ys : List (Word w)} (h : ArrayRep before base xs)
    (hprefix : ArrayRep after base ys) (hlen : ys.length ≤ xs.length)
    (hframe : ArrayFrame base ys.length before after) :
    ArrayRep after base (ys ++ xs.drop ys.length) := by
  have hlength : (ys ++ xs.drop ys.length).length = xs.length := by
    simp only [List.length_append, List.length_drop]
    omega
  refine ⟨by simpa only [hlength] using h.fits, ?_⟩
  intro i hi
  have hix : i < xs.length := by simpa only [hlength] using hi
  by_cases hip : i < ys.length
  · rw [List.getElem_append_left hip]
    exact hprefix.lookup i hip
  · have hle : ys.length ≤ i := Nat.le_of_not_gt hip
    rw [List.getElem_append_right hle, List.getElem_drop]
    have hout : base.toNat + ys.length ≤ (arrayAddr base i).toNat := by
      rw [h.addr_toNat hix]
      omega
    simpa only [Nat.add_sub_of_le hle] using
      (hframe (arrayAddr base i) (Or.inr hout)).trans (h.lookup i hix)

end ArrayRep

namespace Source.ArrayAt

/-- A prefix borrows the same heap allocation; there is no memory operation. -/
theorem take {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) (length : Nat) :
    ArrayAt heapLimit base (xs.take length) s :=
  ⟨h.1.take length,
    Nat.le_trans (Nat.add_le_add_left (List.length_take_le' length xs) _) h.2⟩

/-- Recover the full heap-array invariant after a framed prefix operation. -/
theorem replace_prefix {heapLimit : Nat} {base : Word w} {xs ys : List (Word w)}
    {s t : State w} (h : ArrayAt heapLimit base xs s)
    (hprefix : ArrayAt heapLimit base ys t) (hlen : ys.length ≤ xs.length)
    (hframe : ArrayFrame base ys.length s.mem t.mem) :
    ArrayAt heapLimit base (ys ++ xs.drop ys.length) t := by
  refine ⟨h.1.replace_prefix hprefix.1 hlen hframe, ?_⟩
  have hheap := h.2
  simp only [List.length_append, List.length_drop]
  omega

/-- A memory-preserving operation retains every represented array even if
it updates registers or consumes input. -/
theorem of_mem_eq {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s t : State w} (h : ArrayAt heapLimit base xs s) (hmem : t.mem = s.mem) :
    ArrayAt heapLimit base xs t := by
  exact ⟨hmem.symm ▸ h.1, h.2⟩

end Source.ArrayAt
end Ram
