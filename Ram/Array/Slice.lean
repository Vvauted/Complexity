/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Range

/-!
# Subarray views and adjacent-array reassembly

Subarrays use the same memory and standard list `drop`/`take`; borrowing a
view inserts no allocation or copying into a program. Reassembly checks the
combined interval, since separately represented arrays could otherwise meet
across modular address wraparound. Empty suffixes at an allocation endpoint
are permitted without requiring that the unused endpoint be a strict address.
-/

namespace Ram

/-- Composing array offsets is ordinary modular word addition. -/
theorem arrayAddr_add (base : Word w) (first second : Nat) :
    arrayAddr (arrayAddr base first) second = arrayAddr base (first + second) := by
  simp only [arrayAddr, BitVec.ofNat_add, BitVec.add_assoc]

namespace ArrayRep

/-- A suffix is represented at its shifted word address. If the offset is
beyond the array, the standard empty list imposes no memory reads. -/
theorem drop {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (h : ArrayRep mem base xs) (offset : Nat) :
    ArrayRep mem (arrayAddr base offset) (xs.drop offset) := by
  refine ⟨?_, ?_⟩
  · by_cases ho : offset < xs.length
    · rw [h.addr_toNat ho, List.length_drop]
      have hf := h.fits
      omega
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt ho), List.length_nil, Nat.add_zero]
      exact Nat.le_of_lt (Word.toNat_lt _)
  · intro i hi
    have hix : offset + i < xs.length := by
      rw [List.length_drop] at hi
      omega
    rw [arrayAddr_add]
    simpa only [List.getElem_drop] using h.lookup (offset + i) hix

/-- Joining adjacent represented arrays requires one non-wrapping combined
interval; two independent array assertions alone do not imply that bound. -/
theorem append {mem : Word w → Word w} {base : Word w} {xs ys : List (Word w)}
    (left : ArrayRep mem base xs)
    (right : ArrayRep mem (arrayAddr base xs.length) ys)
    (hfit : base.toNat + (xs.length + ys.length) ≤ 2 ^ w) :
    ArrayRep mem base (xs ++ ys) := by
  refine ⟨by simpa only [List.length_append] using hfit, ?_⟩
  intro i hi
  by_cases hil : i < xs.length
  · rw [List.getElem_append_left hil]
    exact left.lookup i hil
  · have hlo : xs.length ≤ i := Nat.le_of_not_gt hil
    have hir : i - xs.length < ys.length := by
      rw [List.length_append] at hi
      omega
    rw [List.getElem_append_right hlo]
    have hr := right.lookup (i - xs.length) hir
    simpa only [arrayAddr_add, Nat.add_sub_of_le hlo] using hr

end ArrayRep

/-- A framed operation on a contained slice preserves every word outside
the whole array. The zero-length case preserves all memory, even when the
unused slice endpoint wraps to zero. -/
theorem ArrayFrame.within {before after : Word w → Word w} {base : Word w}
    {xs : List (Word w)} {offset length : Nat} (whole : ArrayRep before base xs)
    (hspan : offset + length ≤ xs.length)
    (slice : ArrayFrame (arrayAddr base offset) length before after) :
    ArrayFrame base xs.length before after := by
  intro address hout
  apply slice address
  by_cases hz : length = 0
  · subst length
    simpa only [Nat.add_zero] using Nat.lt_or_ge address.toNat (arrayAddr base offset).toNat
  · have hoffset : offset < xs.length := by omega
    rw [whole.addr_toNat hoffset]
    rcases hout with ha | ha
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

namespace Source.ArrayAt

/-- A suffix remains within the same heap boundary. At the final endpoint
the suffix is empty, so its word address may wrap without a memory access. -/
theorem drop {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {offset : Nat}
    (hoffset : offset ≤ xs.length) :
    ArrayAt heapLimit (arrayAddr base offset) (xs.drop offset) s := by
  refine ⟨h.1.drop offset, ?_⟩
  have haddr : (arrayAddr base offset).toNat ≤ base.toNat + offset := by
    simp only [arrayAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  rw [List.length_drop]
  have hh := h.2
  omega

/-- Borrow any clamped slice whose starting point is in the allocation. -/
theorem slice {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {offset : Nat}
    (hoffset : offset ≤ xs.length) (length : Nat) :
    ArrayAt heapLimit (arrayAddr base offset) ((xs.drop offset).take length) s :=
  (h.drop hoffset).take length

/-- Split a represented array without changing memory or requiring a new
allocation for either half. -/
theorem split {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {offset : Nat}
    (hoffset : offset ≤ xs.length) :
    ArrayAt heapLimit base (xs.take offset) s ∧
      ArrayAt heapLimit (arrayAddr base offset) (xs.drop offset) s :=
  ⟨h.take offset, h.drop hoffset⟩

/-- Reassemble adjacent arrays using the original allocation's total length.
This is useful after independent length-preserving operations on the halves. -/
theorem reassemble {heapLimit : Nat} {base : Word w} {xs left right : List (Word w)}
    {s t : State w} (whole : ArrayAt heapLimit base xs s)
    (front : ArrayAt heapLimit base left t)
    (back : ArrayAt heapLimit (arrayAddr base left.length) right t)
    (hlen : left.length + right.length = xs.length) :
    ArrayAt heapLimit base (left ++ right) t := by
  refine ⟨front.1.append back.1 (by rw [hlen]; exact whole.1.fits), ?_⟩
  simpa only [List.length_append, hlen] using whole.2

end Source.ArrayAt
end Ram
