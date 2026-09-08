/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Range

/-!
# Runtime addresses in represented array intervals

These bridges use the existing `ArrayRep`, `ArrayAt`, and `ArrayFrame`, without
a separate footprint or heap model. A runtime pointer belongs to an array
exactly when its natural address lies in the array's half-open interval.
Recovering its index lets an ordinary single-word store reuse `List.set` and
the existing frame rules, even when later register updates change the state.

For a batch of updates, compose the existing `ArrayFrame.trans` and preserve
other arrays with `Source.ArrayAt.frame`. For slices or two writable buffers,
`Complexity.Computability.Ram.Array.Slice` and `Complexity.Computability.Ram.Array.TwoBuffer` already provide the corresponding
containment and preservation rules; no aliases are added here.

Membership always uses a strict upper bound. Empty arrays have no element
addresses. An unused endpoint may wrap as a word, but is not thereby an element
of the empty suffix; if that word aliases an earlier cell of a nonempty array,
membership correctly refers to that earlier cell rather than to the endpoint.
These are representation lemmas, not additional machine instructions.
-/

namespace Ram

/-- The represented element addresses are exactly the mathematical half-open
interval, not a circular word interval. -/
theorem ArrayRep.exists_index_iff {mem : Word w → Word w} {base address : Word w}
    {xs : List (Word w)} (h : ArrayRep mem base xs) :
    (∃ i, i < xs.length ∧ arrayAddr base i = address) ↔
      base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + xs.length := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [h.addr_toNat hi]
    omega
  · rintro ⟨hlo, hhi⟩
    have hi : address.toNat - base.toNat < xs.length := by omega
    refine ⟨address.toNat - base.toNat, hi, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [h.addr_toNat hi, Nat.add_sub_of_le hlo]

/-- Legal elements of disjoint represented arrays cannot alias, even when
their representations refer to different memory states. -/
theorem ArraysDisjoint.addr_ne {leftMem rightMem : Word w → Word w}
    {base other : Word w} {xs ys : List (Word w)}
    (disjoint : ArraysDisjoint base xs.length other ys.length)
    (left : ArrayRep leftMem base xs) (right : ArrayRep rightMem other ys)
    {i j : Nat} (hi : i < xs.length) (hj : j < ys.length) :
    arrayAddr base i ≠ arrayAddr other j := by
  intro equal
  have he := congrArg (fun address : Word w => address.toNat) equal
  change (arrayAddr base i).toNat = (arrayAddr other j).toNat at he
  rw [left.addr_toNat hi, right.addr_toNat hj] at he
  unfold ArraysDisjoint at disjoint
  omega

/-- A runtime-addressed store gives safety, the updated logical contents, and
its frame together. The target may also differ in registers or I/O, provided
its memory is exactly the indicated single-word update. -/
theorem Source.ArrayAt.store_at {heapLimit : Nat} {base address value : Word w}
    {xs : List (Word w)} {s t : Source.State w} (h : Source.ArrayAt heapLimit base xs s)
    (bounds : base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + xs.length)
    (memory : t.mem = (s.setMem address value).mem) :
    address.toNat < heapLimit ∧
      Source.ArrayAt heapLimit base (xs.set (address.toNat - base.toNat) value) t ∧
      ArrayFrame base xs.length s.mem t.mem := by
  obtain ⟨i, hi, haddress⟩ := h.1.exists_index_iff.mpr bounds
  have index : address.toNat - base.toNat = i := by
    rw [← haddress, h.1.addr_toNat hi]
    exact Nat.add_sub_cancel_left _ _
  have updated := h.setMem hi value
  have memory' : t.mem = (s.setMem (arrayAddr base i) value).mem := by
    simpa only [haddress] using memory
  refine ⟨Nat.lt_of_lt_of_le bounds.2 h.2, ?_, ?_⟩
  · rw [index]
    exact updated.of_mem_eq memory'
  · rw [memory']
    exact ArrayFrame.store h.1 hi value

end Ram
