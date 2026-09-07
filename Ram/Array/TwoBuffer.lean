/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Slice

/-!
# Frames for two array buffers

A two-buffer frame preserves an address when it is outside both intervals.
It does not assert that the buffers are disjoint; clients supply that fact
where needed. Lengths may differ, and borrowing a slice performs no copying,
allocation or other machine operation.

As in `ArrayRep` and `Slice`, element addresses do not wrap. An empty suffix
at the top of the word-address space may nevertheless have word address zero.
The interval and frame lemmas below retain this case explicitly.
-/

namespace Ram

/-- The modular address formula also applies to unused array endpoints. -/
theorem arrayAddr_toNat_mod (base : Word w) (offset : Nat) :
    (arrayAddr base offset).toNat = (base.toNat + offset) % 2 ^ w := by
  rw [arrayAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]

/-- Memory outside both allowed intervals is unchanged. -/
def TwoBufferFrame (first : Word w) (firstLen : Nat) (second : Word w) (secondLen : Nat)
    (before after : Word w → Word w) : Prop :=
  ∀ address,
    (address.toNat < first.toNat ∨ first.toNat + firstLen ≤ address.toNat) →
    (address.toNat < second.toNat ∨ second.toNat + secondLen ≤ address.toNat) →
    after address = before address

namespace TwoBufferFrame

theorem refl (first : Word w) (firstLen : Nat) (second : Word w) (secondLen : Nat)
    (mem : Word w → Word w) : TwoBufferFrame first firstLen second secondLen mem mem :=
  fun _ _ _ => rfl

theorem trans {first second : Word w} {firstLen secondLen : Nat}
    {before middle after : Word w → Word w}
    (left : TwoBufferFrame first firstLen second secondLen before middle)
    (right : TwoBufferFrame first firstLen second secondLen middle after) :
    TwoBufferFrame first firstLen second secondLen before after :=
  fun address hfirst hsecond =>
    (right address hfirst hsecond).trans (left address hfirst hsecond)

/-- Exchange the roles of source and scratch without changing the frame. -/
theorem swap {first second : Word w} {firstLen secondLen : Nat}
    {before after : Word w → Word w}
    (h : TwoBufferFrame first firstLen second secondLen before after) :
    TwoBufferFrame second secondLen first firstLen before after :=
  fun address hsecond hfirst => h address hfirst hsecond

theorem of_left {first second : Word w} {firstLen secondLen : Nat}
    {before after : Word w → Word w} (h : ArrayFrame first firstLen before after) :
    TwoBufferFrame first firstLen second secondLen before after :=
  fun address hfirst _ => h address hfirst

theorem of_right {first second : Word w} {firstLen secondLen : Nat}
    {before after : Word w → Word w} (h : ArrayFrame second secondLen before after) :
    TwoBufferFrame first firstLen second secondLen before after :=
  fun address _ hsecond => h address hsecond

/-- A third represented array survives when disjoint from each buffer. -/
theorem preserves {first second other : Word w} {firstLen secondLen : Nat}
    {before after : Word w → Word w} {ys : List (Word w)}
    (h : TwoBufferFrame first firstLen second secondLen before after)
    (hfirst : ArraysDisjoint first firstLen other ys.length)
    (hsecond : ArraysDisjoint second secondLen other ys.length)
    (hother : ArrayRep before other ys) : ArrayRep after other ys := by
  refine ⟨hother.fits, ?_⟩
  intro i hi
  have haddr := hother.addr_toNat hi
  have houtFirst : (arrayAddr other i).toNat < first.toNat ∨
      first.toNat + firstLen ≤ (arrayAddr other i).toNat := by
    rw [haddr]
    unfold ArraysDisjoint at hfirst
    omega
  have houtSecond : (arrayAddr other i).toNat < second.toNat ∨
      second.toNat + secondLen ≤ (arrayAddr other i).toNat := by
    rw [haddr]
    unfold ArraysDisjoint at hsecond
    omega
  exact (h (arrayAddr other i) houtFirst houtSecond).trans (hother.lookup i hi)

private theorem outside_slice {mem : Word w → Word w} {base : Word w}
    {xs : List (Word w)} {offset length : Nat} (whole : ArrayRep mem base xs)
    (hspan : offset + length ≤ xs.length) (address : Word w)
    (hout : address.toNat < base.toNat ∨ base.toNat + xs.length ≤ address.toNat) :
    address.toNat < (arrayAddr base offset).toNat ∨
      (arrayAddr base offset).toNat + length ≤ address.toNat := by
  by_cases hz : length = 0
  · subst length
    simpa only [Nat.add_zero] using Nat.lt_or_ge address.toNat (arrayAddr base offset).toNat
  · rw [whole.addr_toNat (by omega : offset < xs.length)]
    omega

/-- A pair of contained slices may be enlarged to the two whole buffers.
Empty slices preserve all addresses, including when their endpoints wrap. -/
theorem within {first second : Word w} {xs ys : List (Word w)}
    {firstOffset firstLen secondOffset secondLen : Nat} {before after : Word w → Word w}
    (firstWhole : ArrayRep before first xs) (secondWhole : ArrayRep before second ys)
    (firstSpan : firstOffset + firstLen ≤ xs.length)
    (secondSpan : secondOffset + secondLen ≤ ys.length)
    (h : TwoBufferFrame (arrayAddr first firstOffset) firstLen
      (arrayAddr second secondOffset) secondLen before after) :
    TwoBufferFrame first xs.length second ys.length before after := by
  intro address hfirst hsecond
  exact h address (outside_slice firstWhole firstSpan address hfirst)
    (outside_slice secondWhole secondSpan address hsecond)

end TwoBufferFrame

namespace ArraysDisjoint

/-- Disjoint whole intervals remain disjoint after borrowing a left slice.
If the slice endpoint wraps, the slice must be empty and begins at zero. -/
theorem slice_left {mem : Word w → Word w} {base other : Word w}
    {xs : List (Word w)} {otherLen offset length : Nat}
    (whole : ArrayRep mem base xs) (hspan : offset + length ≤ xs.length)
    (h : ArraysDisjoint base xs.length other otherLen) :
    ArraysDisjoint (arrayAddr base offset) length other otherLen := by
  by_cases hfit : base.toNat + offset < 2 ^ w
  · unfold ArraysDisjoint at h ⊢
    rw [arrayAddr_toNat hfit]
    omega
  · have hf := whole.fits
    have hz : length = 0 := by omega
    have hend : base.toNat + offset = 2 ^ w := by omega
    unfold ArraysDisjoint
    rw [arrayAddr_toNat_mod, hend, Nat.mod_self, hz]
    exact Or.inl (Nat.zero_le _)

/-- The symmetric slice rule, with the represented array on the right. -/
theorem slice_right {mem : Word w → Word w} {base other : Word w}
    {ys : List (Word w)} {len offset length : Nat}
    (whole : ArrayRep mem other ys) (hspan : offset + length ≤ ys.length)
    (h : ArraysDisjoint base len other ys.length) :
    ArraysDisjoint base len (arrayAddr other offset) length :=
  Or.symm (slice_left whole hspan (Or.symm h))

/-- Any two contained views of disjoint buffers remain disjoint. The views
may have different offsets and lengths, including length zero. -/
theorem slices {leftMem rightMem : Word w → Word w} {first second : Word w}
    {xs ys : List (Word w)} {firstOffset firstLen secondOffset secondLen : Nat}
    (firstWhole : ArrayRep leftMem first xs) (secondWhole : ArrayRep rightMem second ys)
    (firstSpan : firstOffset + firstLen ≤ xs.length)
    (secondSpan : secondOffset + secondLen ≤ ys.length)
    (h : ArraysDisjoint first xs.length second ys.length) :
    ArraysDisjoint (arrayAddr first firstOffset) firstLen
      (arrayAddr second secondOffset) secondLen :=
  slice_right secondWhole secondSpan (slice_left firstWhole firstSpan h)

end ArraysDisjoint

/-- The standard take/drop split gives disjoint adjacent views. At a full
address-space endpoint the empty right view may wrap to word address zero. -/
theorem ArrayRep.split_disjoint {mem : Word w → Word w} {base : Word w}
    {xs : List (Word w)} (whole : ArrayRep mem base xs) {offset : Nat}
    (hoffset : offset ≤ xs.length) :
    ArraysDisjoint base (xs.take offset).length
      (arrayAddr base offset) (xs.drop offset).length := by
  by_cases hfit : base.toNat + offset < 2 ^ w
  · unfold ArraysDisjoint
    rw [arrayAddr_toNat hfit, List.length_take, Nat.min_eq_left hoffset]
    exact Or.inl (Nat.le_refl _)
  · have hf := whole.fits
    have hend : base.toNat + offset = 2 ^ w := by omega
    have hz : xs.length - offset = 0 := by omega
    unfold ArraysDisjoint
    rw [arrayAddr_toNat_mod, hend, Nat.mod_self, List.length_drop, hz]
    exact Or.inr (Nat.zero_le _)

/-- Retain the third array's heap-bound assertion as well as its contents. -/
theorem Source.ArrayAt.frame_two {heapLimit firstLen secondLen : Nat}
    {first second other : Word w} {ys : List (Word w)} {s t : Source.State w}
    (h : Source.ArrayAt heapLimit other ys s)
    (frame : TwoBufferFrame first firstLen second secondLen s.mem t.mem)
    (hfirst : ArraysDisjoint first firstLen other ys.length)
    (hsecond : ArraysDisjoint second secondLen other ys.length) :
    Source.ArrayAt heapLimit other ys t :=
  ⟨frame.preserves hfirst hsecond h.1, h.2⟩

end Ram
