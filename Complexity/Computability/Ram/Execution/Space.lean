/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Execution.Memory
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto

/-!
# Seeded physical word footprints of actual RAM executions

The footprint is an author-supplied initial address set together with the
distinct heap addresses touched by the existing execution. The seed includes
preloaded input and metadata even when they are never accessed. Stack loads and
stores are ordinary heap accesses. Registers, code and external I/O are not part
of this measure. It counts neither the highest address nor a reserved arena.

This is a cumulative physical-word footprint, not exact peak reachable-live
storage or cumulative allocation. Repeated access and reuse of an address count
once. Sequential composition retains the original seed; it never resets the
footprint between calls. No runner or alternate execution relation is added.
-/

namespace Ram

/-- The initial address interval, encoded at the actual machine width. -/
def initialSegment (w size : Nat) : Finset (Word w) :=
  (Finset.range size).image (BitVec.ofNat w)

theorem initialSegment_card_le (w size : Nat) :
    (initialSegment w size).card ≤ size := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range size)

/-- A fitting interval has no modular address collisions. -/
theorem initialSegment_card_eq {w size : Nat} (fits : size ≤ 2 ^ w) :
    (initialSegment w size).card = size := by
  unfold initialSegment
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb same
  have ha' : a < 2 ^ w := (Finset.mem_range.mp ha).trans_le fits
  have hb' : b < 2 ^ w := (Finset.mem_range.mp hb).trans_le fits
  have decoded := congrArg BitVec.toNat same
  simpa only [Word.ofNat_toNat_of_lt ha', Word.ofNat_toNat_of_lt hb'] using decoded

/-- An address interval at any base, used for separated heap and stack regions. -/
def addressInterval (w base count : Nat) : Finset (Word w) :=
  (Finset.range count).image (fun i => BitVec.ofNat w (base + i))

theorem addressInterval_card_le (w base count : Nat) :
    (addressInterval w base count).card ≤ count :=
  (Finset.card_image_le).trans_eq (Finset.card_range count)

/-- A fitting interval describes exactly its ordinary half-open address range. -/
theorem mem_addressInterval_iff {w base count : Nat} {address : Word w}
    (fits : base + count ≤ 2 ^ w) :
    address ∈ addressInterval w base count ↔
      base ≤ address.toNat ∧ address.toNat < base + count := by
  simp only [addressInterval, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have range : base + i < 2 ^ w := (Nat.add_lt_add_left hi base).trans_le fits
    rw [Word.ofNat_toNat_of_lt range]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi base⟩
  · rintro ⟨lower, upper⟩
    refine ⟨address.toNat - base, ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le lower, Word.ofNat_toNat_self]

/-- Distinct physical heap words, including the fixed initial footprint. -/
def spaceFootprint (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : Finset (Word w) :=
  seed ∪ heapAccesses code n start

/-- The physical word count of the seeded actual trace. -/
def spaceWords (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : Nat :=
  (spaceFootprint code n start seed).card

@[simp] theorem spaceFootprint_zero (code : Code) (start : State w)
    (seed : Finset (Word w)) : spaceFootprint code 0 start seed = seed := by
  simp [spaceFootprint]

@[simp] theorem spaceWords_zero (code : Code) (start : State w)
    (seed : Finset (Word w)) : spaceWords code 0 start seed = seed.card := by
  simp [spaceWords]

theorem seed_subset_spaceFootprint (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : seed ⊆ spaceFootprint code n start seed :=
  Finset.subset_union_left

theorem accesses_subset_spaceFootprint (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : heapAccesses code n start ⊆ spaceFootprint code n start seed :=
  Finset.subset_union_right

theorem spaceFootprint_seed_mono {code : Code} {n : Nat} {start : State w}
    {seed other : Finset (Word w)} (h : seed ⊆ other) :
    spaceFootprint code n start seed ⊆ spaceFootprint code n start other := by
  intro address member
  rcases Finset.mem_union.mp member with member | member
  · exact Finset.mem_union_left _ (h member)
  · exact Finset.mem_union_right _ member

theorem spaceFootprint_time_mono {code : Code} {n m : Nat} {start : State w}
    {seed : Finset (Word w)} (h : n ≤ m) :
    spaceFootprint code n start seed ⊆ spaceFootprint code m start seed := by
  intro address member
  rcases Finset.mem_union.mp member with member | member
  · exact Finset.mem_union_left _ member
  · obtain ⟨k, hk, current, next, run, step, access⟩ := mem_heapAccesses_iff.mp member
    exact Finset.mem_union_right _
      (mem_heapAccesses_iff.mpr ⟨k, hk.trans_le h, current, next, run, step, access⟩)

theorem spaceWords_seed_mono {code : Code} {n : Nat} {start : State w}
    {seed other : Finset (Word w)} (h : seed ⊆ other) :
    spaceWords code n start seed ≤ spaceWords code n start other :=
  Finset.card_le_card (spaceFootprint_seed_mono h)

theorem spaceWords_time_mono {code : Code} {n m : Nat} {start : State w}
    {seed : Finset (Word w)} (h : n ≤ m) :
    spaceWords code n start seed ≤ spaceWords code m start seed :=
  Finset.card_le_card (spaceFootprint_time_mono h)

/-- Exact union at an actually executed cut; shared addresses are not duplicated. -/
theorem spaceFootprint_add {code : Code} {n : Nat} {start middle : State w}
    (first : Exec code n start middle) (m : Nat) (seed : Finset (Word w)) :
    spaceFootprint code (n + m) start seed =
      spaceFootprint code n start seed ∪ spaceFootprint code m middle seed := by
  ext address
  simp only [spaceFootprint, heapAccesses_add first m, Finset.mem_union]
  tauto

/-- Continue with the complete preceding footprint as the suffix's seed. -/
theorem spaceFootprint_continue {code : Code} {n : Nat} {start middle : State w}
    (first : Exec code n start middle) (m : Nat) (seed : Finset (Word w)) :
    spaceFootprint code (n + m) start seed =
      spaceFootprint code m middle (spaceFootprint code n start seed) := by
  simp only [spaceFootprint, heapAccesses_add first m, Finset.union_assoc]

theorem spaceWords_continue {code : Code} {n : Nat} {start middle : State w}
    (first : Exec code n start middle) (m : Nat) (seed : Finset (Word w)) :
    spaceWords code (n + m) start seed =
      spaceWords code m middle (spaceFootprint code n start seed) := by
  unfold spaceWords
  rw [spaceFootprint_continue first m seed]

theorem spaceWords_add_le {code : Code} {n : Nat} {start middle : State w}
    (first : Exec code n start middle) (m : Nat) (seed : Finset (Word w)) :
    spaceWords code (n + m) start seed ≤
      spaceWords code n start seed + spaceWords code m middle seed := by
  unfold spaceWords
  rw [spaceFootprint_add first m seed]
  exact Finset.card_union_le _ _

/-- Reusing only seeded addresses consumes no additional distinct words. -/
theorem spaceWords_eq_seed_card {code : Code} {n : Nat} {start : State w}
    {seed : Finset (Word w)} (h : heapAccesses code n start ⊆ seed) :
    spaceWords code n start seed = seed.card := by
  simp only [spaceWords, spaceFootprint, Finset.union_eq_left.mpr h]

theorem seed_card_le_spaceWords (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : seed.card ≤ spaceWords code n start seed :=
  Finset.card_le_card (seed_subset_spaceFootprint code n start seed)

/-- At most one new heap address per actual transition, in addition to the seed. -/
theorem spaceWords_le_card_add_steps (code : Code) (n : Nat) (start : State w)
    (seed : Finset (Word w)) : spaceWords code n start seed ≤ seed.card + n :=
  (Finset.card_union_le seed (heapAccesses code n start)).trans
    (Nat.add_le_add_left (heapAccesses_card_le code n start) seed.card)

/-- Any region containing both the initial footprint and actual accesses bounds
the same execution's word footprint. The region may be a noncontiguous union. -/
theorem spaceWords_le_of_subsets {code : Code} {n : Nat} {start : State w}
    {seed region : Finset (Word w)} (initial : seed ⊆ region)
    (accesses : heapAccesses code n start ⊆ region) :
    spaceWords code n start seed ≤ region.card := by
  apply Finset.card_le_card
  intro address member
  rcases Finset.mem_union.mp member with member | member
  · exact initial member
  · exact accesses member

/-- Convert the footprint to bytes at a fixed physical word size. -/
theorem spaceWords_bytes_le {code : Code} {n : Nat} {start : State w}
    {seed : Finset (Word w)} {bound : Nat}
    (h : spaceWords code n start seed ≤ bound) (bytesPerWord : Nat) :
    spaceWords code n start seed * bytesPerWord ≤ bound * bytesPerWord :=
  Nat.mul_le_mul_right bytesPerWord h

/-- A finite space certificate for one actual halted machine trace. -/
structure SpaceBound (code : Code) (n : Nat) (start finish : State w)
    (seed : Finset (Word w)) (bound : Nat) : Prop where
  run : Exec code n start finish
  halted : finish.status = .halted
  space : spaceWords code n start seed ≤ bound

namespace SpaceBound

variable {code : Code} {n : Nat} {start finish : State w}
variable {seed : Finset (Word w)} {a b : Nat}

theorem mono (h : SpaceBound code n start finish seed a) (hab : a ≤ b) :
    SpaceBound code n start finish seed b :=
  ⟨h.run, h.halted, h.space.trans hab⟩

/-- Every prefix retains the same initial footprint and satisfies the full bound. -/
theorem prefix_bound (h : SpaceBound code n start finish seed b) {k : Nat} (hk : k ≤ n) :
    spaceWords code k start seed ≤ b :=
  (spaceWords_time_mono hk).trans h.space

theorem seed_le (h : SpaceBound code n start finish seed b) : seed.card ≤ b :=
  (seed_card_le_spaceWords code n start seed).trans h.space

/-- Sequential continuation uses the preceding footprint as its initial seed. -/
theorem prepend {m : Nat} {middle : State w} (first : Exec code n start middle)
    (suffix : SpaceBound code m middle finish (spaceFootprint code n start seed) b) :
    SpaceBound code (n + m) start finish seed b := by
  refine ⟨first.trans suffix.run, suffix.halted, ?_⟩
  rw [spaceWords_continue first m seed]
  exact suffix.space

end SpaceBound

end Ram
