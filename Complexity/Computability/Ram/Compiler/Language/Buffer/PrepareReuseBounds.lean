/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareReuseSpace
import Complexity.Computability.Ram.Compiler.Language.Arena.Space.Regions

/-!
# Shared physical regions for reusable current-array preparation

The actual initialized allocator and scalar writer use one common high stack
interval. Their complete access union fits a separately justified source heap
prefix plus this fixed stack interval. Repeated requests do not add another
stack reservation, and fitting requests do not allocate another input buffer.

The heap-prefix certificate includes retained candidate allocations and any
previous physical peak; it is not inferred from the final cursor. Geometric
growth bounds the loader's additional reservation, not the candidate's memory.
The original complete footprint remains the seed throughout preparation.
-/

namespace Ram.LanguageCompiler.Buffer.PrepareReuse

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.PrepareReuse

variable {w heapLimit H : Nat}

/-- The two real preparation entries reuse the same high stack base. -/
def frameWords : Nat :=
  max (ABI.frameSize (programControl Replicate.program))
    (ABI.frameSize (programControl Complexity.Language.Buffer.Prepare.writeProgram))

/-- A heap prefix and the loader's separately placed fixed stack interval. -/
def region (w heapLimit H : Nat) : Finset (Word w) :=
  Ram.addressInterval w 0 H ∪ Ram.addressInterval w heapLimit frameWords

theorem region_card_le (w heapLimit H : Nat) :
    (region w heapLimit H).card ≤ H + frameWords :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Ram.addressInterval_card_le w 0 H)
    (Ram.addressInterval_card_le w heapLimit frameWords))

private theorem addressInterval_mono {base first second : Nat} (bound : first ≤ second) :
    Ram.addressInterval w base first ⊆ Ram.addressInterval w base second := by
  intro address member
  obtain ⟨index, before, rfl⟩ := Finset.mem_image.mp member
  exact Finset.mem_image.mpr
    ⟨index, Finset.mem_range.mpr ((Finset.mem_range.mp before).trans_le bound), rfl⟩

private theorem regions_mono {frames : Nat} (bound : frames ≤ frameWords) :
    Ram.addressInterval w 0 H ∪ Ram.addressInterval w heapLimit frames ⊆
      region w heapLimit H :=
  Finset.union_subset_union (Finset.Subset.refl _) (addressInterval_mono bound)

/-- Realize writes in the fixed high stack while carrying a small heap arena
through every actual returned state. The region bound counts shared frames once. -/
theorem fill_exists_regions (values : Array Nat) (buffer : Buffer .nat)
    (count : Nat) (before : count ≤ values.size) (current : Session.State w heapLimit)
    (valid : buffer.Valid current.heap) (size : buffer.length = values.size)
    (capacity : FunctionCapacity Complexity.Language.Buffer.Prepare.writeProgram
      Complexity.Language.Buffer.Prepare.writeEntry w 0 heapLimit)
    (smallArena : ArenaRep current.placement current.cursor H current.heap current.entry)
    (separated : H ≤ heapLimit)
    (lengthFits : buffer.length < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (seed : Finset (Word w)) :
    ∃ finish steps footprint,
      Prepare.SpaceFill values buffer count current finish steps seed footprint ∧
      ArenaRep finish.placement finish.cursor H finish.heap finish.entry ∧
      finish.cursor = current.cursor ∧ steps = count * Prepare.writeSteps ∧
      footprint ⊆ seed ∪ region w heapLimit H := by
  induction count with
  | zero =>
      exact ⟨current, 0, seed, .zero _ _, smallArena, rfl, by simp,
        Finset.subset_union_left⟩
  | succ count ih =>
      obtain ⟨middle, steps, footprint, rest, middleArena, cursor, counted, bounded⟩ :=
        ih (by omega)
      have nextValid := valid.mono rest.erase.source.shape
      obtain ⟨contents, observed⟩ := nextValid.contents
      have indexBound : count < values.size := by omega
      obtain ⟨writtenHeap, written, _⟩ := observed.write_exists
        (index := count) (by rw [observed.size_eq, size]; exact indexBound)
        values[count]
      let smallMiddle : Session.State w H :=
        ⟨middle.heap, middle.placement, middle.cursor, middle.entry, middleArena⟩
      obtain ⟨small, _, smallCursor, smallSteps⟩ :=
        Prepare.write buffer count values[count] smallMiddle writtenHeap
          (capacity.mono_heap separated) nextValid.rooted lengthFits
          (by omega) (fits count indexBound) written
      obtain ⟨outcome, _, _, _, outcomeCursor, outcomeSteps, finalArena, accessed⟩ :=
        small.raise_stack capacity separated
      have accesses : outcome.heapAccesses ⊆ region w heapLimit H :=
        accessed.trans (regions_mono (by
          simpa only [Nat.zero_add, Nat.one_mul] using
            (Nat.le_max_right
              (ABI.frameSize (programControl Replicate.program))
              (ABI.frameSize (programControl
                Complexity.Language.Buffer.Prepare.writeProgram)))))
      refine ⟨Session.State.ofExecution outcome, steps + outcome.result.steps,
        footprint ∪ outcome.heapAccesses, .succ rest indexBound outcome,
        finalArena, ?_, ?_, ?_⟩
      · change outcome.cursor = current.cursor
        exact outcomeCursor.trans (smallCursor.trans cursor)
      · rw [counted, outcomeSteps, smallSteps, Nat.add_mul, Nat.one_mul]
      · intro address member
        rcases Finset.mem_union.mp member with old | fresh
        · exact bounded old
        · exact Finset.mem_union_right _ (accesses fresh)

/-- The same reusable loader has a real high-stack realization bounded by one
common region. Small-arena and capacity premises are separate from a time budget.
The loader uses no fresh cells when the retained cache fits the current request. -/
theorem exists_regions (values : Array Nat) (cache : Cache)
    (current : Session.State w heapLimit) (valid : Valid cache current.heap)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity Complexity.Language.Buffer.Prepare.writeProgram
      Complexity.Language.Buffer.Prepare.writeEntry w 0 heapLimit)
    (smallArena : ArenaRep current.placement current.cursor H current.heap current.entry)
    (separated : H ≤ heapLimit)
    (lengthFits : values.size < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (space : current.cursor +
      Complexity.GeometricCapacity.allocated (capacity cache) values.size ≤ H)
    (seed : Finset (Word w)) :
    ∃ nextCache view finish count footprint,
      SpaceRun values cache current nextCache view finish count seed footprint ∧
      view.Contents finish.heap values ∧ Valid nextCache finish.heap ∧
      finish.cursor = current.cursor +
        Complexity.GeometricCapacity.allocated (capacity cache) values.size ∧
      count = steps cache values.size ∧
      ArenaRep finish.placement finish.cursor H finish.heap finish.entry ∧
      footprint ⊆ seed ∪ region w heapLimit H := by
  by_cases needed : NeedsGrowth cache values.size
  · have amount : Complexity.GeometricCapacity.allocated (capacity cache) values.size =
        Complexity.GeometricCapacity.next (capacity cache) values.size := by
      rcases needed with empty | smaller
      · subst cache
        simp only [capacity, Complexity.GeometricCapacity.allocated_zero,
          Complexity.GeometricCapacity.next_zero]
      · simp only [Complexity.GeometricCapacity.allocated_of_lt smaller,
          Complexity.GeometricCapacity.next_of_lt smaller]
    let length := Complexity.GeometricCapacity.next (capacity cache) values.size
    have space' : current.cursor + length ≤ H := by simpa only [amount] using space
    have bufferFits : length < 2 ^ w := by
      have := smallArena.limit_lt
      omega
    let smallCurrent : Session.State w H :=
      ⟨current.heap, current.placement, current.cursor, current.entry, smallArena⟩
    obtain ⟨small, smallBuffer, smallHeap, smallCursor, smallSteps⟩ :=
      Prepare.allocate length smallCurrent (allocationCapacity.mono_heap separated)
        bufferFits space'
    obtain ⟨allocated, bufferEq, heapEq, _, cursorEq, countEq, allocatedArena, accessed⟩ :=
      small.raise_stack allocationCapacity separated
    have bufferValid : allocated.value.Valid allocated.heap := by
      rw [bufferEq, heapEq, smallBuffer, smallHeap]
      exact current.heap.alloc_valid _ _
    have bound : values.size ≤ allocated.value.length := by
      rw [bufferEq, smallBuffer]
      change values.size ≤ length
      exact Complexity.GeometricCapacity.next_ge_request _ _
    obtain ⟨finish, count, footprint, filled, finalArena, cursor, counted, bounded⟩ :=
      fill_exists_regions values (requestView allocated.value values.size) values.size
        (Nat.le_refl _) (Session.State.ofExecution allocated)
        (valid_prefix bufferValid bound) rfl writeCapacity allocatedArena separated
        lengthFits fits (seed ∪ allocated.heapAccesses)
    have accesses : allocated.heapAccesses ⊆ region w heapLimit H :=
      accessed.trans (regions_mono (by
        simpa only [Nat.zero_add, Nat.one_mul] using
          (Nat.le_max_left
            (ABI.frameSize (programControl Replicate.program))
            (ABI.frameSize (programControl
              Complexity.Language.Buffer.Prepare.writeProgram)))))
    have run := SpaceRun.grow needed allocated filled
    refine ⟨some allocated.value, requestView allocated.value values.size, finish,
      allocated.result.steps + count, footprint, run, run.source.observed.1,
      run.source.observed.2.1, ?_, ?_, finalArena, ?_⟩
    · change finish.cursor = current.cursor + _
      rw [cursor]
      change allocated.cursor = current.cursor + _
      rw [cursorEq, smallCursor, amount]
    · rw [countEq, smallSteps, counted]
      simp only [steps, if_pos needed, length]
    · intro address member
      rcases Finset.mem_union.mp (bounded member) with old | shared
      · rcases Finset.mem_union.mp old with seeded | allocation
        · exact Finset.mem_union_left _ seeded
        · exact Finset.mem_union_right _ (accesses allocation)
      · exact Finset.mem_union_right _ shared
  · cases cache with
    | none => exact (needed (Or.inl rfl)).elim
    | some buffer =>
        have bound : values.size ≤ buffer.length := by
          have : ¬buffer.length < values.size := fun h => needed (Or.inr h)
          omega
        obtain ⟨finish, count, footprint, filled, finalArena, cursor, counted, bounded⟩ :=
          fill_exists_regions values (requestView buffer values.size) values.size
            (Nat.le_refl _) current (valid_prefix (valid buffer rfl) bound) rfl
            writeCapacity smallArena separated lengthFits fits seed
        have run := SpaceRun.reuse (valid buffer rfl) bound filled
        refine ⟨some buffer, requestView buffer values.size, finish, count, footprint,
          run, run.source.observed.1, run.source.observed.2.1, ?_, ?_, finalArena, bounded⟩
        · simpa only [capacity, Complexity.GeometricCapacity.allocated_of_le bound,
            Nat.add_zero] using cursor
        · simpa only [steps, if_neg needed, Nat.zero_add] using counted

/-- A complete previous footprint inside the common region stays bounded by
the same region after preparation. Neither repeated writes nor repeated calls
add another copy of its heap prefix or stack interval. -/
theorem exists_space_le (values : Array Nat) (cache : Cache)
    (current : Session.State w heapLimit) (valid : Valid cache current.heap)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity Complexity.Language.Buffer.Prepare.writeProgram
      Complexity.Language.Buffer.Prepare.writeEntry w 0 heapLimit)
    (smallArena : ArenaRep current.placement current.cursor H current.heap current.entry)
    (separated : H ≤ heapLimit)
    (lengthFits : values.size < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (space : current.cursor +
      Complexity.GeometricCapacity.allocated (capacity cache) values.size ≤ H)
    (seed : Finset (Word w)) (seeded : seed ⊆ region w heapLimit H) :
    ∃ nextCache view finish count footprint,
      SpaceRun values cache current nextCache view finish count seed footprint ∧
      view.Contents finish.heap values ∧ Valid nextCache finish.heap ∧
      finish.cursor = current.cursor +
        Complexity.GeometricCapacity.allocated (capacity cache) values.size ∧
      count = steps cache values.size ∧
      ArenaRep finish.placement finish.cursor H finish.heap finish.entry ∧
      footprint ⊆ region w heapLimit H ∧ footprint.card ≤ H + frameWords := by
  obtain ⟨nextCache, view, finish, count, footprint, run, contents, valid, cursor,
      counted, finalArena, bounded⟩ :=
    exists_regions values cache current valid allocationCapacity writeCapacity smallArena
      separated lengthFits fits space seed
  have subset : footprint ⊆ region w heapLimit H :=
    bounded.trans (Finset.union_subset seeded (Finset.Subset.refl _))
  exact ⟨nextCache, view, finish, count, footprint, run, contents, valid, cursor,
    counted, finalArena, subset, (Finset.card_le_card subset).trans (region_card_le _ _ _)⟩


/-- Connect the actual preparation to the geometric reservation history.
The candidate's independent reservation and historical physical peak remain
explicit; only the loader's additional cells are bounded by four times the
largest request in the actual prefix. No future request size is consulted. -/
theorem exists_space_le_geometric (values : Array Nat) (cache : Cache)
    (current : Session.State w heapLimit) (valid : Valid cache current.heap)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity Complexity.Language.Buffer.Prepare.writeProgram
      Complexity.Language.Buffer.Prepare.writeEntry w 0 heapLimit)
    (capacities requests : Nat → Nat) (n candidateWords : Nat)
    (initial : capacities 0 = 0)
    (transitions : ∀ i, i < n + 1 →
      capacities (i + 1) = Complexity.GeometricCapacity.next (capacities i) (requests i))
    (cached : capacity cache = capacities n) (requested : values.size = requests n)
    (reserved : current.cursor ≤ candidateWords +
      ∑ i ∈ Finset.range n, Complexity.GeometricCapacity.allocated (capacities i) (requests i))
    (smallArena : ArenaRep current.placement current.cursor
      (candidateWords + 4 * (Finset.range (n + 1)).sup requests) current.heap current.entry)
    (separated : candidateWords + 4 * (Finset.range (n + 1)).sup requests ≤ heapLimit)
    (lengthFits : values.size < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (seed : Finset (Word w))
    (seeded : seed ⊆ region w heapLimit
      (candidateWords + 4 * (Finset.range (n + 1)).sup requests)) :
    ∃ nextCache view finish count footprint,
      SpaceRun values cache current nextCache view finish count seed footprint ∧
      view.Contents finish.heap values ∧ Valid nextCache finish.heap ∧
      count = steps cache values.size ∧
      ArenaRep finish.placement finish.cursor
        (candidateWords + 4 * (Finset.range (n + 1)).sup requests) finish.heap finish.entry ∧
      finish.cursor ≤ candidateWords +
        ∑ i ∈ Finset.range (n + 1),
          Complexity.GeometricCapacity.allocated (capacities i) (requests i) ∧
      footprint ⊆ region w heapLimit
        (candidateWords + 4 * (Finset.range (n + 1)).sup requests) ∧
      footprint.card ≤ candidateWords +
        4 * (Finset.range (n + 1)).sup requests + frameWords := by
  have nextReserved : current.cursor +
      Complexity.GeometricCapacity.allocated (capacity cache) values.size ≤
      candidateWords + ∑ i ∈ Finset.range (n + 1),
        Complexity.GeometricCapacity.allocated (capacities i) (requests i) := by
    rw [Finset.sum_range_succ, cached, requested]
    exact (Nat.add_le_add_right reserved _).trans_eq (Nat.add_assoc _ _ _)
  have geometric := Complexity.GeometricCapacity.sum_allocated_le_four_mul_sup
    initial transitions
  have space := nextReserved.trans (Nat.add_le_add_left geometric candidateWords)
  obtain ⟨nextCache, view, finish, count, footprint, run, contents, valid, cursor,
      counted, finalArena, bounded, cardinality⟩ :=
    exists_space_le values cache current valid allocationCapacity writeCapacity smallArena
      separated lengthFits fits space seed seeded
  exact ⟨nextCache, view, finish, count, footprint, run, contents, valid,
    counted, finalArena, by simpa only [cursor] using nextReserved, bounded, cardinality⟩

end Ram.LanguageCompiler.Buffer.PrepareReuse
