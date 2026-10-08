/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.PrepareReuse
import Complexity.Computability.Ram.Compiler.Language.Buffer.Prepare

/-!
# Counted reusable request preparation

The protocol's retained cache is an explicit input and output. Reuse invokes the
existing scalar writer on the actual cached allocation; growth invokes the
existing initialized allocator before those same writes. The actual returned
RAM state is threaded through every call. Candidate storage is never reset.

The prefix descriptor is a preloaded call argument, like the other scalar ports
of this preparation interface. External scheduling, traversal, descriptor
transport and growth-policy arithmetic are not charged as compiled source work.
-/

namespace Ram.LanguageCompiler.Buffer.PrepareReuse

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.PrepareReuse

variable {w heapLimit : Nat}

/-- Complete initialization and write counts for the fixed reuse policy. -/
def steps (cache : Cache) (length : Nat) : Nat :=
  (if NeedsGrowth cache length then
      Prepare.allocationSteps (Complexity.GeometricCapacity.next (capacity cache) length)
    else 0) + length * Prepare.writeSteps

/-- The actual cache allocation is retained, or replaced only by the actual
fresh initialized allocation selected by the public geometric policy. -/
inductive Run (values : Array Nat) : Cache → Session.State w heapLimit →
    Cache → Buffer .nat → Session.State w heapLimit → Nat → Prop
  | reuse {buffer current finish count}
      (valid : buffer.Valid current.heap) (fits : values.size ≤ buffer.length)
      (filled : Prepare.Fill values (requestView buffer values.size) values.size
        current finish count) :
      Run values (some buffer) current (some buffer) (requestView buffer values.size) finish count
  | grow {cache current}
      (needed : NeedsGrowth cache values.size)
      (allocated : FunctionArenaExecution Replicate.program Replicate.replicateNatId 0 heapLimit
        current.placement
        (Replicate.replicateNat_args
          (Complexity.GeometricCapacity.next (capacity cache) values.size) 0)
        current.heap current.entry)
      {finish count}
      (filled : Prepare.Fill values (requestView allocated.value values.size) values.size
        (Session.State.ofExecution allocated) finish count) :
      Run values cache current (some allocated.value) (requestView allocated.value values.size)
        finish (allocated.result.steps + count)

/-- Forget only finite-word execution data, retaining the same source writes,
cache descriptors and actual intermediate heaps. -/
theorem Run.source {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat} {count : Nat}
    (run : Run values cache current nextCache view finish count) :
    Complexity.Language.Buffer.PrepareReuse.Run values cache current.heap nextCache view
      finish.heap := by
  cases run with
  | reuse valid fits filled => exact .reuse valid fits filled.source
  | grow needed allocated filled => exact .grow needed allocated.source filled.source

/-- The source frame, mathematical request and cache shape all concern the
same counted realization. In particular, aliases to the current view may change. -/
theorem Run.observed {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat} {count : Nat}
    (run : Run values cache current nextCache view finish count) :
    view.Contents finish.heap values ∧ Valid nextCache finish.heap ∧
      current.heap.ShapeExtends finish.heap ∧ view.PreservesOutside current.heap finish.heap :=
  run.source.observed

/-- Realization needs only valid cache storage, scalar ranges and enough space
for the policy's actual fresh allocation. Reuse advances the cursor by zero. -/
theorem exists_le (values : Array Nat) (cache : Cache) (current : Session.State w heapLimit)
    (valid : Valid cache current.heap)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity Complexity.Language.Buffer.Prepare.writeProgram
      Complexity.Language.Buffer.Prepare.writeEntry w 0 heapLimit)
    (lengthFits : values.size < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (space : current.cursor +
      Complexity.GeometricCapacity.allocated (capacity cache) values.size ≤ heapLimit) :
    ∃ nextCache view finish count, Run values cache current nextCache view finish count ∧
      view.Contents finish.heap values ∧ Valid nextCache finish.heap ∧
      finish.cursor = current.cursor +
        Complexity.GeometricCapacity.allocated (capacity cache) values.size ∧
      count = steps cache values.size := by
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
    have space' : current.cursor + length ≤ heapLimit := by simpa only [amount] using space
    have bufferFits : length < 2 ^ w := by
      have := current.arena.limit_lt
      omega
    obtain ⟨allocated, bufferEq, heapEq, cursorEq, countEq⟩ :=
      Prepare.allocate length current allocationCapacity bufferFits space'
    have bufferValid : allocated.value.Valid allocated.heap := by
      rw [bufferEq, heapEq]
      exact current.heap.alloc_valid _ _
    have bound : values.size ≤ allocated.value.length := by
      rw [bufferEq]
      exact Complexity.GeometricCapacity.next_ge_request _ _
    obtain ⟨finish, count, filled, cursor, counted⟩ :=
      Prepare.Fill.exists_run values (requestView allocated.value values.size) values.size
        (Nat.le_refl _) (Session.State.ofExecution allocated)
        (valid_prefix bufferValid bound) rfl writeCapacity lengthFits fits
    have run := Run.grow needed allocated filled
    refine ⟨some allocated.value, requestView allocated.value values.size, finish,
      allocated.result.steps + count, run, run.observed.1, run.observed.2.1, ?_, ?_⟩
    · simpa only [length, amount] using cursor.trans cursorEq
    · rw [countEq, counted]
      simp only [steps, if_pos needed, length]
  · cases cache with
    | none => exact (needed (Or.inl rfl)).elim
    | some buffer =>
        have bound : values.size ≤ buffer.length := by
          have : ¬buffer.length < values.size := fun h => needed (Or.inr h)
          omega
        obtain ⟨finish, count, filled, cursor, counted⟩ :=
          Prepare.Fill.exists_run values (requestView buffer values.size) values.size
            (Nat.le_refl _) current (valid_prefix (valid buffer rfl) bound) rfl
            writeCapacity lengthFits fits
        have run := Run.reuse (valid buffer rfl) bound filled
        refine ⟨some buffer, requestView buffer values.size, finish, count, run,
          run.observed.1, run.observed.2.1, ?_, ?_⟩
        · simpa only [capacity, Complexity.GeometricCapacity.allocated_of_le bound,
            Nat.add_zero] using cursor
        · simpa only [steps, if_neg needed, Nat.zero_add] using counted

/-- Source-independent adapter for a single current array argument, with a
separate driver-owned cache rather than candidate-selected loading state. -/
def prepare (cache : Cache) (values : Array Nat) (current : Session.State w heapLimit)
    (args : Env [.buffer .nat]) (finish : Session.State w heapLimit)
    (nextCache : Cache) (count : Nat) : Prop :=
  Run values cache current nextCache args.head finish count

end Ram.LanguageCompiler.Buffer.PrepareReuse
