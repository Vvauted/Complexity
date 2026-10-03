/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Prepare
import Complexity.Computability.Ram.Execution.Space

/-!
# Physical space of the existing current-array preparation

Initialized allocation and every subsequent scalar write contribute their real
compiled accesses. The complete preceding footprint is retained, including
private call frames and all new input cells written by initialization. The
external array and grader storage are not installed as an uncharged source heap.
This is a cumulative physical-word observation, not peak reachable-live storage.
-/

namespace Ram.LanguageCompiler.Buffer.Prepare

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.Prepare

variable {w heapLimit : Nat}

/-- Existing scalar-write invocations with their actual cumulative footprint. -/
inductive SpaceFill (values : Array Nat) (buffer : Buffer .nat) :
    Nat → Session.State w heapLimit → Session.State w heapLimit → Nat →
      Finset (Word w) → Finset (Word w) → Prop
  | zero (current seed) : SpaceFill values buffer 0 current current 0 seed seed
  | succ {count current middle steps seed footprint}
      (rest : SpaceFill values buffer count current middle steps seed footprint)
      (bound : count < values.size)
      (outcome : FunctionArenaExecution writeProgram writeEntry 0 heapLimit
        middle.placement (writeArgs buffer count values[count]) middle.heap middle.entry) :
      SpaceFill values buffer (count + 1) current (Session.State.ofExecution outcome)
        (steps + outcome.result.steps) seed (footprint ∪ outcome.heapAccesses)

theorem SpaceFill.erase {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceFill values buffer count current finish steps seed footprint) :
    Fill values buffer count current finish steps := by
  induction run with
  | zero => exact .zero _
  | succ rest bound outcome ih => exact .succ ih bound outcome

theorem SpaceFill.seed_subset {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceFill values buffer count current finish steps seed footprint) :
    seed ⊆ footprint := by
  induction run with
  | zero => exact fun _ member => member
  | succ rest bound outcome ih => exact ih.trans Finset.subset_union_left

theorem Fill.withSpace {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    (run : Fill values buffer count current finish steps) (seed : Finset (Word w)) :
    ∃ footprint, SpaceFill values buffer count current finish steps seed footprint := by
  induction run with
  | zero => exact ⟨seed, .zero _ _⟩
  | succ rest bound outcome ih =>
      obtain ⟨footprint, observed⟩ := ih
      exact ⟨footprint ∪ outcome.heapAccesses, .succ observed bound outcome⟩

theorem SpaceFill.card_le {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceFill values buffer count current finish steps seed footprint) :
    footprint.card ≤ seed.card + steps := by
  induction run with
  | zero => simp
  | succ rest bound outcome ih =>
      have accessed : outcome.heapAccesses.card ≤ outcome.result.steps := by
        exact Ram.heapAccesses_card_le _ _ _
      exact (Finset.card_union_le _ _).trans
        ((Nat.add_le_add ih accessed).trans_eq (Nat.add_assoc _ _ _))

/-- The original allocator and writes; initialization is not omitted from space. -/
inductive SpaceRun (values : Array Nat) : Session.State w heapLimit →
    Buffer .nat → Session.State w heapLimit → Nat →
      Finset (Word w) → Finset (Word w) → Prop
  | intro (current : Session.State w heapLimit)
      (allocated : FunctionArenaExecution Replicate.program Replicate.replicateNatId 0 heapLimit
        current.placement (Replicate.replicateNat_args values.size 0) current.heap current.entry)
      {finish steps seed footprint}
      (filled : SpaceFill values allocated.value values.size (Session.State.ofExecution allocated)
        finish steps (seed ∪ allocated.heapAccesses) footprint) :
      SpaceRun values current allocated.value finish (allocated.result.steps + steps)
        seed footprint

theorem SpaceRun.erase {values : Array Nat} {buffer : Buffer .nat}
    {steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceRun values current buffer finish steps seed footprint) :
    Run values current buffer finish steps := by
  cases run with
  | intro allocated filled => exact .intro _ allocated filled.erase

theorem SpaceRun.seed_subset {values : Array Nat} {buffer : Buffer .nat}
    {steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceRun values current buffer finish steps seed footprint) :
    seed ⊆ footprint := by
  cases run with
  | intro allocated filled => exact Finset.subset_union_left.trans filled.seed_subset

theorem Run.withSpace {values : Array Nat} {buffer : Buffer .nat}
    {steps : Nat} {current finish : Session.State w heapLimit}
    (run : Run values current buffer finish steps) (seed : Finset (Word w)) :
    ∃ footprint, SpaceRun values current buffer finish steps seed footprint := by
  cases run with
  | intro allocated filled =>
      obtain ⟨footprint, observed⟩ := filled.withSpace (seed ∪ allocated.heapAccesses)
      exact ⟨footprint, .intro _ allocated observed⟩

/-- Conservative physical-word bound derived from the actual counted calls. -/
theorem SpaceRun.card_le {values : Array Nat} {buffer : Buffer .nat}
    {steps : Nat} {current finish : Session.State w heapLimit}
    {seed footprint : Finset (Word w)}
    (run : SpaceRun values current buffer finish steps seed footprint) :
    footprint.card ≤ seed.card + steps := by
  cases run with
  | intro allocated filled =>
      have accessed : allocated.heapAccesses.card ≤ allocated.result.steps := by
        exact Ram.heapAccesses_card_le _ _ _
      exact filled.card_le.trans
        ((Nat.add_le_add_right ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left accessed seed.card)) _).trans_eq (Nat.add_assoc _ _ _))

/-- Fixed single-buffer request preparation using the original current array. -/
def prepare (values : Array Nat) (current : Session.State w heapLimit)
    (args : Env [.buffer .nat]) (finish : Session.State w heapLimit) (steps : Nat) : Prop :=
  Run values current args.head finish steps

/-- Physical-space adapter determined by allocation and actual write invocations. -/
def prepareSpace (values : Array Nat) (current : Session.State w heapLimit)
    (args : Env [.buffer .nat]) (finish : Session.State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  SpaceRun values current args.head finish steps seed footprint

theorem prepareSpace_erase {values : Array Nat} {args : Env [.buffer .nat]}
    {current finish : Session.State w heapLimit} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : prepareSpace values current args finish steps seed footprint) :
    prepare values current args finish steps := run.erase

/-- Erase directly to the already established source allocation/write loader. -/
theorem prepareSpace_source {values : Array Nat} {args : Env [.buffer .nat]}
    {current finish : Session.State w heapLimit} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : prepareSpace values current args finish steps seed footprint) :
    Complexity.Language.Buffer.Prepare.Run values current.heap args.head finish.heap :=
  run.erase.source

theorem prepareSpace_seed_subset {values : Array Nat} {args : Env [.buffer .nat]}
    {current finish : Session.State w heapLimit} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : prepareSpace values current args finish steps seed footprint) :
    seed ⊆ footprint := run.seed_subset

/-- Reuse the existing loader's initialized allocation and every charged write.
The space bound belongs to that realized preparation, not a separate witness. -/
theorem exists_space_le (values : Array Nat) (current : Session.State w heapLimit)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity writeProgram writeEntry w 0 heapLimit)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (space : current.cursor + values.size ≤ heapLimit) (seed : Finset (Word w)) :
    ∃ buffer finish steps footprint,
      SpaceRun values current buffer finish steps seed footprint ∧
      buffer.Contents finish.heap values ∧ finish.cursor = current.cursor + values.size ∧
      footprint.card ≤ seed.card + allocationSteps values.size + values.size * writeSteps := by
  obtain ⟨buffer, finish, steps, run, represented, cursor, counted⟩ :=
    exists_le values current allocationCapacity writeCapacity fits space
  obtain ⟨footprint, actual⟩ := run.withSpace seed
  refine ⟨buffer, finish, steps, footprint, actual, represented, cursor, ?_⟩
  simpa only [counted, Nat.add_assoc] using actual.card_le

end Ram.LanguageCompiler.Buffer.Prepare
