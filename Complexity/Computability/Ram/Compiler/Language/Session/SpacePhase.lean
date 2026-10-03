/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Space
import Complexity.Computability.Ram.Compiler.Language.Session.Bounded

/-!
# Phase observations on the same accumulated session footprint

A phase condition observes the actual invocation count and the complete physical
footprint after that invocation. Space is cumulative from the original seed,
not a per-call reset. A time condition may separately bound each invocation.
Initialization has its own condition on its real count and footprint, including
when no request follows. These conditions are proof obligations only: they do
not execute, allocate or annotate an alternative resource semantics.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language
universe u
variable {ι : Type u} {configuration request : List Ty} {response : Ty}
variable {w heapLimit : Nat}
variable (session : Complexity.Language.Session configuration request response)
variable (encode : ι → Env request)
variable (phase : ι → Nat → Finset (Word w) → Prop)

/-- Each actual callback satisfies its fixed phase condition while retaining all
earlier physical words. The final index still counts only actual instructions. -/
inductive PhaseSpaceRun : Value session.stateTy → State w heapLimit → List ι →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat →
    Finset (Word w) → Finset (Word w) → Prop
  | nil (state memory seed) : PhaseSpaceRun state memory [] [] state memory 0 seed seed
  | cons {state current input reply next inputs replies finish finalMemory steps depth
      seed footprint}
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        current.placement (session.stepArgs state (encode input)) current.heap current.entry)
      (returned : outcome.value = session.stepValue reply next)
      (bounded : phase input outcome.result.steps (seed ∪ outcome.heapAccesses))
      (rest : PhaseSpaceRun next (State.ofExecution outcome) inputs replies finish finalMemory
        steps (seed ∪ outcome.heapAccesses) footprint) :
      PhaseSpaceRun state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (outcome.result.steps + steps) seed footprint

/-- Independent initializer and callback conditions share one actual execution
and physical-word history. Unused initialization time is not callback credit. -/
def PhaseSpaceRuns (initial : Nat → Finset (Word w) → Prop)
    (args : Env configuration) (current : State w heapLimit)
    (inputs : List ι) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      initial outcome.result.steps (seed ∪ outcome.heapAccesses) ∧
      ∃ remaining, PhaseSpaceRun session encode phase state (State.ofExecution outcome)
        inputs replies finish finalMemory remaining (seed ∪ outcome.heapAccesses) footprint ∧
        steps = outcome.result.steps + remaining

variable {session encode phase}

/-- Erasure retains the same actual accesses and count. -/
theorem PhaseSpaceRun.erase
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRun session encode phase state current inputs replies finish finalMemory
      steps seed footprint) :
    SpaceRun session state current (inputs.map encode) replies finish finalMemory
      steps seed footprint := by
  induction run with
  | nil => exact .nil _ _ _
  | cons outcome returned bounded rest ih => exact .cons outcome returned ih

/-- Initialization and every callback preserve the original exact footprint. -/
theorem PhaseSpaceRuns.erase
    {initial : Nat → Finset (Word w) → Prop}
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRuns session encode phase initial args current inputs replies finish
      finalMemory steps seed footprint) :
    SpaceRuns session args current (inputs.map encode) replies finish finalMemory
      steps seed footprint := by
  obtain ⟨depth, state, outcome, returned, bounded, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, remaining, rest.erase, counted⟩

/-- Time envelopes obtained from phase conditions concern those very same
callbacks, not a second run with independently chosen results or memory. -/
theorem PhaseSpaceRun.bounded
    {budget : ι → Nat}
    (condition : ∀ input steps footprint, phase input steps footprint → steps ≤ budget input)
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRun session encode phase state current inputs replies finish finalMemory
      steps seed footprint) :
    BoundedRun session encode budget state current inputs replies finish finalMemory steps := by
  induction run with
  | nil => exact .nil _ _
  | cons outcome returned bounded rest ih =>
      exact .cons outcome returned (condition _ _ _ bounded) ih

/-- Both phase time envelopes project to the existing counted invocation
relation while retaining the initializer and callback outcomes. -/
theorem PhaseSpaceRuns.bounded
    {initial : Nat → Finset (Word w) → Prop} {initBound : Nat} {budget : ι → Nat}
    (initial_condition : ∀ steps footprint, initial steps footprint → steps ≤ initBound)
    (step_condition : ∀ input steps footprint, phase input steps footprint →
      steps ≤ budget input)
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRuns session encode phase initial args current inputs replies finish
      finalMemory steps seed footprint) :
    BoundedRuns session encode budget initBound args current inputs replies finish finalMemory
      steps := by
  obtain ⟨depth, state, outcome, returned, bounded, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, initial_condition _ _ bounded, remaining,
    rest.bounded step_condition, counted⟩

/-- Weaken a callback condition without changing memory or physical words. -/
theorem PhaseSpaceRun.mono
    {phase' : ι → Nat → Finset (Word w) → Prop}
    (condition : ∀ input steps footprint, phase input steps footprint →
      phase' input steps footprint)
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRun session encode phase state current inputs replies finish finalMemory
      steps seed footprint) :
    PhaseSpaceRun session encode phase' state current inputs replies finish finalMemory
      steps seed footprint := by
  induction run with
  | nil => exact .nil _ _ _
  | cons outcome returned bounded rest ih =>
      exact .cons outcome returned (condition _ _ _ bounded) ih

/-- Initial and callback conditions can both be weakened on the same trace. -/
theorem PhaseSpaceRuns.mono
    {initial initial' : Nat → Finset (Word w) → Prop}
    {phase' : ι → Nat → Finset (Word w) → Prop}
    (initial_condition : ∀ steps footprint, initial steps footprint → initial' steps footprint)
    (step_condition : ∀ input steps footprint, phase input steps footprint →
      phase' input steps footprint)
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PhaseSpaceRuns session encode phase initial args current inputs replies finish
      finalMemory steps seed footprint) :
    PhaseSpaceRuns session encode phase' initial' args current inputs replies finish
      finalMemory steps seed footprint := by
  obtain ⟨depth, state, outcome, returned, bounded, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, initial_condition _ _ bounded, remaining,
    rest.mono step_condition, counted⟩

end Ram.LanguageCompiler.Session
