/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Computability.Ram.Execution.Space

/-!
# Physical word footprints of persistent sessions

The footprint starts with an explicitly fixed finite set of resident physical
words and accumulates the actual heap accesses of every complete invocation.
Union, rather than summing per-call cardinalities, counts reused addresses once.
Initialization, call frames and transient scratch accesses belong to the same
footprint; the actual returned heap, placement and cursor feed every next call.

This is cumulative physical-word space, not heap capacity, allocation volume or
exact reachable-live space. Registers, code, I/O and an external driver are not
included. The seed is fixed by the entry boundary, never chosen from a desired
answer or from the session's hidden future. No machine budget is required to
state independent source correctness.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

variable {configuration request : List Ty} {response : Ty}
variable (session : Complexity.Language.Session configuration request response)
variable {w heapLimit : Nat}

/-- The same persistent callback trace with an exact accumulated physical
footprint. The final footprint is an index determined by the real invocations. -/
inductive SpaceRun : Value session.stateTy → State w heapLimit → List (Env request) →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat →
    Finset (Word w) → Finset (Word w) → Prop
  | nil (state memory seed) : SpaceRun state memory [] [] state memory 0 seed seed
  | cons {state current input reply next inputs replies finish finalMemory steps depth
      seed footprint}
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        current.placement (session.stepArgs state input) current.heap current.entry)
      (returned : outcome.value = session.stepValue reply next)
      (rest : SpaceRun next (State.ofExecution outcome) inputs replies finish finalMemory
        steps (seed ∪ outcome.heapAccesses) footprint) :
      SpaceRun state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (outcome.result.steps + steps) seed footprint

/-- Count initialization once and retain its accessed words even on an empty
request history. The initializer runs on the given actual entry memory. -/
def SpaceRuns (args : Env configuration) (current : State w heapLimit)
    (inputs : List (Env request)) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      ∃ remaining, SpaceRun session state (State.ofExecution outcome) inputs replies
        finish finalMemory remaining (seed ∪ outcome.heapAccesses) footprint ∧
        steps = outcome.result.steps + remaining

variable {session}

/-- Forget only the physical observation, retaining the exact counted trace. -/
theorem SpaceRun.erase
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : SpaceRun session state current inputs replies finish finalMemory steps seed footprint) :
    Run session state current inputs replies finish finalMemory steps := by
  induction run with
  | nil => exact .nil _ _
  | cons outcome returned rest ih => exact .cons outcome returned ih

/-- The same initialized execution, not a separately selected successful run. -/
theorem SpaceRuns.erase
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRuns session args current inputs replies finish finalMemory steps seed footprint) :
    Runs session args current inputs replies finish finalMemory steps := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, remaining, rest.erase, counted⟩

/-- No callback can discard previously resident or accessed physical words. -/
theorem SpaceRun.seed_subset
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : SpaceRun session state current inputs replies finish finalMemory steps seed footprint) :
    seed ⊆ footprint := by
  induction run with
  | nil => exact fun _ member => member
  | cons outcome returned rest ih =>
      exact fun _ member => ih (Finset.mem_union.mpr (Or.inl member))

/-- The entry footprint remains included after initialization and all calls. -/
theorem SpaceRuns.seed_subset
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRuns session args current inputs replies finish finalMemory steps seed footprint) :
    seed ⊆ footprint := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact fun _ member => rest.seed_subset (Finset.mem_union.mpr (Or.inl member))

/-- Concatenate at the real intermediate memory, carrying the first phase's
complete footprint into the second. Reused addresses are never summed twice. -/
theorem SpaceRun.append
    {state middle finish : Value session.stateTy}
    {current intermediate finalMemory : State w heapLimit}
    {inputs₁ inputs₂ : List (Env request)}
    {replies₁ replies₂ : List (Value response × Heap)} {steps₁ steps₂ : Nat}
    {seed middleFootprint finalFootprint : Finset (Word w)}
    (first : SpaceRun session state current inputs₁ replies₁ middle intermediate
      steps₁ seed middleFootprint)
    (second : SpaceRun session middle intermediate inputs₂ replies₂ finish finalMemory
      steps₂ middleFootprint finalFootprint) :
    SpaceRun session state current (inputs₁ ++ inputs₂) (replies₁ ++ replies₂)
      finish finalMemory (steps₁ + steps₂) seed finalFootprint := by
  induction first with
  | nil => simpa only [List.nil_append, Nat.zero_add] using second
  | cons outcome returned rest ih =>
      simpa only [List.cons_append, Nat.add_assoc] using
        SpaceRun.cons outcome returned (ih second)

/-- Any given callback trace has its actual finite footprint; observing space
does not require a different implementation or a proposed space bound. -/
theorem Run.withSpace
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)} {steps : Nat}
    (run : Run session state current inputs replies finish finalMemory steps)
    (seed : Finset (Word w)) :
    ∃ footprint, SpaceRun session state current inputs replies finish finalMemory
      steps seed footprint := by
  induction run generalizing seed with
  | nil => exact ⟨seed, .nil _ _ _⟩
  | cons outcome returned rest ih =>
      obtain ⟨footprint, observed⟩ := ih (seed ∪ outcome.heapAccesses)
      exact ⟨footprint, .cons outcome returned observed⟩

/-- Observe physical words of the given initialized counted execution. -/
theorem Runs.withSpace
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat}
    (run : Runs session args current inputs replies finish finalMemory steps)
    (seed : Finset (Word w)) :
    ∃ footprint, SpaceRuns session args current inputs replies finish finalMemory
      steps seed footprint := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  obtain ⟨footprint, observed⟩ := rest.withSpace (seed ∪ outcome.heapAccesses)
  exact ⟨footprint, depth, state, outcome, returned, remaining, observed, counted⟩

/-- Physical-word observation erases to the same independent source trace. -/
theorem SpaceRuns.source
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRuns session args current inputs replies finish finalMemory steps seed footprint) :
    session.Runs args current.heap inputs replies finish finalMemory.heap :=
  run.erase.source

/-- Continue an initialized session without repeating initialization or resetting
its resident footprint. The boundary memory is exactly the first run's return. -/
theorem SpaceRuns.append
    {args : Env configuration} {state finish : Value session.stateTy}
    {current intermediate finalMemory : State w heapLimit}
    {inputs₁ inputs₂ : List (Env request)}
    {replies₁ replies₂ : List (Value response × Heap)} {steps₁ steps₂ : Nat}
    {seed middleFootprint finalFootprint : Finset (Word w)}
    (first : SpaceRuns session args current inputs₁ replies₁ state intermediate
      steps₁ seed middleFootprint)
    (second : SpaceRun session state intermediate inputs₂ replies₂ finish finalMemory
      steps₂ middleFootprint finalFootprint) :
    SpaceRuns session args current (inputs₁ ++ inputs₂) (replies₁ ++ replies₂)
      finish finalMemory (steps₁ + steps₂) seed finalFootprint := by
  obtain ⟨depth, startState, outcome, returned, remaining, rest, counted⟩ := first
  refine ⟨depth, startState, outcome, returned, remaining + steps₂,
    rest.append second, ?_⟩
  omega

/-- Weaken a word budget without altering the observed execution or footprint. -/
theorem SpaceRuns.mono
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed : Finset (Word w)}
    {budget larger : Nat}
    (bounded : ∃ footprint, SpaceRuns session args current inputs replies finish finalMemory
      steps seed footprint ∧ footprint.card ≤ budget)
    (le : budget ≤ larger) :
    ∃ footprint, SpaceRuns session args current inputs replies finish finalMemory
      steps seed footprint ∧ footprint.card ≤ larger := by
  obtain ⟨footprint, run, bound⟩ := bounded
  exact ⟨footprint, run, bound.trans le⟩

end Ram.LanguageCompiler.Session
