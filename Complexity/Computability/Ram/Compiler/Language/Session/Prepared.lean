/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Language.Session.Prepared

/-!
# RAM sessions interleaved with current-input preparation

The client fixes a counted preparation relation, backed by actual executions
such as `List.Prepare.Run`. The candidate cannot choose this relation or its
prices. A generic relation alone does not certify an arbitrary loader's cost:
each concrete preparation must supply real execution evidence and source erasure.

After preparation the selected step starts from its actual resulting memory,
not the preceding callback's unextended heap. Costs include the preparation's
actual invocation sum and the callback. Word fitting is required for the
arguments that were really prepared. External transport, traversal and a
continuous register-saving driver remain separate from preloaded invocations.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

universe u
variable {ι : Type u} {configuration request : List Ty} {response : Ty}
variable {w heapLimit : Nat}
variable (session : Complexity.Language.Session configuration request response)
variable (prepare : ι → State w heapLimit → Env request → State w heapLimit → Nat → Prop)

/-- The real memory produced by current-input preparation feeds the source step.
The private state value is retained, never reconstructed from mathematical data. -/
inductive PreparedRun : Value session.stateTy → State w heapLimit → List ι →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat → Prop
  | nil (state current) : PreparedRun state current [] [] state current 0
  | cons {state current input args prepared preparationSteps reply next inputs replies
      finish finalMemory steps depth}
      (loaded : prepare input current args prepared preparationSteps)
      (fits : EnvFits w args)
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        prepared.placement (session.stepArgs state args) prepared.heap prepared.entry)
      (returned : outcome.value = session.stepValue reply next)
      (rest : PreparedRun next (State.ofExecution outcome) inputs replies finish finalMemory steps) :
      PreparedRun state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (preparationSteps + outcome.result.steps + steps)

/-- Initialization is counted exactly once, also when no request follows. -/
def PreparedRuns (args : Env configuration) (current : State w heapLimit)
    (inputs : List ι) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      ∃ remaining, PreparedRun session prepare state (State.ofExecution outcome)
        inputs replies finish finalMemory remaining ∧ steps = outcome.result.steps + remaining

variable {session prepare}
variable {sourcePrepare : ι → Heap → Env request → Heap → Prop}

/-- Erase the actual preparation and callback evidence, preserving their
intermediate heaps. The concrete loader supplies its source correspondence. -/
theorem PreparedRun.source
    (preparation_source : ∀ input current args prepared steps,
      prepare input current args prepared steps →
        sourcePrepare input current.heap args prepared.heap)
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    (run : PreparedRun session prepare state current inputs replies finish finalMemory steps) :
    session.PreparedRun sourcePrepare state current.heap inputs replies finish finalMemory.heap := by
  induction run with
  | nil => exact .nil _ _
  | cons loaded fits outcome returned rest ih =>
      refine .cons (preparation_source _ _ _ _ _ loaded) ?_ ih
      unfold Complexity.Language.Session.Step
      simpa only [returned] using outcome.source

/-- Project the same counted initialized trace, not a separately selected run. -/
theorem PreparedRuns.source
    (preparation_source : ∀ input current args prepared steps,
      prepare input current args prepared steps →
        sourcePrepare input current.heap args prepared.heap)
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat}
    (run : PreparedRuns session prepare args current inputs replies finish finalMemory steps) :
    session.PreparedRuns sourcePrepare args current.heap inputs replies finish finalMemory.heap := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, _⟩ := run
  refine ⟨state, outcome.heap, ?_, rest.source preparation_source⟩
  unfold Complexity.Language.Session.Starts
  simpa only [returned] using outcome.source

end Ram.LanguageCompiler.Session
