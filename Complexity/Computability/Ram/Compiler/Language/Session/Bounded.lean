/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session

/-!
# Separate bounds for actual session invocations

These proof relations decorate the existing session execution with a bound for
each actual invocation. Each step retains its FunctionArenaExecution, actual
returned state, heap, placement, allocation cursor and memory. Erasing the bounds
recovers Session.Run or Session.Runs with the same replies and exact total count.

Initialization has a separate bound: unused initialization budget cannot pay for
an expensive first request. Request encodings and budgets are fixed parameters;
the selected source entry receives only the current encoded request and retained
state. These relations neither evaluate requests nor reconstruct private state.
They charge preloaded invocations, not input loading, initial arena preparation
or an external streaming/I/O driver. Budget-free source correctness remains in
Complexity.Language.Session.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

universe u

variable {configuration request : List Ty} {response : Ty} {ι : Type u}
variable (session : Complexity.Language.Session configuration request response)
variable (encode : ι → Env request) (budget : ι → Nat)
variable {w heapLimit : Nat}

/-- An actual persistent RAM trace with a separate bound on every invocation.
The final index is the sum of actual instruction counts, not of the budgets. -/
inductive BoundedRun : Value session.stateTy → State w heapLimit → List ι →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat → Prop
  | nil (state memory) : BoundedRun state memory [] [] state memory 0
  | cons {state current input reply next inputs replies finish finalMemory steps depth}
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        current.placement (session.stepArgs state (encode input)) current.heap current.entry)
      (returned : outcome.value = session.stepValue reply next)
      (cost : outcome.result.steps ≤ budget input)
      (rest : BoundedRun next (State.ofExecution outcome) inputs replies
        finish finalMemory steps) :
      BoundedRun state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (outcome.result.steps + steps)

/-- Initialize once with its own bound, then execute separately bounded requests.
The same initializer supplies the retained state, memory and actual setup cost. -/
def BoundedRuns (initBound : Nat) (args : Env configuration) (current : State w heapLimit)
    (inputs : List ι) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧ outcome.result.steps ≤ initBound ∧
      ∃ remaining, BoundedRun session encode budget state (State.ofExecution outcome)
        inputs replies finish finalMemory remaining ∧ steps = outcome.result.steps + remaining

variable {session encode budget}

/-- Forgetting the per-request bounds preserves the exact actual RAM trace. -/
theorem BoundedRun.run
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    (bounded : BoundedRun session encode budget state current inputs replies
      finish finalMemory steps) :
    Run session state current (inputs.map encode) replies finish finalMemory steps := by
  induction bounded with
  | nil => exact Run.nil (session := session) _ _
  | cons outcome returned cost rest ih =>
      exact Run.cons (session := session) outcome returned ih

/-- The sum of actual invocation counts is bounded by the sum of their bounds. -/
theorem BoundedRun.steps_le
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    (bounded : BoundedRun session encode budget state current inputs replies
      finish finalMemory steps) :
    steps ≤ (inputs.map budget).sum := by
  induction bounded with
  | nil => exact Nat.le_refl 0
  | cons outcome returned cost rest ih =>
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add cost ih

/-- Forgetting both phase bounds retains the same initialized execution and cost. -/
theorem BoundedRuns.runs
    {initBound : Nat} {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat}
    (bounded : BoundedRuns session encode budget initBound args current inputs replies
      finish finalMemory steps) :
    Runs session args current (inputs.map encode) replies finish finalMemory steps := by
  obtain ⟨depth, state, outcome, returned, cost, remaining, rest, total⟩ := bounded
  exact ⟨depth, state, outcome, returned, remaining, rest.run, total⟩

/-- Add the separately proved initialization and request bounds. Initialization
is still charged when the request sequence is empty. -/
theorem BoundedRuns.steps_le
    {initBound : Nat} {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat}
    (bounded : BoundedRuns session encode budget initBound args current inputs replies
      finish finalMemory steps) :
    steps ≤ initBound + (inputs.map budget).sum := by
  obtain ⟨depth, state, outcome, returned, cost, remaining, rest, total⟩ := bounded
  rw [total]
  exact Nat.add_le_add cost rest.steps_le

end Ram.LanguageCompiler.Session
