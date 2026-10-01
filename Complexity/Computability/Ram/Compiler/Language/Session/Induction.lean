/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session

/-!
# Finite composition of actual session invocation bounds

An invariant describes both the actual retained source value and the represented
RAM memory. A step premise supplies an existing FunctionArenaExecution of the
selected session entry, its actual returned value, invariant preservation at
State.ofExecution, and a bound on its actual instruction count. List induction
only joins these witnesses through Session.Run and adds their counts.

The step premise receives the current request, never the remaining request
sequence. Admissibility and the per-request budget are proof-side conditions,
not additional arguments or data for the source program. Source correctness and
termination still have their independent budget-free Session relations; these
theorems compose separately established machine-resource facts.

Costs remain sums of preloaded invocations. Input preparation, the initial arena
bootstrap and an external streaming/I/O driver are not priced by this module.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

variable {configuration request : List Ty} {response : Ty}
variable {session : Complexity.Language.Session configuration request response}
variable {w heapLimit : Nat}

/-- Compose successful actual steps at their returned memories. The numeric bound
is the sum of the supplied current-request bounds, including an empty sequence. -/
theorem Run.exists_le_of_step
    (invariant : Value session.stateTy → State w heapLimit → Prop)
    (admissible : Env request → Prop) (budget : Env request → Nat)
    (step : ∀ (state : Value session.stateTy) (current : State w heapLimit)
      (input : Env request), invariant state current → admissible input →
      ∃ (depth : Nat) (reply : Value response) (next : Value session.stateTy),
        ∃ outcome : FunctionArenaExecution session.program session.step depth heapLimit
          current.placement (session.stepArgs state input) current.heap current.entry,
          outcome.value = session.stepValue reply next ∧
            invariant next (State.ofExecution outcome) ∧
            outcome.result.steps ≤ budget input)
    {state : Value session.stateTy} {current : State w heapLimit}
    (initial : invariant state current) (inputs : List (Env request))
    (legal : ∀ input ∈ inputs, admissible input) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalMemory : State w heapLimit) (steps : Nat),
      Run session state current inputs replies finish finalMemory steps ∧
        invariant finish finalMemory ∧ steps ≤ (inputs.map budget).sum := by
  induction inputs generalizing state current with
  | nil =>
      exact ⟨[], state, current, 0, Run.nil (session := session) state current,
        initial, Nat.le_refl 0⟩
  | cons input inputs ih =>
      obtain ⟨depth, reply, next, outcome, returned, preserved, cost⟩ :=
        step state current input initial (legal input (by simp))
      obtain ⟨replies, finish, finalMemory, steps, rest, final, bound⟩ :=
        ih preserved (fun input member => legal input (by simp [member]))
      refine ⟨(reply, outcome.heap) :: replies, finish, finalMemory,
        outcome.result.steps + steps,
        Run.cons (session := session) outcome returned rest, final, ?_⟩
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add cost bound

/-- Prepend one actual initializer to the finite step composition. Its own
instruction count is retained exactly, rather than treated as a free setup or
replaced by a mathematical state encoding. This also charges initialization when
the request list is empty. A proved bound for initialization can be added later
by ordinary transitivity. -/
theorem Runs.exists_le_of_step
    (invariant : Value session.stateTy → State w heapLimit → Prop)
    (admissible : Env request → Prop) (budget : Env request → Nat)
    (step : ∀ (state : Value session.stateTy) (current : State w heapLimit)
      (input : Env request), invariant state current → admissible input →
      ∃ (depth : Nat) (reply : Value response) (next : Value session.stateTy),
        ∃ outcome : FunctionArenaExecution session.program session.step depth heapLimit
          current.placement (session.stepArgs state input) current.heap current.entry,
          outcome.value = session.stepValue reply next ∧
            invariant next (State.ofExecution outcome) ∧
            outcome.result.steps ≤ budget input)
    {args : Env configuration} {current : State w heapLimit}
    {depth : Nat} {state : Value session.stateTy}
    (outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry)
    (returned : outcome.value = session.initValue state)
    (initial : invariant state (State.ofExecution outcome))
    (inputs : List (Env request)) (legal : ∀ input ∈ inputs, admissible input) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalMemory : State w heapLimit) (steps : Nat),
      Runs session args current inputs replies finish finalMemory steps ∧
        invariant finish finalMemory ∧
        steps ≤ outcome.result.steps + (inputs.map budget).sum := by
  obtain ⟨replies, finish, finalMemory, steps, run, final, bound⟩ :=
    Run.exists_le_of_step invariant admissible budget step initial inputs legal
  refine ⟨replies, finish, finalMemory, outcome.result.steps + steps,
    ?_, final, Nat.add_le_add_left bound _⟩
  exact ⟨depth, state, outcome, returned, steps, run, rfl⟩

end Ram.LanguageCompiler.Session
