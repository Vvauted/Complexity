/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution

/-!
# Persistent sessions of compiled source calls

The same source session is realized by actual allocation-aware RAM invocations.
Every continuation retains the preceding invocation's complete memory projection,
heap, placement and allocation cursor. Returned state words become the next
call's state arguments; mathematical state reconstruction is not an input path.

The cost is the sum of these preloaded invocations, including their call/return
wrappers and final halts. Input preparation, the initial arena bootstrap, and an
external streaming driver remain separate boundaries. This is not yet a theorem
about one continuously running I/O program. Source correctness is independent of
these machine readiness and resource conditions.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

/-- Actual persistent memory together with its source heap representation. -/
structure State (w heapLimit : Nat) where
  heap : Heap
  placement : Nat → Word w
  cursor : Nat
  entry : Source.State w
  arena : ArenaRep placement cursor heapLimit heap entry

/-- Continue from an invocation's actual returned memory, including private words. -/
def State.ofExecution {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth heapLimit : Nat} {placement : Nat → Word w}
    {args : Env signatures[fn].params} {heap : Heap} {entry : Source.State w}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry) :
    State w heapLimit :=
  ⟨outcome.heap, outcome.finalPlacement, outcome.cursor, outcome.nextEntry, outcome.memory⟩

private theorem envWords_cast {Γ Δ : List Ty} (same : Γ = Δ)
    (placement : Nat → Word w) (args : Env Γ) :
    envWords placement (cast (congrArg Env same) args) = envWords placement args := by
  cases same
  rfl

private theorem valueWords_cast {α β : Ty} (same : α = β)
    (placement : Nat → Word w) (value : Value α) :
    valueWords placement (cast (congrArg Value same) value) =
      valueWords placement value := by
  cases same
  rfl

variable {configuration request : List Ty} {response : Ty}
variable (session : Complexity.Language.Session configuration request response)
variable {w heapLimit : Nat}

/-- Signature transport preserves the actual state and request word sequence. -/
@[simp] theorem stepArgs_words (placement : Nat → Word w)
    (state : Value session.stateTy) (input : Env request) :
    envWords placement (session.stepArgs state input) =
      valueWords placement state ++ envWords placement input := by
  exact (envWords_cast (congrArg Signature.params session.step_signature).symm
    placement (Env.cons state input)).trans (envWords_cons placement state input)

/-- Initialization returns the state's actual representation. -/
@[simp] theorem initValue_words (placement : Nat → Word w)
    (state : Value session.stateTy) :
    valueWords placement (session.initValue state) = valueWords placement state := by
  exact valueWords_cast (congrArg Signature.result session.init_signature).symm placement state

/-- Reply words precede the retained state words in the actual returned value. -/
@[simp] theorem stepValue_words (placement : Nat → Word w)
    (reply : Value response) (state : Value session.stateTy) :
    valueWords placement (session.stepValue reply state) =
      valueWords placement reply ++ valueWords placement state := by
  exact (valueWords_cast (congrArg Signature.result session.step_signature).symm
    placement (reply, state)).trans (valueWords_prod placement reply state)

/-- The first step consumes the initializer's actual returned state words. -/
theorem init_next_words {depth : Nat} {current : State w heapLimit}
    {args : Env configuration} {state : Value session.stateTy}
    (outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry)
    (returned : outcome.value = session.initValue state) (input : Env request) :
    envWords outcome.finalPlacement (session.stepArgs state input) =
      LocalCompiler.Function.returnedValues
        (fieldCount session.signatures[session.init].result) outcome.result.state ++
      envWords outcome.finalPlacement input := by
  have words : LocalCompiler.Function.returnedValues
      (fieldCount session.signatures[session.init].result) outcome.result.state =
      valueWords outcome.finalPlacement outcome.value := outcome.returned
  rw [words, returned, stepArgs_words, initValue_words]

/-- A continuation takes state words from the previous RAM return, not an encoder
of a mathematical state. The discarded prefix is exactly the reply fields. -/
theorem step_next_words {depth : Nat} {current : State w heapLimit}
    {state next : Value session.stateTy} {input : Env request} {reply : Value response}
    (outcome : FunctionArenaExecution session.program session.step depth heapLimit
      current.placement (session.stepArgs state input) current.heap current.entry)
    (returned : outcome.value = session.stepValue reply next) (nextInput : Env request) :
    envWords outcome.finalPlacement (session.stepArgs next nextInput) =
      (LocalCompiler.Function.returnedValues
        (fieldCount session.signatures[session.step].result) outcome.result.state).drop
          (fieldCount response) ++ envWords outcome.finalPlacement nextInput := by
  have words : LocalCompiler.Function.returnedValues
      (fieldCount session.signatures[session.step].result) outcome.result.state =
      valueWords outcome.finalPlacement outcome.value := outcome.returned
  rw [words, returned, stepArgs_words, stepValue_words]
  simp

/-- Successful steps thread actual source and RAM memory. The index counts the
sum of complete preloaded invocations, not external input/driver work. -/
inductive Run : Value session.stateTy → State w heapLimit → List (Env request) →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat → Prop
  | nil (state memory) : Run state memory [] [] state memory 0
  | cons {state current input reply next inputs replies finish finalMemory steps depth}
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        current.placement (session.stepArgs state input) current.heap current.entry)
      (returned : outcome.value = session.stepValue reply next)
      (rest : Run next (State.ofExecution outcome) inputs replies finish finalMemory steps) :
      Run state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (outcome.result.steps + steps)

/-- Initialize once and then resume the same session, retaining initialization's
actual instruction count even when no request follows. -/
def Runs (args : Env configuration) (current : State w heapLimit)
    (inputs : List (Env request)) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      ∃ remaining, Run session state (State.ofExecution outcome) inputs replies
        finish finalMemory remaining ∧ steps = outcome.result.steps + remaining

variable {session}

/-- Erasing machine evidence recovers the original independent source session. -/
theorem Run.source
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)} {steps : Nat}
    (run : Run session state current inputs replies finish finalMemory steps) :
    session.Run state current.heap inputs replies finish finalMemory.heap := by
  induction run with
  | nil => exact .nil _ _
  | cons outcome returned rest ih =>
      exact .cons (by
        unfold Complexity.Language.Session.Step
        simpa only [returned] using outcome.source) ih

/-- The initialized RAM trace has exactly the source meaning of the same entries. -/
theorem Runs.source
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat}
    (run : Runs session args current inputs replies finish finalMemory steps) :
    session.Runs args current.heap inputs replies finish finalMemory.heap := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, _⟩ := run
  refine ⟨state, outcome.heap, ?_, rest.source⟩
  unfold Complexity.Language.Session.Starts
  simpa only [returned] using outcome.source

/-- Concatenation preserves actual boundary memory and adds the actual costs. -/
theorem Run.append
    {state middle finish : Value session.stateTy}
    {current intermediate finalMemory : State w heapLimit}
    {inputs₁ inputs₂ : List (Env request)}
    {replies₁ replies₂ : List (Value response × Heap)} {steps₁ steps₂ : Nat}
    (first : Run session state current inputs₁ replies₁ middle intermediate steps₁)
    (second : Run session middle intermediate inputs₂ replies₂ finish finalMemory steps₂) :
    Run session state current (inputs₁ ++ inputs₂) (replies₁ ++ replies₂)
      finish finalMemory (steps₁ + steps₂) := by
  induction first with
  | nil => simpa only [List.nil_append, Nat.zero_add] using second
  | cons outcome returned rest ih =>
      simpa only [List.cons_append, Nat.add_assoc] using
        Run.cons outcome returned (ih second)

/-- An ordinary bound can be weakened without changing the underlying trace. -/
theorem Runs.mono
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {budget larger : Nat}
    (bounded : ∃ steps ≤ budget, Runs session args current inputs replies finish finalMemory steps)
    (le : budget ≤ larger) :
    ∃ steps ≤ larger, Runs session args current inputs replies finish finalMemory steps := by
  obtain ⟨steps, bound, run⟩ := bounded
  exact ⟨steps, bound.trans le, run⟩

end Ram.LanguageCompiler.Session
