/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared
import Complexity.Language.Session.Prepared.Stateful

/-!
# Physical prepared sessions with retained loader state

The loader's state is threaded explicitly across real preparation and callback
executions. Both see the preceding operation's actual memory. Initialization
uses a fixed cache; no later step may choose a fresh cache independently.

The fixed concrete loader provides its counted execution and source projection.
Accumulated physical addresses cannot be forgotten, including across buffer
reuse. This relation observes existing executions, not a new evaluator or an
unchecked assignment of prices to a preparation function.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

universe u v
variable {ι : Type u} {δ : Type v}
variable {configuration request : List Ty} {response : Ty}
variable {w heapLimit : Nat}
variable (session : Complexity.Language.Session configuration request response)
variable (prepareSpace : δ → ι → State w heapLimit → Env request →
  State w heapLimit → δ → Nat → Finset (Word w) → Finset (Word w) → Prop)

/-- The exact cache and memory returned by a loader are retained across the
callback; actual preparation and callback steps share one physical footprint. -/
inductive StatefulPreparedSpaceRun : δ → Value session.stateTy → State w heapLimit →
    List ι → List (Value response × Heap) → δ → Value session.stateTy →
    State w heapLimit → Nat → Finset (Word w) → Finset (Word w) → Prop
  | nil (cache state current seed) :
      StatefulPreparedSpaceRun cache state current [] [] cache state current 0 seed seed
  | cons {cache state current input args prepared nextCache preparationSteps reply next
      inputs replies finalCache finish finalMemory steps depth seed preparedFootprint footprint}
      (loaded : prepareSpace cache input current args prepared nextCache
        preparationSteps seed preparedFootprint)
      (retained : seed ⊆ preparedFootprint)
      (fits : EnvFits w args)
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        prepared.placement (session.stepArgs state args) prepared.heap prepared.entry)
      (returned : outcome.value = session.stepValue reply next)
      (rest : StatefulPreparedSpaceRun nextCache next (State.ofExecution outcome)
        inputs replies finalCache finish finalMemory steps
        (preparedFootprint ∪ outcome.heapAccesses) footprint) :
      StatefulPreparedSpaceRun cache state current (input :: inputs)
        ((reply, outcome.heap) :: replies) finalCache finish finalMemory
        (preparationSteps + outcome.result.steps + steps) seed footprint

/-- Count actual initialization once and retain its memory and accesses before
using the interface-fixed initial loader state. -/
def StatefulPreparedSpaceRuns (initialCache : δ) (args : Env configuration)
    (current : State w heapLimit) (inputs : List ι)
    (replies : List (Value response × Heap)) (finalCache : δ)
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      ∃ remaining, StatefulPreparedSpaceRun session prepareSpace initialCache state
        (State.ofExecution outcome) inputs replies finalCache finish finalMemory remaining
        (seed ∪ outcome.heapAccesses) footprint ∧ steps = outcome.result.steps + remaining

variable {session prepareSpace}

/-- Every actual prepared callback contributes one reply. -/
theorem StatefulPreparedSpaceRun.length
    {cache finalCache : δ} {state finish : Value session.stateTy}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRun session prepareSpace cache state current inputs replies
      finalCache finish finalMemory steps seed footprint) : replies.length = inputs.length := by
  induction run with
  | nil => rfl
  | cons loaded retained fits outcome returned rest ih => exact congrArg Nat.succ ih

/-- The stateful execution may forget its cache observations, never its actual
memory, steps or accesses. The converse does not follow. -/
theorem StatefulPreparedSpaceRun.erase
    {preparation : ι → State w heapLimit → Env request → State w heapLimit →
      Nat → Finset (Word w) → Finset (Word w) → Prop}
    (preparation_erase : ∀ cache input current args prepared nextCache steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        preparation input current args prepared steps seed footprint)
    {cache finalCache : δ} {state finish : Value session.stateTy}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRun session prepareSpace cache state current inputs replies
      finalCache finish finalMemory steps seed footprint) :
    PreparedSpaceRun session preparation state current inputs replies finish finalMemory
      steps seed footprint := by
  induction run with
  | nil => exact .nil _ _ _
  | cons loaded retained fits outcome returned rest ih =>
      exact .cons (preparation_erase _ _ _ _ _ _ _ _ _ loaded)
        retained fits outcome returned ih

/-- Erase cache observations after actual initialized execution. -/
theorem StatefulPreparedSpaceRuns.erase
    {preparation : ι → State w heapLimit → Env request → State w heapLimit →
      Nat → Finset (Word w) → Finset (Word w) → Prop}
    (preparation_erase : ∀ cache input current args prepared nextCache steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        preparation input current args prepared steps seed footprint)
    {initialCache finalCache : δ} {args : Env configuration}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {finish : Value session.stateTy}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRuns session prepareSpace initialCache args current inputs replies
      finalCache finish finalMemory steps seed footprint) :
    PreparedSpaceRuns session preparation args current inputs replies finish finalMemory
      steps seed footprint := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, remaining, rest.erase preparation_erase, counted⟩

/-- Source projection preserves both exact cache endpoints and every actual
callback return heap. Loader correspondence relates the same cache descriptor. -/
theorem StatefulPreparedSpaceRun.source
    {sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop}
    (preparation_source : ∀ cache input current args prepared nextCache steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        sourcePrepare cache input current.heap args prepared.heap nextCache)
    {cache finalCache : δ} {state finish : Value session.stateTy}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRun session prepareSpace cache state current inputs replies
      finalCache finish finalMemory steps seed footprint) :
    session.StatefulPreparedRun sourcePrepare cache state current.heap inputs replies
      finalCache finish finalMemory.heap := by
  induction run with
  | nil => exact .nil _ _ _
  | cons loaded retained fits outcome returned rest ih =>
      refine .cons (preparation_source _ _ _ _ _ _ _ _ _ loaded) ?_ ih
      unfold Complexity.Language.Session.Step
      simpa only [returned] using outcome.source

/-- Project the same initialized physical execution to source behavior without
reselecting any loader cache or intermediate heap. -/
theorem StatefulPreparedSpaceRuns.source
    {sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop}
    (preparation_source : ∀ cache input current args prepared nextCache steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        sourcePrepare cache input current.heap args prepared.heap nextCache)
    {initialCache finalCache : δ} {args : Env configuration}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {finish : Value session.stateTy}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRuns session prepareSpace initialCache args current inputs replies
      finalCache finish finalMemory steps seed footprint) :
    session.StatefulPreparedRuns sourcePrepare initialCache args current.heap inputs replies
      finalCache finish finalMemory.heap := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  refine ⟨state, outcome.heap, ?_, rest.source preparation_source⟩
  unfold Complexity.Language.Session.Starts
  simpa only [returned] using outcome.source

/-- Reusing a loader cache never resets previously resident physical words. -/
theorem StatefulPreparedSpaceRun.seed_subset
    {cache finalCache : δ} {state finish : Value session.stateTy}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRun session prepareSpace cache state current inputs replies
      finalCache finish finalMemory steps seed footprint) : seed ⊆ footprint := by
  induction run with
  | nil => exact fun _ member => member
  | cons loaded retained fits outcome returned rest ih =>
      exact fun _ member => ih (Finset.mem_union.mpr (Or.inl (retained member)))

/-- The initial resident seed remains counted through initialization and all
stateful preparations. -/
theorem StatefulPreparedSpaceRuns.seed_subset
    {initialCache finalCache : δ} {args : Env configuration}
    {current finalMemory : State w heapLimit} {inputs : List ι}
    {replies : List (Value response × Heap)} {finish : Value session.stateTy}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : StatefulPreparedSpaceRuns session prepareSpace initialCache args current inputs replies
      finalCache finish finalMemory steps seed footprint) : seed ⊆ footprint := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact fun _ member => rest.seed_subset (Finset.mem_union.mpr (Or.inl member))

/-- Histories compose at the same actual cache, callback state, memory and
physical footprint. Storage reuse is not replaced by isolated per-call sums. -/
theorem StatefulPreparedSpaceRun.append
    {cache middleCache finalCache : δ} {state middle finish : Value session.stateTy}
    {current intermediate finalMemory : State w heapLimit} {inputs₁ inputs₂ : List ι}
    {replies₁ replies₂ : List (Value response × Heap)} {steps₁ steps₂ : Nat}
    {seed middleFootprint finalFootprint : Finset (Word w)}
    (first : StatefulPreparedSpaceRun session prepareSpace cache state current inputs₁ replies₁
      middleCache middle intermediate steps₁ seed middleFootprint)
    (second : StatefulPreparedSpaceRun session prepareSpace middleCache middle intermediate
      inputs₂ replies₂ finalCache finish finalMemory steps₂ middleFootprint finalFootprint) :
    StatefulPreparedSpaceRun session prepareSpace cache state current (inputs₁ ++ inputs₂)
      (replies₁ ++ replies₂) finalCache finish finalMemory (steps₁ + steps₂)
      seed finalFootprint := by
  induction first with
  | nil => simpa only [List.nil_append, Nat.zero_add] using second
  | cons loaded retained fits outcome returned rest ih =>
      simpa only [List.cons_append, Nat.add_assoc] using
        StatefulPreparedSpaceRun.cons loaded retained fits outcome returned (ih second)

end Ram.LanguageCompiler.Session
