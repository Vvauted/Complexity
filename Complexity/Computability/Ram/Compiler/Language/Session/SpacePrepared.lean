/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Space
import Complexity.Computability.Ram.Compiler.Language.Session.Prepared

/-!
# Physical footprints through current-input preparation

The interface author fixes the preparation relation, with its actual counted
execution, current arguments, returned memory and accumulated physical words.
Concrete loaders must connect this relation to their real invocation traces;
an arbitrary relation or footprint annotation alone certifies no loader.

The accumulated seed cannot be dropped by preparation. The callback starts at
the loader's actual resulting heap and memory, and unions its actual accesses
into the same footprint. Future inputs are not initializer data. This module
adds proof observations, not a loader, runtime or environment evaluator.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language

universe u
variable {ι : Type u} {configuration request : List Ty} {response : Ty}
variable {w heapLimit : Nat}
variable (session : Complexity.Language.Session configuration request response)
variable (prepareSpace : ι → State w heapLimit → Env request → State w heapLimit →
  Nat → Finset (Word w) → Finset (Word w) → Prop)

/-- Current-input preparation and callback share one retained memory and one
accumulating physical footprint. Only actual preparation steps are added. -/
inductive PreparedSpaceRun : Value session.stateTy → State w heapLimit → List ι →
    List (Value response × Heap) → Value session.stateTy → State w heapLimit → Nat →
    Finset (Word w) → Finset (Word w) → Prop
  | nil (state current seed) : PreparedSpaceRun state current [] [] state current 0 seed seed
  | cons {state current input args prepared preparationSteps reply next inputs replies
      finish finalMemory steps depth seed preparedFootprint footprint}
      (loaded : prepareSpace input current args prepared preparationSteps seed preparedFootprint)
      (retained : seed ⊆ preparedFootprint)
      (fits : EnvFits w args)
      (outcome : FunctionArenaExecution session.program session.step depth heapLimit
        prepared.placement (session.stepArgs state args) prepared.heap prepared.entry)
      (returned : outcome.value = session.stepValue reply next)
      (rest : PreparedSpaceRun next (State.ofExecution outcome) inputs replies finish finalMemory
        steps (preparedFootprint ∪ outcome.heapAccesses) footprint) :
      PreparedSpaceRun state current (input :: inputs) ((reply, outcome.heap) :: replies)
        finish finalMemory (preparationSteps + outcome.result.steps + steps) seed footprint

/-- Initialization's real accesses seed the first preparation, including when
the history is empty. Only configuration data initializes the source session. -/
def PreparedSpaceRuns (args : Env configuration) (current : State w heapLimit)
    (inputs : List ι) (replies : List (Value response × Heap))
    (finish : Value session.stateTy) (finalMemory : State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  ∃ depth state,
    ∃ outcome : FunctionArenaExecution session.program session.init depth heapLimit
      current.placement (session.initArgs args) current.heap current.entry,
    outcome.value = session.initValue state ∧
      ∃ remaining, PreparedSpaceRun session prepareSpace state (State.ofExecution outcome)
        inputs replies finish finalMemory remaining (seed ∪ outcome.heapAccesses) footprint ∧
        steps = outcome.result.steps + remaining

variable {session prepareSpace}
variable {prepare : ι → State w heapLimit → Env request → State w heapLimit → Nat → Prop}

/-- Erase the same concrete loader's footprint evidence, preserving its actual
steps, arguments and intermediate memory. This is not a new free preparation. -/
theorem PreparedSpaceRun.erase
    (preparation_erase : ∀ input current args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        prepare input current args prepared steps)
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRun session prepareSpace state current inputs replies finish finalMemory
      steps seed footprint) :
    PreparedRun session prepare state current inputs replies finish finalMemory steps := by
  induction run with
  | nil => exact .nil _ _
  | cons loaded retained fits outcome returned rest ih =>
      exact .cons (preparation_erase _ _ _ _ _ _ _ loaded) fits outcome returned ih

/-- The initialized trace projects without changing any invocation or cost. -/
theorem PreparedSpaceRuns.erase
    (preparation_erase : ∀ input current args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        prepare input current args prepared steps)
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session prepareSpace args current inputs replies finish finalMemory
      steps seed footprint) :
    PreparedRuns session prepare args current inputs replies finish finalMemory steps := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact ⟨depth, state, outcome, returned, remaining, rest.erase preparation_erase, counted⟩

/-- Preparation and callback cannot reset the retained physical-word history. -/
theorem PreparedSpaceRun.seed_subset
    {state finish : Value session.stateTy} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)} {steps : Nat}
    {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRun session prepareSpace state current inputs replies finish finalMemory
      steps seed footprint) : seed ⊆ footprint := by
  induction run with
  | nil => exact fun _ member => member
  | cons loaded retained fits outcome returned rest ih =>
      exact fun _ member => ih (Finset.mem_union.mpr (Or.inl (retained member)))

/-- The original resident arena prefix remains counted after all preparations. -/
theorem PreparedSpaceRuns.seed_subset
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session prepareSpace args current inputs replies finish finalMemory
      steps seed footprint) : seed ⊆ footprint := by
  obtain ⟨depth, state, outcome, returned, remaining, rest, counted⟩ := run
  exact fun _ member => rest.seed_subset (Finset.mem_union.mpr (Or.inl member))

/-- Prepared histories compose at their real intermediate heap and footprint,
retaining reused storage rather than adding isolated per-call word counts. -/
theorem PreparedSpaceRun.append
    {state middle finish : Value session.stateTy}
    {current intermediate finalMemory : State w heapLimit}
    {inputs₁ inputs₂ : List ι} {replies₁ replies₂ : List (Value response × Heap)}
    {steps₁ steps₂ : Nat} {seed middleFootprint finalFootprint : Finset (Word w)}
    (first : PreparedSpaceRun session prepareSpace state current inputs₁ replies₁ middle
      intermediate steps₁ seed middleFootprint)
    (second : PreparedSpaceRun session prepareSpace middle intermediate inputs₂ replies₂ finish
      finalMemory steps₂ middleFootprint finalFootprint) :
    PreparedSpaceRun session prepareSpace state current (inputs₁ ++ inputs₂)
      (replies₁ ++ replies₂) finish finalMemory (steps₁ + steps₂) seed finalFootprint := by
  induction first with
  | nil => simpa only [List.nil_append, Nat.zero_add] using second
  | cons loaded retained fits outcome returned rest ih =>
      simpa only [List.cons_append, Nat.add_assoc] using
        PreparedSpaceRun.cons loaded retained fits outcome returned (ih second)

/-- The fixed concrete loader's source correspondence erases the same space
trace to the independent source session, with all intermediate heaps intact. -/
theorem PreparedSpaceRuns.source
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    (preparation_source : ∀ input current args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session prepareSpace args current inputs replies finish finalMemory
      steps seed footprint) :
    session.PreparedRuns sourcePrepare args current.heap inputs replies finish finalMemory.heap := by
  let erased : ι → State w heapLimit → Env request → State w heapLimit → Nat → Prop :=
    fun input current args prepared steps =>
      ∃ seed footprint, prepareSpace input current args prepared steps seed footprint
  have machine : PreparedRuns session erased args current inputs replies finish finalMemory steps :=
    run.erase (fun _ _ _ _ _ seed footprint loaded => ⟨seed, footprint, loaded⟩)
  apply machine.source
  intro input entry arguments prepared count loaded
  obtain ⟨entryFootprint, finalFootprint, evidence⟩ := loaded
  exact preparation_source _ _ _ _ _ _ _ evidence

end Ram.LanguageCompiler.Session
