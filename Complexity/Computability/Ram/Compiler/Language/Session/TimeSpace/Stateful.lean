/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeSpace
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared.Stateful

/-!
# Joint session resources with retained loader state

The interface fixes a concrete current-input loader and its initial cache before
any history is chosen. Actual preparations thread that cache and the retained
heap across callbacks. Time and physical-word bounds concern this same run,
including initialization and every actual loader execution.

Uniform contracts reuse the canonical time-derived admission policy. Finite
protocols instead fix their word width and numerical budgets. Neither policy
loads future requests or uses their sizes as loader advice. Source projection
preserves the fixed initial and final cache and all return-time heaps.
-/

namespace Complexity.Language.Session

universe u v z r
variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ω : α → Type v} {ι : Type z} {δ : Type r}
variable {request : List Ty} {response : Ty}

/-- Uniform time and physical space for an accepted actual trace. One initial
loader state is fixed by the interface, not selected from the future history. -/
def StatefulPreparedTraceTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (initialCache : δ) (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → ω x → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.timeWidth overhead x (timeGrowth x environment) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap)) (finalCache : δ)
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.StatefulPreparedSpaceRuns session prepareSpace initialCache
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (Complexity.Program.timeWidth_base admitted))
          inputs replies finalCache finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧
        steps ≤ timeConstant * (1 + timeGrowth x environment) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x environment)

/-- The very same resource-certified trace gives independent source behavior,
using the concrete loader's cache-preserving source correspondence. -/
theorem StatefulPreparedTraceTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop}
    {initialCache : δ} {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : (x : α) → ω x → Nat}
    (resources : session.StatefulPreparedTraceTimeSpaceOOn prepareSpace initialCache valid accept
      timeGrowth spaceGrowth)
    (preparation_source : ∀ {w heapLimit : Nat} cache input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared nextCache
      steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        sourcePrepare cache input current.heap args prepared.heap nextCache)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ inputs replies finalCache finish finalHeap,
      session.StatefulPreparedRuns sourcePrepare initialCache (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finalCache finish finalHeap ∧
      accept x environment inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨inputs, replies, finalCache, finish, finalWorld, steps, footprint, run, accepted, costs⟩ :=
    runs x environment legal
      (Complexity.Program.timeWidth overhead x (timeGrowth x environment)) (Nat.le_refl _)
  exact ⟨inputs, replies, finalCache, finish, finalWorld.heap,
    run.source preparation_source, accepted⟩

/-- Joint uniform bounds for every legal history, retaining its request-word
admission and one loader cache across its actual callbacks. -/
def StatefulPreparedHistoryTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (initialCache : δ) (requestWords : ι → Array Nat) (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : α → List ι → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyTimeWidth overhead requestWords x inputs (timeGrowth x inputs) ≤ w,
      ∃ (replies : List (Value response × Heap)) (finalCache : δ)
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.StatefulPreparedSpaceRuns session prepareSpace initialCache
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyTimeWidth_base admitted))
          inputs replies finalCache finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        post x inputs replies ∧ steps ≤ timeConstant * (1 + timeGrowth x inputs) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x inputs)

/-- Recover source behavior with the same cache and reply observations from a
joint history certificate. No input preparation is reselected. -/
theorem StatefulPreparedHistoryTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop}
    {initialCache : δ} {requestWords : ι → Array Nat} {valid : α → List ι → Prop}
    {post : α → List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : α → List ι → Nat}
    (resources : session.StatefulPreparedHistoryTimeSpaceOOn prepareSpace initialCache
      requestWords valid post timeGrowth spaceGrowth)
    (preparation_source : ∀ {w heapLimit : Nat} cache input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared nextCache
      steps seed footprint,
      prepareSpace cache input current args prepared nextCache steps seed footprint →
        sourcePrepare cache input current.heap args prepared.heap nextCache)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ replies finalCache finish finalHeap,
      session.StatefulPreparedRuns sourcePrepare initialCache (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finalCache finish finalHeap ∧
      post x inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨replies, finalCache, finish, finalWorld, steps, footprint, run, accepted, costs⟩ :=
    runs x inputs legal
      (historyTimeWidth overhead requestWords x inputs (timeGrowth x inputs)) (Nat.le_refl _)
  exact ⟨replies, finalCache, finish, finalWorld.heap, run.source preparation_source, accepted⟩

/-- Uniform joint bounds for every accepted source history, retaining the
interface's initial loader state and the exact final cache. Coefficients are
fixed before all inputs, environments, histories and admitted machine widths.
Independent source correctness supplies accepted histories; this universal
resource condition does not choose an easier branch. -/
def StatefulPreparedWorstCaseTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (initialCache : δ) (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → ω x → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x environment, valid x environment →
      ∀ inputs replies finalCache finish finalHeap,
        session.StatefulPreparedRuns sourcePrepare initialCache (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finalCache finish finalHeap →
        accept x environment inputs replies →
        ∀ w, ∀ admitted : timeWidthWith overhead x (admissionWords x environment)
            (timeGrowth x environment) ≤ w,
          ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
              (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
            (steps : Nat) (footprint : Finset (Ram.Word w)),
            Ram.LanguageCompiler.Session.StatefulPreparedSpaceRuns session prepareSpace initialCache
              (Complexity.Program.Input.args x)
              (Ram.LanguageCompiler.Session.State.ofInput x w (timeWidthWith_base admitted))
              inputs replies finalCache finish finalWorld steps
              (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
            finalWorld.heap = finalHeap ∧
            steps ≤ timeConstant * (1 + timeGrowth x environment) ∧
            footprint.card ≤ spaceConstant * (1 + spaceGrowth x environment)

/-- Fixed-width numerical bounds for every accepted source branch. Both source
and RAM traces thread the interface's fixed initial loader cache. This universal
resource claim needs independent source correctness to provide an accepted trace. -/
def StatefulPreparedWorstCaseTimeSpaceBoundOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : δ → ι → Heap → Env request → Heap → δ → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, δ → ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → δ → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (initialCache : δ) (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (wordWidth : Nat) (timeBudget spaceBudget : (x : α) → ω x → Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∃ admitted : widthWith 0 x (admissionWords x environment) ≤ wordWidth,
      ∀ inputs replies finalCache finish finalHeap,
        session.StatefulPreparedRuns sourcePrepare initialCache (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finalCache finish finalHeap →
        accept x environment inputs replies →
        ∃ (finalWorld : Ram.LanguageCompiler.Session.State wordWidth
            (Ram.LanguageCompiler.ArrayFunction.heapLimit wordWidth))
          (steps : Nat) (footprint : Finset (Ram.Word wordWidth)),
          Ram.LanguageCompiler.Session.StatefulPreparedSpaceRuns session prepareSpace initialCache
            (Complexity.Program.Input.args x)
            (Ram.LanguageCompiler.Session.State.ofInput x wordWidth (widthWith_base admitted))
            inputs replies finalCache finish finalWorld steps
            (Ram.initialSegment wordWidth (Complexity.Program.RamInput.cursor x)) footprint ∧
          finalWorld.heap = finalHeap ∧
          steps ≤ timeBudget x environment ∧ footprint.card ≤ spaceBudget x environment

end Complexity.Language.Session
