/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session.Refinement

/-!
# Source sessions with current-request preparation

Reference-bearing external inputs must be materialized in the current heap
before calling the selected source entry. A protocol fixes the preparation
relation; it is not an implementation-selected decoder or private-state loader.
The current raw request alone is prepared, and the actual retained state is
passed unchanged to the call at that prepared heap.

These relations compose existing preparation and source evaluations. They do
not define a new evaluator. Invariants about state contents need a real frame
argument across preparation; heap extension does not preserve arbitrary
relations automatically. Correctness has no RAM or resource premise.
-/

namespace Complexity.Language.Session

universe u
variable {ι σ β : Type u}
variable {configuration request : List Ty} {response : Ty}
variable (session : Session configuration request response)
variable (prepare : ι → Heap → Env request → Heap → Prop)

/-- Interleave current-input preparation and actual source calls, retaining
each reply's own return heap. No preparation sees future requests. -/
inductive PreparedRun : Value session.stateTy → Heap → List ι →
    List (Value response × Heap) → Value session.stateTy → Heap → Prop
  | nil (state heap) : PreparedRun state heap [] [] state heap
  | cons {state heap input args prepared reply next intermediate inputs replies finish finalHeap}
      (loaded : prepare input heap args prepared)
      (called : session.Step state prepared args reply next intermediate)
      (rest : PreparedRun next intermediate inputs replies finish finalHeap) :
      PreparedRun state heap (input :: inputs) ((reply, intermediate) :: replies) finish finalHeap

/-- Initialize once; subsequent preparation retains that initialized heap and
the heaps returned by actual calls rather than rebuilding private state. -/
def PreparedRuns (args : Env configuration) (heap : Heap) (inputs : List ι)
    (replies : List (Value response × Heap)) (finish : Value session.stateTy)
    (finalHeap : Heap) : Prop :=
  ∃ state initialized, session.Starts args heap state initialized ∧
    session.PreparedRun prepare state initialized inputs replies finish finalHeap

/-- Every successful prepared request has exactly one actual callback reply. -/
theorem PreparedRun.length
    {state finish : Value session.stateTy} {heap finalHeap : Heap}
    {inputs : List ι} {replies : List (Value response × Heap)}
    (run : session.PreparedRun prepare state heap inputs replies finish finalHeap) :
    replies.length = inputs.length := by
  induction run with
  | nil => rfl
  | cons loaded called rest ih => exact congrArg Nat.succ ih

/-- Refine a step after every actual preparation admitted by the fixed input
protocol. The author must transport the state observation through that preparation,
using its concrete frame and representation properties. -/
def PreparedStepRefines (output : Representation β response)
    (relation : σ → Value session.stateTy → Heap → Prop)
    (admissible : σ → ι → Prop) (step : σ → ι → β × σ) : Prop :=
  ∀ abstract state heap input, relation abstract state heap → admissible abstract input →
    ∀ args prepared, prepare input heap args prepared →
      ∃ reply next finish,
        session.Step state prepared args reply next finish ∧
        output.Rel (step abstract input).1 reply finish ∧
        relation (step abstract input).2 next finish

variable {session prepare}
variable {output : Representation β response}
variable {relation : σ → Value session.stateTy → Heap → Prop}
variable {admissible : σ → ι → Prop} {step : σ → ι → β × σ}

/-- Compose ordinary mathematical transitions through actual prepared requests.
Preparation totality is a source fact, without finite-machine readiness. -/
theorem PreparedStepRefines.run
    (refinement : session.PreparedStepRefines prepare output relation admissible step)
    (preparable : ∀ input heap, ∃ args finish, prepare input heap args finish)
    {abstract : σ} {state : Value session.stateTy} {heap : Heap}
    (represented : relation abstract state heap) (inputs : List ι)
    (legal : ValidInputs admissible step abstract inputs) :
    ∃ replies finish finalHeap,
      session.PreparedRun prepare state heap inputs replies finish finalHeap ∧
        List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
          (modelRun step inputs abstract).1 replies ∧
        relation (modelRun step inputs abstract).2 finish finalHeap := by
  induction inputs generalizing abstract state heap with
  | nil => exact ⟨[], state, heap, .nil _ _, .nil, represented⟩
  | cons input inputs ih =>
      obtain ⟨args, prepared, loaded⟩ := preparable input heap
      obtain ⟨reply, next, intermediate, called, observed, preserved⟩ :=
        refinement abstract state heap input represented legal.1 args prepared loaded
      obtain ⟨replies, finish, finalHeap, rest, observations, final⟩ :=
        ih preserved legal.2
      refine ⟨(reply, intermediate) :: replies, finish, finalHeap,
        .cons loaded called rest, ?_, ?_⟩
      · simp only [modelRun_cons]
        exact .cons observed observations
      · simpa only [modelRun_cons] using final

/-- Attach the one actual source initialization to the same prepared refinement. -/
theorem PreparedStepRefines.runs
    (refinement : session.PreparedStepRefines prepare output relation admissible step)
    (preparable : ∀ input heap, ∃ args finish, prepare input heap args finish)
    {args : Env configuration} {heap : Heap} {abstract : σ}
    (initialized : ∃ state initialHeap,
      session.Starts args heap state initialHeap ∧ relation abstract state initialHeap)
    (inputs : List ι) (legal : ValidInputs admissible step abstract inputs) :
    ∃ replies finish finalHeap,
      session.PreparedRuns prepare args heap inputs replies finish finalHeap ∧
        List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
          (modelRun step inputs abstract).1 replies ∧
        relation (modelRun step inputs abstract).2 finish finalHeap := by
  obtain ⟨state, initialHeap, started, represented⟩ := initialized
  obtain ⟨replies, finish, finalHeap, run, observed, final⟩ :=
    refinement.run preparable represented inputs legal
  exact ⟨replies, finish, finalHeap, ⟨state, initialHeap, started, run⟩, observed, final⟩

end Complexity.Language.Session
