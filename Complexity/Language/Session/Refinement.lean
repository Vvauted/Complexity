/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session
import Init.Data.List.Monadic

/-!
# Mathematical refinement of persistent source sessions

A single-step refinement relates ordinary mathematical state to an actual source
value and heap. Replies use the existing heap-indexed `Representation`, at their
own return-time heaps. The state relation may retain ghost invariants and does
not choose, encode or reload a runtime state.

Finite mathematical histories reuse Lean's `List.mapM` in `StateM`. They are
proof models, not source callbacks or a second implementation. The fixed request
encoding describes the arguments already supplied at each call; it is not a
runtime loader. Reference-bearing external inputs still need a loading protocol.
Admissibility may depend on the mathematical state, so a completed protocol need
not accept another request. `ValidInputs` checks only the legal history in a proof.

The total refinement constructs successful source traces, and also describes any
actual trace of the same entries, including the source projection of a RAM run.
Neither statement requires a machine width or a time budget.
-/

namespace Complexity.Language.Session

universe u

variable {configuration request : List Ty} {response : Ty}
variable {session : Session configuration request response}
variable {σ ι β : Type u}

/-- Ordinary left-to-right stateful list traversal, used only as a proof model. -/
def modelRun (step : σ → ι → β × σ) (inputs : List ι) (state : σ) : List β × σ :=
  (inputs.mapM (m := StateM σ) (fun input state => step state input)) state

@[simp] theorem modelRun_nil (step : σ → ι → β × σ) (state : σ) :
    modelRun step [] state = ([], state) := rfl

@[simp] theorem modelRun_cons (step : σ → ι → β × σ) (input : ι)
    (inputs : List ι) (state : σ) :
    modelRun step (input :: inputs) state =
      ((step state input).1 :: (modelRun step inputs (step state input).2).1,
        (modelRun step inputs (step state input).2).2) := by
  simp only [modelRun, List.mapM_cons]
  rfl

/-- Each request is admissible at its own mathematical state. This proof-side
history condition does not pass a future sequence to either source entry. -/
def ValidInputs (admissible : σ → ι → Prop) (step : σ → ι → β × σ) :
    σ → List ι → Prop
  | _, [] => True
  | state, input :: inputs =>
      admissible state input ∧ ValidInputs admissible step (step state input).2 inputs

/-- Total correspondence of one actual source step to an ordinary mathematical
transition. The state relation observes the actual heap, without a chosen
encoder, unique runtime representation or disjoint-ownership assumption. -/
def StepRefines (session : Session configuration request response)
    (encode : ι → Env request) (output : Representation β response)
    (relation : σ → Value session.stateTy → Heap → Prop)
    (admissible : σ → ι → Prop) (step : σ → ι → β × σ) : Prop :=
  ∀ abstract state heap input, relation abstract state heap → admissible abstract input →
    ∃ reply next finish,
      session.Step state heap (encode input) reply next finish ∧
        output.Rel (step abstract input).1 reply finish ∧
        relation (step abstract input).2 next finish

variable {encode : ι → Env request} {output : Representation β response}
variable {relation : σ → Value session.stateTy → Heap → Prop}
variable {admissible : σ → ι → Prop} {step : σ → ι → β × σ}

/-- A total single-step refinement constructs a finite trace with exactly the
model's replies and final state observation. Requests remain environment data. -/
theorem StepRefines.run
    (refinement : StepRefines session encode output relation admissible step)
    {abstract : σ} {state : Value session.stateTy} {heap : Heap}
    (represented : relation abstract state heap) (inputs : List ι)
    (legal : ValidInputs admissible step abstract inputs) :
    ∃ replies finish finalHeap,
      session.Run state heap (inputs.map encode) replies finish finalHeap ∧
        List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
          (modelRun step inputs abstract).1 replies ∧
        relation (modelRun step inputs abstract).2 finish finalHeap := by
  induction inputs generalizing abstract state heap with
  | nil => exact ⟨[], state, heap, .nil _ _, .nil, represented⟩
  | cons input inputs ih =>
      obtain ⟨reply, next, intermediate, actual, observed, preserved⟩ :=
        refinement abstract state heap input represented legal.1
      obtain ⟨replies, finish, finalHeap, rest, observations, final⟩ :=
        ih preserved legal.2
      refine ⟨(reply, intermediate) :: replies, finish, finalHeap, .cons actual rest, ?_, ?_⟩
      · simp only [modelRun_cons]
        exact .cons observed observations
      · simpa only [modelRun_cons] using final

/-- The same refinement describes an already supplied actual trace, not only a
separately selected successful witness. This is the entry for RAM source erasure. -/
theorem StepRefines.post_of_run
    (refinement : StepRefines session encode output relation admissible step)
    {abstract : σ} {state finish : Value session.stateTy} {heap finalHeap : Heap}
    (represented : relation abstract state heap) (inputs : List ι)
    (legal : ValidInputs admissible step abstract inputs)
    {replies : List (Value response × Heap)}
    (run : session.Run state heap (inputs.map encode) replies finish finalHeap) :
    List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
        (modelRun step inputs abstract).1 replies ∧
      relation (modelRun step inputs abstract).2 finish finalHeap := by
  induction inputs generalizing abstract state heap replies with
  | nil =>
      cases run
      exact ⟨.nil, represented⟩
  | cons input inputs ih =>
      cases run with
      | cons actual rest =>
          obtain ⟨reply, next, intermediate, specified, observed, preserved⟩ :=
            refinement abstract state heap input represented legal.1
          obtain ⟨rfl, rfl, rfl⟩ := actual.deterministic specified
          obtain ⟨observations, final⟩ :=
            ih preserved legal.2 rest
          constructor
          · simp only [modelRun_cons]
            exact .cons observed observations
          · simpa only [modelRun_cons] using final

/-- A successful initializer has one actual state and heap. -/
theorem Starts.deterministic
    {args : Env configuration} {heap : Heap}
    {state₁ state₂ : Value session.stateTy} {finish₁ finish₂ : Heap}
    (first : session.Starts args heap state₁ finish₁)
    (second : session.Starts args heap state₂ finish₂) :
    state₁ = state₂ ∧ finish₁ = finish₂ := by
  have same := Part.some_injective (first.symm.trans second)
  have values := Except.ok.inj (congrArg Prod.fst same)
  exact ⟨(Equiv.cast _).injective values, congrArg Prod.snd same⟩

/-- Any two successful traces from the same actual state and heap have the same
replies, including their return-time heaps, and the same final observation. -/
theorem Run.deterministic
    {state finish₁ finish₂ : Value session.stateTy} {heap finalHeap₁ finalHeap₂ : Heap}
    {inputs : List (Env request)} {replies₁ replies₂ : List (Value response × Heap)}
    (first : session.Run state heap inputs replies₁ finish₁ finalHeap₁)
    (second : session.Run state heap inputs replies₂ finish₂ finalHeap₂) :
    replies₁ = replies₂ ∧ finish₁ = finish₂ ∧ finalHeap₁ = finalHeap₂ := by
  induction first generalizing replies₂ finish₂ finalHeap₂ with
  | nil =>
      cases second
      exact ⟨rfl, rfl, rfl⟩
  | cons called rest ih =>
      cases second with
      | cons called' rest' =>
          obtain ⟨rfl, rfl, rfl⟩ := called.deterministic called'
          obtain ⟨rfl, rfl, rfl⟩ := ih rest'
          exact ⟨rfl, rfl, rfl⟩

/-- Initialization and all subsequent actual steps have unique observations.
This aligns an independently proved source postcondition with a costed run. -/
theorem Runs.deterministic
    {args : Env configuration} {heap finalHeap₁ finalHeap₂ : Heap}
    {finish₁ finish₂ : Value session.stateTy} {inputs : List (Env request)}
    {replies₁ replies₂ : List (Value response × Heap)}
    (first : session.Runs args heap inputs replies₁ finish₁ finalHeap₁)
    (second : session.Runs args heap inputs replies₂ finish₂ finalHeap₂) :
    replies₁ = replies₂ ∧ finish₁ = finish₂ ∧ finalHeap₁ = finalHeap₂ := by
  obtain ⟨state₁, heap₁, start₁, rest₁⟩ := first
  obtain ⟨state₂, heap₂, start₂, rest₂⟩ := second
  obtain ⟨rfl, rfl⟩ := start₁.deterministic start₂
  exact rest₁.deterministic rest₂

/-- Attach a proved initialization to the same finite source refinement.
The supplied start includes its actual heap, not a reconstructed model state. -/
theorem StepRefines.runs
    (refinement : StepRefines session encode output relation admissible step)
    {args : Env configuration} {heap : Heap} {abstract : σ}
    (initialized : ∃ state initialHeap,
      session.Starts args heap state initialHeap ∧ relation abstract state initialHeap)
    (inputs : List ι) (legal : ValidInputs admissible step abstract inputs) :
    ∃ replies finish finalHeap,
      session.Runs args heap (inputs.map encode) replies finish finalHeap ∧
        List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
          (modelRun step inputs abstract).1 replies ∧
        relation (modelRun step inputs abstract).2 finish finalHeap := by
  obtain ⟨state, initialHeap, started, represented⟩ := initialized
  obtain ⟨replies, finish, finalHeap, run, observed, final⟩ :=
    refinement.run represented inputs legal
  exact ⟨replies, finish, finalHeap, ⟨state, initialHeap, started, run⟩, observed, final⟩

/-- Transfer ordinary mathematical observations to any initialized actual source
trace, so a separate cost proof cannot silently choose a different computation. -/
theorem StepRefines.post_of_runs
    (refinement : StepRefines session encode output relation admissible step)
    {args : Env configuration} {heap : Heap} {abstract : σ}
    (initialized : ∃ state initialHeap,
      session.Starts args heap state initialHeap ∧ relation abstract state initialHeap)
    (inputs : List ι) (legal : ValidInputs admissible step abstract inputs)
    {replies : List (Value response × Heap)} {finish : Value session.stateTy}
    {finalHeap : Heap}
    (run : session.Runs args heap (inputs.map encode) replies finish finalHeap) :
    List.Forall₂ (fun expected observed => output.Rel expected observed.1 observed.2)
        (modelRun step inputs abstract).1 replies ∧
      relation (modelRun step inputs abstract).2 finish finalHeap := by
  obtain ⟨state, initialHeap, started, represented⟩ := initialized
  obtain ⟨actual, actualHeap, actualStart, rest⟩ := run
  obtain ⟨rfl, rfl⟩ := actualStart.deterministic started
  exact refinement.post_of_run represented inputs legal rest

end Complexity.Language.Session
