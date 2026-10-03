/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared

/-!
# Fixed-width physical-word budgets for finite session tasks

The task author fixes word width and physical-word budget. Every legal public
configuration and history/environment must fit and have a real execution;
admission, capacity and termination are conclusions, not extra legality filters.
The preloaded arena prefix includes metadata. Actual initialization, callbacks
and concrete current-input preparation accumulate distinct physical words in
one retained footprint. This is not a byte-limit simulation or exact peak-live
space. Neither hidden environment nor future request history initializes memory.

Preparation-space relations are fixed by the interface author and backed by
concrete real loader executions, never candidate-selected annotations. Source
correctness and adversarial termination remain separate obligations. In
particular, an existential accepted trace does not cover every adversary branch.
-/

namespace Complexity.Language.Session

universe u v z
variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type z} {ω : α → Type v} {request : List Ty} {response : Ty}

/-- Finite fixed-width word space on every legal sequential request history. -/
def SpaceBound (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop) (w bound : Nat) : Prop :=
  ∀ x inputs, valid x inputs →
    ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        footprint.card ≤ bound

/-- A finite accepted prepared trace, including real preparation addresses. -/
def PreparedTraceSpaceBound
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound : Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧ footprint.card ≤ bound

/-- Every given permitted successful source trace has a bounded realization
with the same returned values, final private state and heap. This is not a
termination theorem for every legal environment branch. -/
def PreparedWorstCaseSpaceBound
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound : Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∀ inputs replies finish finalHeap,
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
      accept x environment inputs replies →
      ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
          (Complexity.Program.RamInput.words x) ≤ w,
        ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
            (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
          (footprint : Finset (Ram.Word w)),
          Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
            (Complexity.Program.Input.args x)
            (Ram.LanguageCompiler.Session.State.ofInput x w base)
            inputs replies finish finalWorld steps
            (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
          finalWorld.heap = finalHeap ∧ footprint.card ≤ bound

/-- Restrict legal histories without changing width, budget or computation. -/
theorem SpaceBound.mono_valid
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid valid' : α → List ι → Prop} {w bound : Nat}
    (space : session.SpaceBound encode valid w bound)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.SpaceBound encode valid' w bound :=
  fun x inputs legal => space x inputs (restrict x inputs legal)

/-- An enlarged word budget retains every legal execution witness. -/
theorem SpaceBound.mono_bound
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : α → List ι → Prop} {w bound larger : Nat}
    (space : session.SpaceBound encode valid w bound) (le : bound ≤ larger) :
    session.SpaceBound encode valid w larger := by
  intro x inputs legal
  obtain ⟨base, fits, replies, finish, finalWorld, steps, footprint, run, words⟩ :=
    space x inputs legal
  exact ⟨base, fits, replies, finish, finalWorld, steps, footprint, run, words.trans le⟩

/-- Project the same fixed-width physical trace to independent source behavior. -/
theorem SpaceBound.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : α → List ι → Prop} {w bound : Nat}
    (space : session.SpaceBound encode valid w bound)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap := by
  obtain ⟨base, fits, replies, finish, finalWorld, steps, footprint, run, words⟩ :=
    space x inputs legal
  exact ⟨replies, finish, finalWorld.heap, run.source⟩

/-- Restrict the legal environments, retaining the fixed concrete loader. -/
theorem PreparedTraceSpaceBound.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid valid' : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound : Nat)
    (space : session.PreparedTraceSpaceBound prepareSpace valid accept w bound)
    (restrict : ∀ x environment, valid' x environment → valid x environment) :
    session.PreparedTraceSpaceBound prepareSpace valid' accept w bound :=
  fun x environment legal => space x environment (restrict x environment legal)

/-- Enlarge the fixed word budget on the same real preparation/callback trace. -/
theorem PreparedTraceSpaceBound.mono_bound
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound larger : Nat)
    (space : session.PreparedTraceSpaceBound prepareSpace valid accept w bound) (le : bound ≤ larger) :
    session.PreparedTraceSpaceBound prepareSpace valid accept w larger := by
  intro x environment legal
  obtain ⟨base, inputs, replies, finish, finalWorld, steps, footprint, run, accepted, words⟩ := space x environment legal
  exact ⟨base, inputs, replies, finish, finalWorld, steps, footprint, run, accepted, words.trans le⟩

/-- Finite time and physical words of one accepted real execution. -/
def PreparedTraceTimeSpaceBound
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w timeBudget spaceBudget : Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧ steps ≤ timeBudget ∧ footprint.card ≤ spaceBudget

/-- Restrict the legal environments, retaining the fixed concrete loader. -/
theorem PreparedWorstCaseSpaceBound.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid valid' : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound : Nat)
    (space : session.PreparedWorstCaseSpaceBound sourcePrepare prepareSpace valid accept w bound)
    (restrict : ∀ x environment, valid' x environment → valid x environment) :
    session.PreparedWorstCaseSpaceBound sourcePrepare prepareSpace valid' accept w bound :=
  fun x environment legal => space x environment (restrict x environment legal)

/-- Enlarge the fixed word budget on the same real preparation/callback trace. -/
theorem PreparedWorstCaseSpaceBound.mono_bound
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w bound larger : Nat)
    (space : session.PreparedWorstCaseSpaceBound sourcePrepare prepareSpace valid accept w bound) (le : bound ≤ larger) :
    session.PreparedWorstCaseSpaceBound sourcePrepare prepareSpace valid accept w larger := by
  intro x environment legal inputs replies finish finalHeap source accepted
  obtain ⟨base, finalWorld, steps, footprint, run, sameHeap, words⟩ := space x environment legal inputs replies finish finalHeap source accepted
  exact ⟨base, finalWorld, steps, footprint, run, sameHeap, words.trans le⟩

/-- Finite time and physical words of one accepted real execution. -/
def PreparedWorstCaseTimeSpaceBound
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (w timeBudget spaceBudget : Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∀ inputs replies finish finalHeap,
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
      accept x environment inputs replies →
      ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
          (Complexity.Program.RamInput.words x) ≤ w,
        ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
            (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
          (footprint : Finset (Ram.Word w)),
          Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
            (Complexity.Program.Input.args x)
            (Ram.LanguageCompiler.Session.State.ofInput x w base)
            inputs replies finish finalWorld steps
            (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
          finalWorld.heap = finalHeap ∧ steps ≤ timeBudget ∧ footprint.card ≤ spaceBudget

/-- Fixed-width instruction and physical-word budgets on one persistent trace. -/
def TimeSpaceBound (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop) (w timeBudget spaceBudget : Nat) : Prop :=
  ∀ x inputs, valid x inputs →
    ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        steps ≤ timeBudget ∧ footprint.card ≤ spaceBudget


/-- The concrete loader correspondence projects the same accepted trace.
Neither the oracle nor a free mathematical state conversion is executed. -/
theorem PreparedTraceSpaceBound.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {w bound : Nat}
    (preparation_source : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    (space : session.PreparedTraceSpaceBound prepareSpace valid accept w bound)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
      accept x environment inputs replies := by
  obtain ⟨base, inputs, replies, finish, finalWorld, steps, footprint, run, accepted, words⟩ :=
    space x environment legal
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source preparation_source, accepted⟩

/-- At the fixed task width, realize the particular permitted source trace
without changing its outputs, private final state, heap or accepted history. -/
theorem PreparedWorstCaseSpaceBound.realizes
    {session : Session (Complexity.Program.Input.params α) request response}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {w bound : Nat}
    (space : session.PreparedWorstCaseSpaceBound sourcePrepare prepareSpace valid accept w bound)
    {x : α} {environment : ω x} (legal : valid x environment)
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {finalHeap : Heap}
    (source : session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
      (Complexity.Program.Input.heap x) inputs replies finish finalHeap)
    (accepted : accept x environment inputs replies) :
    ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        finalWorld.heap = finalHeap ∧ footprint.card ≤ bound :=
  space x environment legal inputs replies finish finalHeap source accepted

end Complexity.Language.Session
