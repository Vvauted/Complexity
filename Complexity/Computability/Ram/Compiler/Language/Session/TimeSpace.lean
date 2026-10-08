/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.TimeSpace
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceTraceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedTraceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedHistoryBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedWorstCaseBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceScheduledTraceBound

/-!
# Joint time and space bounds for persistent sessions

Time and physical-word targets may depend differently on all protocol parameters.
One width overhead and two coefficients are chosen before every public input,
environment, history and machine width. Word admission uses the time target only;
space never enlarges a machine word. Existing input/history/external-word
requirements are retained. One width is fixed for the entire decorated execution,
not resized between callbacks. The additional scale is proof-side admission data:
neither future requests nor their answers are loaded into source memory. Both
costs constrain the same decorated execution. Preparation-space relations are
fixed by the interface author and must be actual loader observations, not arbitrary
resource labels. No new runner is introduced.
-/

namespace Complexity.Language.Session

universe u v z r
variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ω : α → Type v} {ι : Type z} {request : List Ty} {response : Ty}

/-- Preserve the complete protocol-fixed history admission and add only the
whole-trace time target. This changes no source arguments or initialized heap. -/
def historyTimeWidth (overhead : Nat) (requestWords : ι → Array Nat)
    (x : α) (inputs : List ι) (timeTarget : Nat) : Nat :=
  max (historyWidth overhead requestWords x inputs)
    (Complexity.Program.timeWidth overhead x timeTarget)

theorem historyTimeWidth_base {overhead w : Nat} {requestWords : ι → Array Nat}
    {x : α} {inputs : List ι} {timeTarget : Nat}
    (admitted : historyTimeWidth overhead requestWords x inputs timeTarget ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
      (Complexity.Program.RamInput.words x) ≤ w :=
  historyWidth_base ((Nat.le_max_left _ _).trans admitted)

/-- Preserve external scale-word admission while allowing time-derived address
capacity. The scale words and target are not runtime input or future advice. -/
def timeWidthWith (overhead : Nat) (x : α) (words : Array Nat)
    (timeTarget : Nat) : Nat :=
  max (widthWith overhead x words) (Complexity.Program.timeWidth overhead x timeTarget)

theorem timeWidthWith_base {overhead w : Nat} {x : α} {words : Array Nat}
    {timeTarget : Nat}
    (admitted : timeWidthWith overhead x words timeTarget ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
      (Complexity.Program.RamInput.words x) ≤ w :=
  widthWith_base ((Nat.le_max_left _ _).trans admitted)

/-- Uniform instruction and physical-word bounds for each specified request
history, with one time-derived word width throughout the actual session. -/
def TimeSpaceOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (timeGrowth spaceGrowth : α → List ι → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : Complexity.Program.timeWidth overhead x (timeGrowth x inputs) ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (Complexity.Program.timeWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        steps ≤ timeConstant * (1 + timeGrowth x inputs) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x inputs)

/-- Uniform joint bounds for an accepted actual trace of each legal environment.
Both observations belong to the same retained sequence of session executions. -/
def TraceTimeSpaceOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → ω x → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.timeWidth overhead x (timeGrowth x environment) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (Complexity.Program.timeWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧
        steps ≤ timeConstant * (1 + timeGrowth x environment) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x environment)

/-- Erase the resource observations of the same accepted trace to obtain its
width-independent source behavior. -/
theorem TraceTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : (x : α) → ω x → Nat}
    (resources : session.TraceTimeSpaceOOn encode valid accept timeGrowth spaceGrowth)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ inputs replies finish finalHeap,
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧ accept x environment inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, costs⟩ :=
    runs x environment legal
      (Complexity.Program.timeWidth overhead x (timeGrowth x environment)) (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩

/-- Uniform joint bounds for an accepted actual trace, including the fixed
preparation of each current request in the retained session state. -/
def PreparedTraceTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → ω x → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.timeWidth overhead x (timeGrowth x environment) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (Complexity.Program.timeWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧
        steps ≤ timeConstant * (1 + timeGrowth x environment) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x environment)

/-- Project the same accepted prepared trace to its source behavior, using the
fixed preparation relation's source correspondence. -/
theorem PreparedTraceTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : (x : α) → ω x → Nat}
    (resources : session.PreparedTraceTimeSpaceOOn prepareSpace valid accept timeGrowth spaceGrowth)
    (preparation_source : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ inputs replies finish finalHeap,
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
      accept x environment inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, run, accepted, costs⟩ :=
    runs x environment legal
      (Complexity.Program.timeWidth overhead x (timeGrowth x environment)) (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source preparation_source, accepted⟩

/-- Joint bounds for every specified legal prepared history. Width admission
retains its request-word requirements as well as the whole-history time target. -/
def PreparedHistoryTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat) (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : α → List ι → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyTimeWidth overhead requestWords x inputs (timeGrowth x inputs) ≤ w,
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyTimeWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        post x inputs replies ∧ steps ≤ timeConstant * (1 + timeGrowth x inputs) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x inputs)

/-- Recover the source execution and postcondition of the same prepared history
from its resource certificate and preparation-source correspondence. -/
theorem PreparedHistoryTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {requestWords : ι → Array Nat} {valid : α → List ι → Prop}
    {post : α → List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : α → List ι → Nat}
    (resources : session.PreparedHistoryTimeSpaceOOn prepareSpace requestWords valid post
      timeGrowth spaceGrowth)
    (preparation_source : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ replies finish finalHeap,
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧ post x inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨replies, finish, finalWorld, steps, footprint, run, accepted, costs⟩ :=
    runs x inputs legal
      (historyTimeWidth overhead requestWords x inputs (timeGrowth x inputs)) (Nat.le_refl _)
  exact ⟨replies, finish, finalWorld.heap, run.source preparation_source, accepted⟩

/-- Uniform joint bounds for every accepted prepared source branch. Separate
source correctness supplies such a branch; this universal claim assumes none. -/
def PreparedWorstCaseTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → ω x → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x environment, valid x environment →
      ∀ inputs replies finish finalHeap,
        session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
        accept x environment inputs replies →
        ∀ w, ∀ admitted : timeWidthWith overhead x (admissionWords x environment)
            (timeGrowth x environment) ≤ w,
          ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
              (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
            (steps : Nat) (footprint : Finset (Ram.Word w)),
            Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
              (Complexity.Program.Input.args x)
              (Ram.LanguageCompiler.Session.State.ofInput x w (timeWidthWith_base admitted))
              inputs replies finish finalWorld steps
              (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
            finalWorld.heap = finalHeap ∧
            steps ≤ timeConstant * (1 + timeGrowth x environment) ∧
            footprint.card ≤ spaceConstant * (1 + spaceGrowth x environment)

/-- Concrete resources for an intentionally finite protocol. The interface author
fixes the word width and budgets; there are no existential asymptotic multipliers
which could absorb every finite computation. Input admission, all encoded
requests, acceptance and both costs refer to one actual decorated trace. -/
def TraceTimeSpaceBoundOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (wordWidth : Nat) (timeBudget spaceBudget : (x : α) → ω x → Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∃ admitted : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ wordWidth,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State wordWidth
          (Ram.LanguageCompiler.ArrayFunction.heapLimit wordWidth))
        (steps : Nat) (footprint : Finset (Ram.Word wordWidth)),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits wordWidth (encode input)) ∧
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x wordWidth admitted)
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment wordWidth (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧
        steps ≤ timeBudget x environment ∧ footprint.card ≤ spaceBudget x environment

/-- A finite resource certificate retains the same width-independent source
behavior; the fixed machine width supplies no additional source input. -/
theorem TraceTimeSpaceBoundOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {wordWidth : Nat} {timeBudget spaceBudget : (x : α) → ω x → Nat}
    (resources : session.TraceTimeSpaceBoundOn encode valid accept wordWidth
      timeBudget spaceBudget)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ inputs replies finish finalHeap,
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧ accept x environment inputs replies := by
  obtain ⟨admitted, inputs, replies, finish, finalWorld, steps, footprint,
    fits, run, accepted, costs⟩ := resources x environment legal
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩

/-- Concrete fixed-width resources for every accepted source branch, including
the actual fixed loader. The protocol's admission words retain their role as
proof-side scales only. Correctness must separately supply an accepted source
trace; this universal resource claim does not invent one or preload a future. -/
def PreparedWorstCaseTimeSpaceBoundOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (wordWidth : Nat) (timeBudget spaceBudget : (x : α) → ω x → Nat) : Prop :=
  ∀ x environment, valid x environment →
    ∃ admitted : widthWith 0 x (admissionWords x environment) ≤ wordWidth,
      ∀ inputs replies finish finalHeap,
        session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
        accept x environment inputs replies →
        ∃ (finalWorld : Ram.LanguageCompiler.Session.State wordWidth
            (Ram.LanguageCompiler.ArrayFunction.heapLimit wordWidth))
          (steps : Nat) (footprint : Finset (Ram.Word wordWidth)),
          Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
            (Complexity.Program.Input.args x)
            (Ram.LanguageCompiler.Session.State.ofInput x wordWidth (widthWith_base admitted))
            inputs replies finish finalWorld steps
            (Ram.initialSegment wordWidth (Complexity.Program.RamInput.cursor x)) footprint ∧
          finalWorld.heap = finalHeap ∧
          steps ≤ timeBudget x environment ∧ footprint.card ≤ spaceBudget x environment

section Scheduled
variable {σ : Type r} {η : α → List σ → Type v}

/-- Uniform joint bounds for an accepted actual trace under a fixed schedule.
The schedule's word requirements affect admission, not the source arguments. -/
def ScheduledTraceTimeSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → η x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → η x schedule →
      List ι → List (Value response × Heap) → Prop)
    (timeGrowth spaceGrowth : (x : α) → (schedule : List σ) → η x schedule → Nat) : Prop :=
  ∃ overhead timeConstant spaceConstant : Nat,
    ∀ x schedule environment, valid x schedule environment → ∀ w,
      ∀ admitted : historyTimeWidth overhead scheduleWords x schedule
        (timeGrowth x schedule environment) ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
        (steps : Nat) (footprint : Finset (Ram.Word w)),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyTimeWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x schedule environment inputs replies ∧
        steps ≤ timeConstant * (1 + timeGrowth x schedule environment) ∧
        footprint.card ≤ spaceConstant * (1 + spaceGrowth x schedule environment)

/-- Erase the same scheduled trace's resource observations while retaining its
accepted source behavior. -/
theorem ScheduledTraceTimeSpaceOOn.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {scheduleWords : σ → Array Nat}
    {valid : (x : α) → (schedule : List σ) → η x schedule → Prop}
    {accept : (x : α) → (schedule : List σ) → η x schedule →
      List ι → List (Value response × Heap) → Prop}
    {timeGrowth spaceGrowth : (x : α) → (schedule : List σ) → η x schedule → Nat}
    (resources : session.ScheduledTraceTimeSpaceOOn encode scheduleWords valid accept
      timeGrowth spaceGrowth)
    {x : α} {schedule : List σ} {environment : η x schedule}
    (legal : valid x schedule environment) :
    ∃ inputs replies finish finalHeap,
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧ accept x schedule environment inputs replies := by
  obtain ⟨overhead, timeConstant, spaceConstant, runs⟩ := resources
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, costs⟩ :=
    runs x schedule environment legal
      (historyTimeWidth overhead scheduleWords x schedule (timeGrowth x schedule environment))
      (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩
end Scheduled

end Complexity.Language.Session
