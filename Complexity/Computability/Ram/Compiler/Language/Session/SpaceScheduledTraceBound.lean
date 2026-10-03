/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.ScheduledTraceTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.Space

/-!
# Physical-word bounds for ScheduledTrace session executions

These bounds use the same domain, width admission and information boundary as
the corresponding time interface. A fixed initial seed is the preloaded arena
prefix, including metadata, not a purported exact set of reachable live cells.
Every actual invocation unions its heap accesses into that seed; reused addresses
count once. Registers, code, oracle work and external driver/transport are out.
The time-and-space interface bounds one and the same decorated execution, not
two separately selected successful histories. No change to source execution or
runtime is made. Correctness and termination remain independent obligations.
-/

namespace Complexity.Language.Session

universe u v z r

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {σ : Type v} {ω : α → List σ → Type z} {ι : Type r}
variable {request : List Ty} {response : Ty}


/-- Uniform cumulative physical words on the same actual initialized trace. -/
def ScheduledTraceSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → (schedule : List σ) → ω x schedule → Nat)
    (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x schedule environment, valid x schedule environment → ∀ w,
      ∀ admitted : historyWidth overhead scheduleWords x schedule ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x schedule environment inputs replies ∧
        footprint.card ≤ bound (size x schedule environment)


/-- Actual instruction counts and physical words on one shared execution.
Independent time and space witnesses must not be substituted for this claim. -/
def ScheduledTraceTimeSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → (schedule : List σ) → ω x schedule → Nat)
    (timeGrowth spaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
      (fun n => (timeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
      (fun n => (spaceGrowth n : ℝ)) ∧
    ∀ x schedule environment, valid x schedule environment → ∀ w,
      ∀ admitted : historyWidth overhead scheduleWords x schedule ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x schedule environment inputs replies ∧
        steps ≤ timeBound (size x schedule environment) ∧ footprint.card ≤ spaceBound (size x schedule environment)


/-- Project the space bound without changing the accepted execution. -/
theorem ScheduledTraceTimeSpaceO.space
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → (schedule : List σ) → ω x schedule → Nat)
    (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.ScheduledTraceTimeSpaceO encode scheduleWords valid accept size timeGrowth spaceGrowth) :
    session.ScheduledTraceSpaceO encode scheduleWords valid accept size spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, spaceBound, spaceAsymptotic, ?_⟩
  intro x schedule environment legal w admitted
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, timeCost, spaceCost⟩ := runs x schedule environment legal w admitted
  exact ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, spaceCost⟩

/-- Project the actual time bound of this same physical-footprint trace. -/
theorem ScheduledTraceTimeSpaceO.time
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → (schedule : List σ) → ω x schedule → Nat)
    (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.ScheduledTraceTimeSpaceO encode scheduleWords valid accept size timeGrowth spaceGrowth) :
    session.ScheduledTraceTimeO encode scheduleWords valid accept size timeGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, timeBound, timeAsymptotic, ?_⟩
  intro x schedule environment legal w admitted
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, timeCost, spaceCost⟩ := runs x schedule environment legal w admitted
  exact ⟨inputs, replies, finish, finalWorld, steps, fits, run.erase, accepted, timeCost⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev ScheduledTraceSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → (schedule : List σ) → ω x schedule → Nat) : Prop :=
  session.ScheduledTraceSpaceO encode scheduleWords valid accept growth id

/-- Restrict legality without changing admission, footprint or source entries. -/
theorem ScheduledTraceSpaceO.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid valid' : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → (schedule : List σ) → ω x schedule → Nat)
    (growth : Nat → Nat)
    (space : session.ScheduledTraceSpaceO encode scheduleWords valid accept size growth)
    (restrict : ∀ x schedule environment, valid' x schedule environment → valid x schedule environment) :
    session.ScheduledTraceSpaceO encode scheduleWords valid' accept size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x schedule environment legal
  exact runs x schedule environment (restrict x schedule environment legal)

/-- Project the same physical-word trace to independent source behavior. -/
theorem ScheduledTraceSpaceO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {scheduleWords : σ → Array Nat}
    {valid : (x : α) → (schedule : List σ) → ω x schedule → Prop}
    {accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → (schedule : List σ) → ω x schedule → Nat}
    {growth : Nat → Nat}
    (space : session.ScheduledTraceSpaceO encode scheduleWords valid accept size growth)
    {x : α} {schedule : List σ} {environment : ω x schedule}
    (legal : valid x schedule environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧
      accept x schedule environment inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, fits, run, accepted, cost⟩ :=
    runs x schedule environment legal (historyWidth overhead scheduleWords x schedule)
      (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩

end Complexity.Language.Session
