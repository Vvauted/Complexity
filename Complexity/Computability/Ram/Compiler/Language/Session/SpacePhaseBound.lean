/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.PhaseTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePhase

/-!
# Uniform phase bounds on accumulated physical space

Each space envelope bounds the complete footprint up to that phase, including
the fixed preloaded arena prefix and earlier invocations. It is not an isolated
callback footprint and is never summed across calls. In the combined interface,
each time envelope instead bounds that actual invocation's instruction count.
Initialization cannot subsidize the time of a later callback. The public history
justifies width but never becomes initializer data. Loading and transport remain
outside this preloaded-callback boundary; prepared loaders need their own space
trace. These are physical word bounds, not exact peak reachable-live storage.
-/

namespace Complexity.Language.Session

universe u v
variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}

/-- Initialization and each callback have uniform bounds on the accumulated
physical footprint of that same persistent execution. -/
def PhaseSpaceO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initSize : α → Nat) (stepSize : α → ι → Nat)
    (initGrowth stepGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ initBound stepBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (initBound n : ℝ))
      (fun n => (initGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (stepBound n : ℝ))
      (fun n => (stepGrowth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyWidth overhead requestWords x inputs ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PhaseSpaceRuns session encode
          (fun input _ words => words.card ≤ stepBound (stepSize x input))
          (fun _ words => words.card ≤ initBound (initSize x))
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint

/-- The phase's actual instruction count and its complete accumulated physical
words satisfy independent envelopes on one shared persistent trace. -/
def PhaseTimeSpaceO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initSize : α → Nat) (stepSize : α → ι → Nat)
    (initTimeGrowth stepTimeGrowth initSpaceGrowth stepSpaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ initTime stepTime initSpace stepSpace : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (initTime n : ℝ))
      (fun n => (initTimeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (stepTime n : ℝ))
      (fun n => (stepTimeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (initSpace n : ℝ))
      (fun n => (initSpaceGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (stepSpace n : ℝ))
      (fun n => (stepSpaceGrowth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyWidth overhead requestWords x inputs ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat)
        (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PhaseSpaceRuns session encode
          (fun input steps words => steps ≤ stepTime (stepSize x input) ∧
            words.card ≤ stepSpace (stepSize x input))
          (fun steps words => steps ≤ initTime (initSize x) ∧
            words.card ≤ initSpace (initSize x))
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint

/-- Project each actual phase's time bound without selecting another trace. -/
theorem PhaseTimeSpaceO.time
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initSize : α → Nat) (stepSize : α → ι → Nat)
    (initTimeGrowth stepTimeGrowth initSpaceGrowth stepSpaceGrowth : Nat → Nat)
    (bounded : session.PhaseTimeSpaceO encode requestWords valid initSize stepSize
      initTimeGrowth stepTimeGrowth initSpaceGrowth stepSpaceGrowth) :
    session.PhaseTimeO encode requestWords valid initSize stepSize
      initTimeGrowth stepTimeGrowth := by
  obtain ⟨overhead, initTime, stepTime, initSpace, stepSpace,
    initTimeAsymptotic, stepTimeAsymptotic, initSpaceAsymptotic, stepSpaceAsymptotic,
    runs⟩ := bounded
  refine ⟨overhead, initTime, stepTime, initTimeAsymptotic, stepTimeAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run⟩ :=
    runs x inputs legal w admitted
  exact ⟨fits, replies, finish, finalWorld, steps,
    run.bounded (fun _ _ bound => bound.1) (fun _ _ _ bound => bound.1)⟩

/-- Project the accumulated word envelopes of each actual phase. -/
theorem PhaseTimeSpaceO.space
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initSize : α → Nat) (stepSize : α → ι → Nat)
    (initTimeGrowth stepTimeGrowth initSpaceGrowth stepSpaceGrowth : Nat → Nat)
    (bounded : session.PhaseTimeSpaceO encode requestWords valid initSize stepSize
      initTimeGrowth stepTimeGrowth initSpaceGrowth stepSpaceGrowth) :
    session.PhaseSpaceO encode requestWords valid initSize stepSize
      initSpaceGrowth stepSpaceGrowth := by
  obtain ⟨overhead, initTime, stepTime, initSpace, stepSpace,
    initTimeAsymptotic, stepTimeAsymptotic, initSpaceAsymptotic, stepSpaceAsymptotic,
    runs⟩ := bounded
  refine ⟨overhead, initSpace, stepSpace, initSpaceAsymptotic, stepSpaceAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run⟩ :=
    runs x inputs legal w admitted
  exact ⟨fits, replies, finish, finalWorld, steps, footprint,
    run.mono (fun _ _ bound => bound.2) (fun _ _ _ bound => bound.2)⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev PhaseSpaceOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initGrowth : α → Nat) (stepGrowth : α → ι → Nat) : Prop :=
  session.PhaseSpaceO encode requestWords valid initGrowth stepGrowth id id

/-- Restrict legal histories while retaining the same cumulative phase envelopes. -/
theorem PhaseSpaceO.mono_valid
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {requestWords : ι → Array Nat}
    {valid valid' : α → List ι → Prop} {initSize : α → Nat} {stepSize : α → ι → Nat}
    {initGrowth stepGrowth : Nat → Nat}
    (space : session.PhaseSpaceO encode requestWords valid initSize stepSize initGrowth stepGrowth)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.PhaseSpaceO encode requestWords valid' initSize stepSize initGrowth stepGrowth := by
  obtain ⟨overhead, initBound, stepBound, initAsymptotic, stepAsymptotic, runs⟩ := space
  exact ⟨overhead, initBound, stepBound, initAsymptotic, stepAsymptotic,
    fun x inputs legal => runs x inputs (restrict x inputs legal)⟩

/-- The same phase-bounded physical trace supplies independent source behavior. -/
theorem PhaseSpaceO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {requestWords : ι → Array Nat}
    {valid : α → List ι → Prop} {initSize : α → Nat} {stepSize : α → ι → Nat}
    {initGrowth stepGrowth : Nat → Nat}
    (space : session.PhaseSpaceO encode requestWords valid initSize stepSize initGrowth stepGrowth)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap := by
  obtain ⟨overhead, initBound, stepBound, initAsymptotic, stepAsymptotic, runs⟩ := space
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run⟩ :=
    runs x inputs legal (historyWidth overhead requestWords x inputs) (Nat.le_refl _)
  exact ⟨replies, finish, finalWorld.heap, run.erase.source⟩

end Complexity.Language.Session
