/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Bounded
import Complexity.Computability.Ram.Compiler.Language.Session.Width

/-!
# Separate uniform bounds for initialization and each callback

Initialization and each request have their own asymptotic envelope on the same
persistent execution. An expensive first request cannot spend unused setup
budget. The envelopes and width multiplier are global, independent of the
configuration, history and machine width.

The fixed raw request-word presentation contributes only to machine admission.
Initialization still receives only the registered configuration, with its
existing heap and memory. Each later entry receives just the current request
and its actual retained state. Input fitting, allocation capacity and termination
are obligations on every legal history, not assumptions excluding hard inputs.

These bounds count actual preloaded RAM invocations, including their wrappers.
They do not charge an external streaming driver, port transport, serialization,
initial input loading or arena preparation. Source correctness is independent.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}

/-- Separate uniform time bounds for actual initialization and each invocation.
The interface author fixes both the current-request encoding and its raw words;
neither may supply computed advice or candidate-selected padding. Reference
loading requires its own justified protocol, not a proof-side request encoder. -/
def PhaseTimeO (session : Session (Complexity.Program.Input.params α) request response)
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
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        Ram.LanguageCompiler.Session.BoundedRuns session encode
          (fun input => stepBound (stepSize x input)) (initBound (initSize x))
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps

/-- State the two possibly multivariate growth expressions directly. In
particular, a constant step growth gives one uniform per-request bound, not an
amortized total bound. Neither expression is evaluated by the source program. -/
abbrev PhaseTimeOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop) (initGrowth : α → Nat) (stepGrowth : α → ι → Nat) : Prop :=
  session.PhaseTimeO encode requestWords valid initGrowth stepGrowth id id

/-- Restrict legal histories while retaining both global bounds, the width
policy, the actual stateful computation and its separately charged phases. -/
theorem PhaseTimeO.mono_valid
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {requestWords : ι → Array Nat}
    {valid valid' : α → List ι → Prop} {initSize : α → Nat} {stepSize : α → ι → Nat}
    {initGrowth stepGrowth : Nat → Nat}
    (time : session.PhaseTimeO encode requestWords valid initSize stepSize initGrowth stepGrowth)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.PhaseTimeO encode requestWords valid' initSize stepSize initGrowth stepGrowth := by
  obtain ⟨overhead, initBound, stepBound, initAsymptotic, stepAsymptotic, runs⟩ := time
  exact ⟨overhead, initBound, stepBound, initAsymptotic, stepAsymptotic,
    fun x inputs legal => runs x inputs (restrict x inputs legal)⟩

end Complexity.Language.Session
