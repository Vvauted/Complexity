/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Width

/-!
# Reply-constrained traces with a public schedule

A session may start before the sizes of its later invocations are announced.
Its initial configuration alone then cannot determine a sufficient word width.
The fixed public schedule supplies the existing `historyWidth` scale without
becoming a source argument or changing the configuration's initial memory.

Schedule and hidden environment are quantified separately. The interface author
fixes the schedule's raw-word presentation; it must not encode computed answers,
hidden data, candidate actions or padding chosen by the implementation. The
acceptance relation specifies when scheduled announcements occur and how actual
replies determine subsequent feedback. Each source call still receives only its
current request and actual retained state.

All configuration/schedule-admitted widths must have an accepted real execution.
Neither fitting nor capacity is an extra legality assumption. At fixed width the
existing `ofInput_history_independent` theorem gives exactly the same initial
memory for different schedules. This finite-history admission policy is not a
dynamically growing-word machine or an executable streaming driver.

As for `Session.TraceTimeO`, existential accepted traces describe fixed
deterministic environments, not universal adversarial choices. Costs sum actual
preloaded invocations, including initialization. External loading, transport and
serialization remain outside this boundary.
-/

namespace Complexity.Language.Session

universe u v z r

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {σ : Type v} {ω : α → List σ → Type z} {ι : Type r}
variable {request : List Ty} {response : Ty}

/-- Uniform time for an actual accepted trace, admitted using only the initial
configuration and a fixed public schedule. Hidden environment data and the
candidate's generated transcript cannot select the admission words. -/
def ScheduledTraceTimeO
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
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.Runs session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          (inputs.map encode) replies finish finalWorld steps ∧
        accept x schedule environment inputs replies ∧
        steps ≤ bound (size x schedule environment)

/-- State the mathematical growth expression directly for the same scheduled
trace; neither the expression nor the future schedule is evaluated by source. -/
abbrev ScheduledTraceTimeOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (scheduleWords : σ → Array Nat)
    (valid : (x : α) → (schedule : List σ) → ω x schedule → Prop)
    (accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → (schedule : List σ) → ω x schedule → Nat) : Prop :=
  session.ScheduledTraceTimeO encode scheduleWords valid accept growth id

/-- Project the same accepted RAM trace to the selected source entries.
The public schedule justifies width; it is not passed to initialization. -/
theorem ScheduledTraceTimeO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {scheduleWords : σ → Array Nat}
    {valid : (x : α) → (schedule : List σ) → ω x schedule → Prop}
    {accept : (x : α) → (schedule : List σ) → ω x schedule →
      List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → (schedule : List σ) → ω x schedule → Nat}
    {growth : Nat → Nat}
    (time : session.ScheduledTraceTimeO encode scheduleWords valid accept size growth)
    {x : α} {schedule : List σ} {environment : ω x schedule}
    (legal : valid x schedule environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧
      accept x schedule environment inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨inputs, replies, finish, finalWorld, steps, fits, run, accepted, cost⟩ :=
    runs x schedule environment legal (historyWidth overhead scheduleWords x schedule)
      (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩

end Complexity.Language.Session
