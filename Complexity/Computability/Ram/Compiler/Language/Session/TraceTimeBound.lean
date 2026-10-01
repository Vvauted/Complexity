/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound

/-!
# Uniform time for reply-constrained session traces

A protocol may determine the next request from the preceding actual reply.
An externally chosen request list cannot express that requirement by itself.
Here a fixed acceptance relation constrains the requests and the actual replies
of the same initialized RAM trace.

The environment is universally quantified proof data, separate from the public
configuration. Neither its hidden state nor the accepted history reaches the
initializer or chooses its memory or word-width policy. Each step receives only
its current encoded request and actual retained source state.

The acceptance relation is chosen by the protocol author, not the candidate.
It must state the intended information, transition and stopping rules. For a
fixed deterministic environment this can describe the complete closed loop.
Existence of an accepted trace alone is not universal correctness against a
nondeterministic or adaptive adversary. This interface does not add an evaluator,
execute the environment as solver code, or price arbitrary callbacks.

Costs are the existing actual preloaded invocation counts, including
initialization. External input preparation, port transport, serialization and
a continuously running I/O driver remain outside this boundary. Independent
source correctness can use the same acceptance relation without a RAM budget.
-/

namespace Complexity.Language.Session

universe u v z

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ω : α → Type v} {ι : Type z} {request : List Ty} {response : Ty}

/-- A uniform bound on actual initialized traces satisfying a fixed protocol's
acceptance relation. Hidden environments are quantified separately from the
public input. Every legal environment and configuration-admitted width must
have a fitting accepted execution; fitting and capacity are not input filters. -/
def TraceTimeO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.width overhead x ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
        Ram.LanguageCompiler.Session.Runs session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          (inputs.map encode) replies finish finalWorld steps ∧
        accept x environment inputs replies ∧ steps ≤ bound (size x environment)

/-- State a protocol's mathematical growth expression directly, keeping the
environment proof-side and counting the same accepted RAM computation. -/
abbrev TraceTimeOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → ω x → Nat) : Prop :=
  session.TraceTimeO encode valid accept growth id

/-- A bounded accepted RAM trace projects to an accepted trace of the same source
entries. No separate solver, chosen mathematical implementation or state loader
is used by this projection. -/
theorem TraceTimeO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → ω x → Nat} {growth : Nat → Nat}
    (time : session.TraceTimeO encode valid accept size growth)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap ∧ accept x environment inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨inputs, replies, finish, finalWorld, steps, fits, run, accepted, cost⟩ :=
    runs x environment legal (Complexity.Program.width overhead x) (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap, run.source, accepted⟩

end Complexity.Language.Session
