/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Prepared
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound

/-!
# Uniform time for prepared, reply-constrained traces

The protocol author fixes a preparation backed by actual counted invocations,
its source correspondence, and causal acceptance. Hidden environment data is
universally quantified but never initializer input or width advice. Current
heap-backed feedback is prepared only after the preceding actual reply.

The same accepted execution supplies initialization, preparation and candidate
callback costs. This extends the preloaded-invocation boundary; it does not price
external traversal, transport, scalar loading or continuous driver control.
An arbitrary preparation predicate does not certify a new operation's price.
Use actual execution relations, such as compiled linked-list preparation, not
a candidate-selected decoder or cost annotation.
-/

namespace Complexity.Language.Session

universe u v
variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type u} {ω : α → Type v} {request : List Ty} {response : Ty}

/-- A fixed current-input preparation and the selected source session have a
uniform accepted invocation bound at every configuration-admitted word width.
Readiness and actual fitting prepared arguments are conclusions of the run. -/
def PreparedTraceTimeO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (valid : (x : α) → ω x → Prop)
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
        Ram.LanguageCompiler.Session.PreparedRuns session prepare
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          inputs replies finish finalWorld steps ∧
        accept x environment inputs replies ∧ steps ≤ bound (size x environment)

/-- Write the mathematical size expression directly for the same prepared run. -/
abbrev PreparedTraceTimeOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → ω x → Nat) : Prop :=
  session.PreparedTraceTimeO prepare valid accept growth id

/-- The concrete loader's correspondence projects the same accepted RAM trace
to source. No alternative successful history is chosen for correctness. -/
theorem PreparedTraceTimeO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → ω x → Nat} {growth : Nat → Nat}
    (preparation_source : ∀ {w heapLimit} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps,
      prepare input current args prepared steps →
        sourcePrepare input current.heap args prepared.heap)
    (time : session.PreparedTraceTimeO prepare valid accept size growth)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
        accept x environment inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨inputs, replies, finish, finalWorld, steps, run, accepted, cost⟩ :=
    runs x environment legal (Complexity.Program.width overhead x) (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap,
    run.source preparation_source, accepted⟩

end Complexity.Language.Session
