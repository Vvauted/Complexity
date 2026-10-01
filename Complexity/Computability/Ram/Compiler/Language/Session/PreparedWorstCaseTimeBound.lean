/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Prepared
import Complexity.Computability.Ram.Compiler.Language.Session.Width

/-!
# Uniform realization of every permitted prepared source trace

An existential accepted trace does not cover all choices of a nondeterministic
environment. This interface instead lifts every protocol-permitted successful
source trace to the same RAM trace, with one global asymptotic bound. Inputs,
replies and their return-time heaps, final source state and final source heap
are retained. No favorable branch may replace a more expensive source branch.

This is a resource requirement, not total correctness: the client must separately
prove that every legal interaction branch terminates successfully. Restricting
only already-successful traces would otherwise admit vacuous claims.

The author fixes the current-input preparation and raw scale words. Those words
may include an external size unknown to the source, but only the declared
configuration initializes memory. At every admitted width the same existing
source trace must be realized; source behavior cannot use the width as advice.
Preparation costs require actual invocations, not candidate price annotations.
External traversal, transport and continuous driver control remain separate.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type u} {ω : α → Type v} {request : List Ty} {response : Ty}

/-- Every permitted source trace has an actual RAM realization at every admitted
width. Termination for all legal environment choices is a separate obligation. -/
def PreparedWorstCaseTimeO
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x environment, valid x environment →
      ∀ inputs replies finish finalHeap,
        session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
        accept x environment inputs replies →
        ∀ w, ∀ admitted : widthWith overhead x (admissionWords x environment) ≤ w,
          ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
              (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
            Ram.LanguageCompiler.Session.PreparedRuns session prepare
              (Complexity.Program.Input.args x)
              (Ram.LanguageCompiler.Session.State.ofInput x w (widthWith_base admitted))
              inputs replies finish finalWorld steps ∧
            finalWorld.heap = finalHeap ∧ steps ≤ bound (size x environment)

/-- Use the mathematical multivariate growth expression without an extra size
wrapper, while retaining every permitted trace and its actual observations. -/
abbrev PreparedWorstCaseTimeOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → ω x → Nat) : Prop :=
  session.PreparedWorstCaseTimeO sourcePrepare prepare admissionWords valid accept growth id

/-- Any given permitted successful source execution therefore has a RAM
realization. The same final heap and private source state are preserved. -/
theorem PreparedWorstCaseTimeO.realizes
    {session : Session (Complexity.Program.Input.params α) request response}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop}
    {admissionWords : (x : α) → ω x → Array Nat}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → ω x → Nat} {growth : Nat → Nat}
    (time : session.PreparedWorstCaseTimeO sourcePrepare prepare admissionWords
      valid accept size growth)
    {x : α} {environment : ω x} (legal : valid x environment)
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {finalHeap : Heap}
    (source : session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
      (Complexity.Program.Input.heap x) inputs replies finish finalHeap)
    (accepted : accept x environment inputs replies) :
    ∃ w, ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        Ram.LanguageCompiler.Session.PreparedRuns session prepare
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          inputs replies finish finalWorld steps ∧ finalWorld.heap = finalHeap := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨finalWorld, steps, run, sameHeap, counted⟩ :=
    runs x environment legal inputs replies finish finalHeap source accepted
      (widthWith overhead x (admissionWords x environment)) (Nat.le_refl _)
  exact ⟨_, widthWith_base (Nat.le_refl _), finalWorld, steps, run, sameHeap⟩

end Complexity.Language.Session
