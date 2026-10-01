/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.Prepared
import Complexity.Computability.Ram.Compiler.Language.Session.Width

/-!
# Uniform time for prepared sequential request histories

Each fixed external request is prepared only at its actual call boundary, in
the heap retained by earlier calls. The public raw words of the finite history
supply the existing logarithmic width policy without entering initialization.
At fixed width the initial memory is still exactly the configuration's memory.

The same actual initialized RAM trace supplies the requested output property
and its total invocation count, including real input preparation. Global bounds
cannot choose another successful history or omit expensive replies. Readiness,
fitting arguments and capacity are conclusions for all legal histories and
admitted widths, never extra filters on legal inputs.

The interface describes sequential external inputs, not adaptive adversarial
games. External traversal, port loading, serialization and continuous driver
control remain outside the counted preloaded calls.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}

/-- Uniform time and observations of the same prepared sequential execution.
The protocol author fixes both the real preparation and raw width words. -/
def PreparedHistoryTimeO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyWidth overhead requestWords x inputs ≤ w,
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        Ram.LanguageCompiler.Session.PreparedRuns session prepare
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps ∧
        post x inputs replies ∧ steps ≤ bound (size x inputs)

/-- Spell a multivariate mathematical growth expression directly, with the
same actual execution, output property and fixed public width policy. -/
abbrev PreparedHistoryTimeOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (growth : α → List ι → Nat) : Prop :=
  session.PreparedHistoryTimeO prepare requestWords valid post growth id

/-- The concrete preparation's erasure transfers the observed property of the
same counted RAM history to source. Future inputs remain absent from init. -/
theorem PreparedHistoryTimeO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {requestWords : ι → Array Nat} {valid : α → List ι → Prop}
    {post : α → List ι → List (Value response × Heap) → Prop}
    {size : α → List ι → Nat} {growth : Nat → Nat}
    (preparation_source : ∀ {w heapLimit} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps,
      prepare input current args prepared steps →
        sourcePrepare input current.heap args prepared.heap)
    (time : session.PreparedHistoryTimeO prepare requestWords valid post size growth)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalHeap : Heap),
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
      post x inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨replies, finish, finalWorld, steps, run, observed, cost⟩ :=
    runs x inputs legal (historyWidth overhead requestWords x inputs) (Nat.le_refl _)
  exact ⟨replies, finish, finalWorld.heap, run.source preparation_source, observed⟩

end Complexity.Language.Session
