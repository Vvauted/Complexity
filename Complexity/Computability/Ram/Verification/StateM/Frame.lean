/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Frame
import Complexity.Computability.Ram.Verification.StateM.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Framing native stateful models inside a larger state

An implementation of an ordinary `StateM` model also implements the native
`modifyGet` operation that runs that model on the left side of a product state.
The returned value is unchanged and the right-hand model is retained through
the existing heap frame rule. The resulting native stateful computation can
be composed using `Refines.stateM_bind` and specified with Std's usual triples.

Only the ordinary model runs inside `modifyGet`; this is not an extra RAM
instruction or a new evaluator. The source statement stays fixed. The same
safe execution and proved endpoint frame justify the enlarged representation;
disjointness, heap bounds and any original register conditions remain explicit.
-/

namespace Ram.Source.Refines

universe u

variable {α σ γ : Type u} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : σ → State w → Prop} {outputRep : α × σ → State w → Prop}
variable {model : StateM σ α}

/-- Lift a native stateful implementation to a product state while retaining an
unrelated represented heap object. The standard returned-value/final-state
pair is reassociated internally, so subsequent native binds need no adapter. -/
theorem stateM_frame_heap
    (h : Refines program heapLimit depth stmt inputRep outputRep model.run)
    (observed : γ → Set (Word w)) (writes : σ → Set (Word w))
    (heapModel : γ → (Word w → Word w) → Prop)
    (depends : ∀ z before after, Set.EqOn after before (observed z) →
      heapModel z before → heapModel z after)
    (unchanged : ∀ state entry finish, inputRep state entry →
      SafeExec program heapLimit depth stmt entry finish →
      outputRep (model.run state) finish →
      Set.EqOn finish.mem entry.mem (writes state)ᶜ) :
    Refines program heapLimit depth stmt
      (fun (state, z) s => inputRep state s ∧ heapModel z s.mem ∧
        Disjoint (observed z) (writes state))
      (fun result t => outputRep (result.1, result.2.1) t ∧ heapModel result.2.2 t.mem)
      (modifyGet (fun (state, z) =>
        let result := model.run state
        (result.1, (result.2, z))) : StateM (σ × γ) α).run := by
  have framed := h.frame_heap observed writes heapModel depends unchanged
  exact (framed.equiv (Equiv.refl (σ × γ)) (Equiv.prodAssoc α σ γ)).congr_fun
    (fun _ => rfl)

end Ram.Source.Refines
