/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Model
import Ram.Verification.StateM

/-!
# Native stateful models restricted by an invariant

An existing native `StateM` implementation can operate on the standard subtype
of states satisfying a preserved invariant. The preservation proof constructs
the final subtype value; native `modifyGet` retains the original return value
and state computation. There is no new evaluator, state datatype or runtime
check, and the RAM statement is unchanged.

This is useful for existing invariant-bearing types such as fixed-length
lists. Once restricted, the native stateful model can be transported through
genuine mathlib equivalences using `Refines.stateM_equiv`. Subtype restriction
does not pretend that forgetting the invariant is itself a bijection.
-/

namespace Ram.Source.Refines

universe u

variable {α σ : Type u} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : σ → State w → Prop} {outputRep : α × σ → State w → Prop}
variable {model : StateM σ α}

/-- Restrict an implementation to states satisfying an invariant proved to
hold after the actual model computation. Both original representations and
the returned value are retained through the subtype's ordinary value map. -/
theorem stateM_subtype
    (h : Refines program heapLimit depth stmt inputRep outputRep model.run)
    (P : σ → Prop) (preserves : ∀ state, P state → P (model.run state).2) :
    Refines program heapLimit depth stmt
      (fun state : {s : σ // P s} => inputRep state.val)
      (fun result : α × {s : σ // P s} => outputRep (result.1, result.2.val))
      (modifyGet (fun state : {s : σ // P s} =>
        let result := model.run state.val
        (result.1, (⟨result.2, preserves state.val state.property⟩ : {s : σ // P s}))) :
        StateM {s : σ // P s} α).run := by
  apply h.transfer
    (inputRel := fun old (next : {s : σ // P s}) => old = next.val)
    (outputRel := fun old (next : α × {s : σ // P s}) => old = (next.1, next.2.val))
  · intro state s represented
    exact ⟨state.val, represented, rfl⟩
  · rintro result next finish rfl represented
    exact represented
  · rintro state next rfl
    rfl

end Ram.Source.Refines
