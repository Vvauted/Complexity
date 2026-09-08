/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.StateM.Basic

/-!
# Mathematical postconditions retained by compositional refinements

`Refines.with_postcondition` attaches a proved property of the ordinary model
result without leaving the refinement interface. The same pure function and
RAM statement remain available to `Refines.seq`; the strengthened output
representation supplies the mathematical fact to the next implementation.

`Refines.stateM_spec_refines` does the same for native `Std.Do.Triple` proofs,
so a postcondition proved using `mvcgen` can be carried into `stateM_bind`.
Unlike `stateM_spec`, this interface does not fix one initial state or hide the
model result behind an existential contract postcondition.

These properties describe the chosen mathematical result, not every value
that could represent the same machine state. Representation relations may be
noninjective, including word encodings. No runtime assertion is inserted, and
the existing safe terminating execution and separately proved costs are not
changed. A property depending on the initial mathematical input can capture a
fixed ghost in its closure or retain that input in the result's ghost model.
-/

namespace Ram.Source.Refines

variable {α β : Type*} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : α → State w → Prop} {outputRep : β → State w → Prop} {f : α → β}

/-- Retain a pure mathematical postcondition in the representation used by
subsequent refinements. The input's mathematical precondition is explicit;
no injectivity or converse interpretation of the output representation is assumed. -/
theorem with_postcondition
    (h : Refines program heapLimit depth stmt inputRep outputRep f)
    {P : α → Prop} {Q : β → Prop} (property : ∀ x, P x → Q (f x)) :
    Refines program heapLimit depth stmt
      (fun x s => inputRep x s ∧ P x)
      (fun y t => outputRep y t ∧ Q y) f := by
  rintro x s ⟨represented, hp⟩
  exact ((h x).mono_post (fun _ result => ⟨result, property x hp⟩)) s represented

universe u

/-- Carry a native stateful Hoare postcondition into later refinement
composition. Both the returned value and final abstract state remain the
ordinary pair produced by `StateM.run`, ready for `Refines.stateM_bind`. -/
theorem stateM_spec_refines {α σ : Type u} {model : StateM σ α}
    {inputRep : σ → State w → Prop} {outputRep : α × σ → State w → Prop}
    (h : Refines program heapLimit depth stmt inputRep outputRep model.run)
    {P : σ → Prop} {Q : α → σ → Prop}
    (specification : Std.Do.Triple (ps := .arg σ .pure) model (fun state => ⟨P state⟩)
      (fun result state => ⟨Q result state⟩, ⟨⟩)) :
    Refines program heapLimit depth stmt
      (fun state s => inputRep state s ∧ P state)
      (fun result t => outputRep result t ∧ Q result.1 result.2) model.run :=
  h.with_postcondition (fun state hs => specification state hs)

end Ram.Source.Refines
