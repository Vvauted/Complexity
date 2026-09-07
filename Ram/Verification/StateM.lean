/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Std.Do.Triple.Basic
import Ram.Verification.Refinement

/-!
# Native Lean stateful specifications for RAM implementations

The mathematical model of an implementation may be an ordinary `StateM`
program. Its result is the usual pair of returned value and final abstract
state. Clients can prove native `Std.Do.Triple` specifications using
`mvcgen`, registered `@[spec]` lemmas, and ordinary Lean/mathlib reasoning.

`Refines.stateM_spec` transfers those specifications through an existing
implementation refinement. It uses Std's own `WP` interpretation of `StateM`;
there is no alternative evaluator or new `WP` instance. Safe terminating RAM
execution still comes from the refinement, not from the abstract triple.
In particular, native loop verification does not discharge RAM heap bounds,
word overflow conditions, stack safety, or compiler-derived running time.
-/

namespace Ram.Source.Refines

universe u

variable {α σ : Type u} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : σ → State w → Prop} {outputRep : α × σ → State w → Prop}

/-- Transfer a native `StateM` Hoare triple to the corresponding RAM
implementation, retaining both the return value and final abstract state. -/
theorem stateM_spec {model : StateM σ α}
    (h : Refines program heapLimit depth stmt inputRep outputRep model.run)
    {P : σ → Prop} {Q : α → σ → Prop}
    (specification : Std.Do.Triple (ps := .arg σ .pure) model (fun state => ⟨P state⟩)
      (fun result state => ⟨Q result state⟩, ⟨⟩)) (initial : σ) (hp : P initial) :
    TotalContract program heapLimit depth stmt (inputRep initial)
      (fun target => ∃ result, outputRep result target ∧ Q result.1 result.2) := by
  apply h.spec (Q := fun _ result => Q result.1 result.2) ?_ initial hp
  intro state hs
  exact specification state hs

end Ram.Source.Refines
