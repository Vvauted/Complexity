/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.StateM.Basic

/-!
# Composing native stateful models

`Refines.stateM_bind` composes RAM implementations using ordinary `StateM`
bind. The intermediate representation contains both the first returned value
and its final abstract state; clients need not repack those pairs manually.

The second RAM statement is fixed. Its model and representation precondition
may be indexed by the first returned value, but the executable is not selected
or specialized by a proof-only value. Native `StateT.run_bind` supplies the
model equation and the existing `Refines.seq` supplies actual safe execution.
-/

namespace Ram.Source.Refines

universe u

variable {α β σ : Type u} {program : Program} {heapLimit depth : Nat}
variable {first second : Stmt} {inputRep : σ → State w → Prop}
variable {middleRep : α × σ → State w → Prop} {outputRep : β × σ → State w → Prop}

/-- Sequential RAM implementations refine native monadic bind. The second
model may depend on the first return value; its RAM statement remains fixed.
That value is available through the intermediate representation, not through
ghost-dependent generation of a new statement. -/
theorem stateM_bind {model : StateM σ α} {next : α → StateM σ β}
    (ha : Refines program heapLimit depth first inputRep middleRep model.run)
    (hb : ∀ value, Refines program heapLimit depth second
      (fun state => middleRep (value, state)) outputRep (next value).run) :
    Refines program heapLimit depth (.seq first second) inputRep outputRep
      (model >>= next).run := by
  have secondRef : Refines program heapLimit depth second middleRep outputRep
      (fun middle => (next middle.1).run middle.2) := by
    rintro ⟨value, state⟩
    exact hb value state
  exact (ha.seq secondRef).congr_fun (fun state => (StateT.run_bind model next state).symm)

end Ram.Source.Refines
