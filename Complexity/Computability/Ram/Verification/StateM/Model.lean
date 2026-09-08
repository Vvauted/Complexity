/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.StateM.Basic
import Mathlib.Control.Monad.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Native stateful models in equivalent mathematical coordinates

`Refines.stateM_equiv` changes the state and return types of an ordinary
`StateM` model through mathlib equivalences. It uses `StateT.equiv` and
`Equiv.arrowCongr`, not a new state monad or record/lens datatype. A product
state can therefore be presented as a user's record, or rearranged with
`Equiv.prodComm` and `Equiv.prodAssoc`, while retaining the implementation.

This changes mathematical coordinates only. It neither converts the actual
heap nor assumes that its representation is bijective. A physical change of
layout still requires its own implementation and cost proof. For a lossy
model change, use `Refines.transfer` with a proved relation instead.
-/

namespace Ram.Source.Refines

universe u v

/-- Reuse a native stateful implementation through standard equivalences of
its mathematical state and return value. The result is again native `StateM`,
so it can be used directly by `stateM_bind` and native Hoare specifications. -/
theorem stateM_equiv {α σ : Type u} {β τ : Type v}
    {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
    {inputRep : σ → State w → Prop} {outputRep : α × σ → State w → Prop}
    {model : StateM σ α}
    (h : Refines program heapLimit depth stmt inputRep outputRep model.run)
    (state : σ ≃ τ) (result : α ≃ β) :
    Refines program heapLimit depth stmt
      (fun next => inputRep (state.symm next))
      (fun next => outputRep (result.symm next.1, state.symm next.2))
      (StateT.equiv (m₁ := Id) (m₂ := Id)
        (Equiv.arrowCongr state (Equiv.prodCongr result state)) model).run :=
  h.equiv state (Equiv.prodCongr result state)

end Ram.Source.Refines
