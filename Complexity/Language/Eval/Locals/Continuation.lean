/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals
import Complexity.Language.Eval.Continuation

/-!
# Returning from an ordinary-local block observation

The ordinary-local observation retains all local values on every exit. At a
function continuation boundary, only normal completion passes those values to
the remaining statements. Return and fault exit immediately with the actual
final heap. `Stmt.evalWith_eq_observe` connects these two existing views using
the native exception transformer; it does not interpret the source again.
-/

namespace Complexity.Language.Stmt

/-- Connect a lossless block observation to the existing function continuation.
Normal completion uses the actual updated locals. Return and fault skip `next`
without discarding the block's heap effects. -/
theorem evalWith_eq_observe {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Locals : Type} (view : Env Γ ≃ Locals) (stmt : Stmt signatures Γ result)
    (program : Program signatures) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    stmt.evalWith program entry next = (do
      let (control, locals) ← ExceptT.lift (observe view stmt program (view entry))
      match control with
      | .normal => next (view.symm locals)
      | .returned value => pure value
      | .fault error => throw error) := by
  funext heap
  simp only [evalWith, ExceptT.lift, ExceptT.mk, Bind.bind, ExceptT.bind,
    Functor.map, StateT.map, StateT.bind, observe, action, Equiv.symm_apply_apply,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some, ExceptT.bindCont]
  apply congrArg ((stmt.eval program ⟨entry, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨finalLocals, finalHeap⟩, control⟩
  cases control <;>
    simp only [Prod.swap, Pure.pure, Part.bind_some, Equiv.symm_apply_apply]
  all_goals rfl

end Complexity.Language.Stmt
