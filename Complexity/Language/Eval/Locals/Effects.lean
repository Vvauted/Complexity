/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Effects
import Complexity.Language.Eval.Locals.Continuation
import Init.Control.Lawful.Instances

/-!
# Local frames at an observation continuation

Continuations need agree only on actual outcomes of the same source block.
`Stmt.observe_bind_congr` and its native exception-transformer form make that
principle available without unfolding `Part` at each generated loop site.

The execution supplied to the equality premise retains the complete final
locals, heap and control. A frontend can use `Exec.get_eq` to replace protected
output fields by their original values while leaving mutable fields intact.
Returns and faults are not filtered out, and undefined observations remain
undefined. No alternative observer or execution relation is introduced.
-/

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty} {Locals α : Type}

/-- Replace a continuation when it agrees on every actual observed outcome,
at that outcome's actual final heap. No equality on unreachable outcomes is
required, and the observed block need not terminate. -/
theorem observe_bind_congr (view : Env Γ ≃ Locals) (stmt : Stmt signatures Γ result)
    (program : Program signatures) (locals : Locals)
    (first second : Control result × Locals → StateT Heap Part α)
    (same : ∀ initialHeap finalHeap control finalLocals,
      Exec program stmt ⟨view.symm locals, initialHeap⟩
        ⟨view.symm finalLocals, finalHeap⟩ control →
      first (control, finalLocals) finalHeap = second (control, finalLocals) finalHeap) :
    (observe view stmt program locals >>= first) =
      (observe view stmt program locals >>= second) := by
  classical
  funext initialHeap
  change (observe view stmt program locals initialHeap).bind
      (fun outcome => first outcome.1 outcome.2) =
    (observe view stmt program locals initialHeap).bind
      (fun outcome => second outcome.1 outcome.2)
  by_cases defined : (observe view stmt program locals initialHeap).Dom
  · let outcome := (observe view stmt program locals initialHeap).get defined
    have member : outcome ∈ observe view stmt program locals initialHeap := Part.get_mem defined
    calc
      _ = first outcome.1 outcome.2 := Part.bind_of_mem member _
      _ = second outcome.1 outcome.2 :=
        same initialHeap outcome.2 outcome.1.1 outcome.1.2 (mem_observe_iff.mp member)
      _ = _ := (Part.bind_of_mem member (fun outcome => second outcome.1 outcome.2)).symm
  · simp only [Part.eq_none_iff'.mpr defined, Part.bind_none]

/-- The same actual-outcome congruence after lifting the observation into the
existing native exception action. The premise may use `Exec.get_eq` to restore
readonly coordinates; source faults and returns still carry their actual heap. -/
theorem observe_bind_congr_except (view : Env Γ ≃ Locals)
    (stmt : Stmt signatures Γ result) (program : Program signatures) (locals : Locals)
    (first second : Control result × Locals → ExceptT Fault (StateT Heap Part) α)
    (same : ∀ initialHeap finalHeap control finalLocals,
      Exec program stmt ⟨view.symm locals, initialHeap⟩
        ⟨view.symm finalLocals, finalHeap⟩ control →
      first (control, finalLocals) finalHeap = second (control, finalLocals) finalHeap) :
    (ExceptT.lift (observe view stmt program locals) >>= first) =
      (ExceptT.lift (observe view stmt program locals) >>= second) := by
  change (ExceptT.lift (observe view stmt program locals) >>= first).run =
    (ExceptT.lift (observe view stmt program locals) >>= second).run
  rw [ExceptT.run_bind_lift, ExceptT.run_bind_lift]
  exact observe_bind_congr view stmt program locals
    (fun outcome => (first outcome).run) (fun outcome => (second outcome).run) same

end Complexity.Language.Stmt
