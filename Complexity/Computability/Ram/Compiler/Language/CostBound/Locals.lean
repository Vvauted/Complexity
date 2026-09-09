/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Language.Eval.Locals

/-!
# Loop cost bounds in ordinary local coordinates

The existing source cost rules apply through the same lossless local view used
by named block observations. Mathematical invariants and potentials mention
ordinary locals and heaps; actual observation equations supply the effects of
the guard and body. This transports `StmtCostBound.while`, without another cost
interpreter, a new termination argument or a second proof of result contents.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem observe_eq_some_of_exec {signatures : List Signature} {Γ : List Ty}
    {result : Ty} {Locals : Type} (view : Env Γ ≃ Locals)
    {program : Complexity.Language.Program signatures}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program stmt entry finish control) :
    Complexity.Language.Stmt.observe view stmt program (view entry.locals) entry.heap =
      Part.some ((control, view finish.locals), finish.heap) := by
  apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
  simpa only [Equiv.symm_apply_apply] using execution

namespace StmtCostBound

/-- Prove a potential bound using the actual named guard/body observations.
The equations retain changed locals and heaps. Only completed source paths are
used, so the cost proof need not re-establish termination or operation validity. -/
theorem while_observe {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Locals : Type} (view : Env Γ ≃ Locals)
    {program : Complexity.Language.Program signatures}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Locals → Heap → Prop} {potential guardBound : Locals → Heap → Nat}
    {bodyBound : Locals → Heap → Locals → Heap → Nat}
    (guardCost : ∀ locals heap, invariant locals heap →
      StmtCostBound program guard ⟨view.symm locals, heap⟩ (guardBound locals heap))
    (bodyCost : ∀ locals heap afterGuard afterGuardHeap, invariant locals heap →
      Complexity.Language.Stmt.observe view guard program locals heap =
        Part.some ((.returned true, afterGuard), afterGuardHeap) →
      StmtCostBound program body ⟨view.symm afterGuard, afterGuardHeap⟩
        (bodyBound locals heap afterGuard afterGuardHeap))
    (preserve : ∀ locals heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant locals heap →
      Complexity.Language.Stmt.observe view guard program locals heap =
        Part.some ((.returned true, afterGuard), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program afterGuard afterGuardHeap =
        Part.some ((.normal, afterBody), afterBodyHeap) → invariant afterBody afterBodyHeap)
    (falseExit : ∀ locals heap afterGuard afterGuardHeap, invariant locals heap →
      Complexity.Language.Stmt.observe view guard program locals heap =
        Part.some ((.returned false, afterGuard), afterGuardHeap) →
      guardBound locals heap + 11 ≤ potential locals heap)
    (normalStep : ∀ locals heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant locals heap →
      Complexity.Language.Stmt.observe view guard program locals heap =
        Part.some ((.returned true, afterGuard), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program afterGuard afterGuardHeap =
        Part.some ((.normal, afterBody), afterBodyHeap) →
      guardBound locals heap + bodyBound locals heap afterGuard afterGuardHeap +
        potential afterBody afterBodyHeap + 10 ≤ potential locals heap)
    (returnExit : ∀ locals heap afterGuard afterGuardHeap finalLocals finalHeap value,
      invariant locals heap →
      Complexity.Language.Stmt.observe view guard program locals heap =
        Part.some ((.returned true, afterGuard), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program afterGuard afterGuardHeap =
        Part.some ((.returned value, finalLocals), finalHeap) →
      guardBound locals heap + bodyBound locals heap afterGuard afterGuardHeap + 17 ≤
        potential locals heap)
    {locals : Locals} {heap : Heap} (initial : invariant locals heap) :
    StmtCostBound program (.while guard body) ⟨view.symm locals, heap⟩
      (potential locals heap) := by
  have bound : StmtCostBound program (.while guard body) ⟨view.symm locals, heap⟩
      (potential (view (view.symm locals)) heap) := by
    apply StmtCostBound.while
      (invariant := fun state => invariant (view state.locals) state.heap)
      (potential := fun state => potential (view state.locals) state.heap)
      (guardBound := fun state => guardBound (view state.locals) state.heap)
      (bodyBound := fun state afterGuard =>
        bodyBound (view state.locals) state.heap (view afterGuard.locals) afterGuard.heap)
    · intro state initial
      simpa only [Equiv.symm_apply_apply] using @guardCost (view state.locals) state.heap initial
    · intro state afterGuard initial test
      simpa only [Equiv.symm_apply_apply] using
        @bodyCost (view state.locals) state.heap (view afterGuard.locals) afterGuard.heap
          initial (observe_eq_some_of_exec view test)
    · intro state afterGuard afterBody initial test iteration
      exact preserve _ _ _ _ _ _ initial
        (observe_eq_some_of_exec view test) (observe_eq_some_of_exec view iteration)
    · intro state afterGuard initial test
      exact falseExit _ _ _ _ initial (observe_eq_some_of_exec view test)
    · intro state afterGuard afterBody initial test iteration
      exact normalStep _ _ _ _ _ _ initial
        (observe_eq_some_of_exec view test) (observe_eq_some_of_exec view iteration)
    · intro state afterGuard finish value initial test iteration
      exact returnExit _ _ _ _ _ _ value initial
        (observe_eq_some_of_exec view test) (observe_eq_some_of_exec view iteration)
    · simpa only [Equiv.apply_symm_apply] using initial
  simp only [Equiv.apply_symm_apply] at bound
  exact @bound

end StmtCostBound

end Ram.LanguageCompiler
