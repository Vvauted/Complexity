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

/-- Fixed lexical captures need not occur in the author's loop invariant,
potential or component bounds. The guard and body frames preserve them along
the same actual observations; mutable locals and heap effects remain visible.
This rule reuses `while_observe`, including its false-exit and early-return
charges, and supplies no new termination or result-correctness requirement. -/
theorem while_observe_fixed {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Locals Mutable Captured : Type} (view : Env Γ ≃ Locals)
    (regroup : Locals ≃ Mutable × Captured)
    {program : Complexity.Language.Program signatures}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    (guardFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control .bool},
      Complexity.Language.Exec program guard entry finish control →
        (regroup (view finish.locals)).2 = (regroup (view entry.locals)).2)
    (bodyFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control result},
      Complexity.Language.Exec program body entry finish control →
        (regroup (view finish.locals)).2 = (regroup (view entry.locals)).2)
    (captures : Captured)
    {invariant : Mutable → Heap → Prop} {potential guardBound : Mutable → Heap → Nat}
    {bodyBound : Mutable → Heap → Mutable → Heap → Nat}
    (guardCost : ∀ mutable heap, invariant mutable heap →
      StmtCostBound program guard ⟨view.symm (regroup.symm (mutable, captures)), heap⟩
        (guardBound mutable heap))
    (bodyCost : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      Complexity.Language.Stmt.observe view guard program (regroup.symm (mutable, captures)) heap =
        Part.some ((.returned true, regroup.symm (afterGuard, captures)), afterGuardHeap) →
      StmtCostBound program body ⟨view.symm (regroup.symm (afterGuard, captures)), afterGuardHeap⟩
        (bodyBound mutable heap afterGuard afterGuardHeap))
    (preserve : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      Complexity.Language.Stmt.observe view guard program (regroup.symm (mutable, captures)) heap =
        Part.some ((.returned true, regroup.symm (afterGuard, captures)), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program
          (regroup.symm (afterGuard, captures)) afterGuardHeap =
        Part.some ((.normal, regroup.symm (afterBody, captures)), afterBodyHeap) →
      invariant afterBody afterBodyHeap)
    (falseExit : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      Complexity.Language.Stmt.observe view guard program (regroup.symm (mutable, captures)) heap =
        Part.some ((.returned false, regroup.symm (afterGuard, captures)), afterGuardHeap) →
      guardBound mutable heap + 11 ≤ potential mutable heap)
    (normalStep : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      Complexity.Language.Stmt.observe view guard program (regroup.symm (mutable, captures)) heap =
        Part.some ((.returned true, regroup.symm (afterGuard, captures)), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program
          (regroup.symm (afterGuard, captures)) afterGuardHeap =
        Part.some ((.normal, regroup.symm (afterBody, captures)), afterBodyHeap) →
      guardBound mutable heap + bodyBound mutable heap afterGuard afterGuardHeap +
        potential afterBody afterBodyHeap + 10 ≤ potential mutable heap)
    (returnExit : ∀ mutable heap afterGuard afterGuardHeap finalMutable finalHeap value,
      invariant mutable heap →
      Complexity.Language.Stmt.observe view guard program (regroup.symm (mutable, captures)) heap =
        Part.some ((.returned true, regroup.symm (afterGuard, captures)), afterGuardHeap) →
      Complexity.Language.Stmt.observe view body program
          (regroup.symm (afterGuard, captures)) afterGuardHeap =
        Part.some ((.returned value, regroup.symm (finalMutable, captures)), finalHeap) →
      guardBound mutable heap + bodyBound mutable heap afterGuard afterGuardHeap + 17 ≤
        potential mutable heap)
    {mutable : Mutable} {heap : Heap} (initial : invariant mutable heap) :
    StmtCostBound program (.while guard body)
      ⟨view.symm (regroup.symm (mutable, captures)), heap⟩ (potential mutable heap) := by
  have unpack {locals : Locals} (fixed : (regroup locals).2 = captures) :
      ∃ mutable, locals = regroup.symm (mutable, captures) := by
    refine ⟨(regroup locals).1, ?_⟩
    apply regroup.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl fixed
  have repack {τ : Ty} {stmt : Complexity.Language.Stmt signatures Γ τ}
      (frame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control τ},
        Complexity.Language.Exec program stmt entry finish control →
          (regroup (view finish.locals)).2 = (regroup (view entry.locals)).2)
      {locals after : Locals} {heap finishHeap : Heap} {control : Control τ}
      (fixed : (regroup locals).2 = captures)
      (observed : Complexity.Language.Stmt.observe view stmt program locals heap =
        Part.some ((control, after), finishHeap)) :
      ∃ mutable, after = regroup.symm (mutable, captures) := by
    apply unpack
    have preserved : (regroup after).2 = (regroup locals).2 := by
      simpa only [Equiv.apply_symm_apply] using
        frame (Complexity.Language.Stmt.observe_eq_some_iff.mp observed)
    exact preserved.trans fixed
  have bound : StmtCostBound program (.while guard body)
      ⟨view.symm (regroup.symm (mutable, captures)), heap⟩
      (potential (regroup (regroup.symm (mutable, captures))).1 heap) := by
    apply while_observe view
      (invariant := fun locals heap =>
        (regroup locals).2 = captures ∧ invariant (regroup locals).1 heap)
      (potential := fun locals heap => potential (regroup locals).1 heap)
      (guardBound := fun locals heap => guardBound (regroup locals).1 heap)
      (bodyBound := fun locals heap afterGuard afterGuardHeap =>
        bodyBound (regroup locals).1 heap (regroup afterGuard).1 afterGuardHeap)
    · intro locals heap initial
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      simp only [Equiv.apply_symm_apply]
      exact @guardCost mutable heap current
    · intro locals heap afterGuard afterGuardHeap initial tested
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      obtain ⟨afterMutable, rfl⟩ := repack guardFrame initial.1 tested
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      simp only [Equiv.apply_symm_apply]
      exact @bodyCost mutable heap afterMutable afterGuardHeap current tested
    · intro locals heap afterGuard afterGuardHeap afterBody afterBodyHeap initial tested iterated
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      obtain ⟨guardMutable, rfl⟩ := repack guardFrame initial.1 tested
      obtain ⟨bodyMutable, rfl⟩ := repack bodyFrame (by simp) iterated
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      constructor
      · simp
      · simpa only [Equiv.apply_symm_apply] using
          preserve mutable heap guardMutable afterGuardHeap bodyMutable afterBodyHeap
            current tested iterated
    · intro locals heap afterGuard afterGuardHeap initial tested
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      obtain ⟨afterMutable, rfl⟩ := repack guardFrame initial.1 tested
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      simpa only [Equiv.apply_symm_apply] using
        falseExit mutable heap afterMutable afterGuardHeap current tested
    · intro locals heap afterGuard afterGuardHeap afterBody afterBodyHeap initial tested iterated
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      obtain ⟨guardMutable, rfl⟩ := repack guardFrame initial.1 tested
      obtain ⟨bodyMutable, rfl⟩ := repack bodyFrame (by simp) iterated
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      simpa only [Equiv.apply_symm_apply] using
        normalStep mutable heap guardMutable afterGuardHeap bodyMutable afterBodyHeap
          current tested iterated
    · intro locals heap afterGuard afterGuardHeap finalLocals finalHeap value initial tested iterated
      obtain ⟨mutable, rfl⟩ := unpack initial.1
      obtain ⟨guardMutable, rfl⟩ := repack guardFrame initial.1 tested
      obtain ⟨finalMutable, rfl⟩ := repack bodyFrame (by simp) iterated
      have current : invariant mutable heap := by
        simpa only [Equiv.apply_symm_apply] using initial.2
      simpa only [Equiv.apply_symm_apply] using
        returnExit mutable heap guardMutable afterGuardHeap finalMutable finalHeap value
          current tested iterated
    · exact ⟨by simp, by simpa only [Equiv.apply_symm_apply] using initial⟩
  simp only [Equiv.apply_symm_apply] at bound
  exact @bound

end StmtCostBound

end Ram.LanguageCompiler
