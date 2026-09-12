/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Language.Eval.Locals.Specification

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

/-- A linear potential using the existing loop rule's normal-round and
false-exit charges. An early return still has its separate cost obligation. -/
def whileLinearBound (guard body remaining : Nat) : Nat :=
  (guard + body + 10) * remaining + guard + 11

/-- The linear potential always pays for the final false guard. -/
theorem whileLinearBound_exit (guard body remaining : Nat) :
    guard + 11 ≤ whileLinearBound guard body remaining := by
  unfold whileLinearBound
  omega

/-- Decreasing the remaining-round count by at least one pays for a normal
guard/body round and leaves the same potential for the next iteration. -/
theorem whileLinearBound_step (guard body : Nat) {next remaining : Nat}
    (decreases : next + 1 ≤ remaining) :
    guard + body + whileLinearBound guard body next + 10 ≤
      whileLinearBound guard body remaining := by
  have scaled := Nat.mul_le_mul_left (guard + body + 10) decreases
  simp only [Nat.mul_add, Nat.mul_one] at scaled
  unfold whileLinearBound
  omega

/-- One available round also pays for a direct function return from the body.
No increment or subsequent guard is charged as an executed operation here. -/
theorem whileLinearBound_return (guard body : Nat) {remaining : Nat}
    (positive : 0 < remaining) :
    guard + body + 17 ≤ whileLinearBound guard body remaining := by
  have paid := whileLinearBound_step guard body (next := 0) positive
  unfold whileLinearBound at paid ⊢
  omega

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

/-- Bound a loop directly from its independent guard and body contracts.
The fixed-capture view is the generated ordinary-local view. Mathematical
postconditions, not execution equations, supply the invariant and potential
obligations. The contracts remain budget-free; this rule only transports the
existing loop cost rule and its actual false-exit and early-return charges. -/
theorem while_contract_fixed {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured : Type} (view : Env Γ ≃ Mutable × Captured)
    {program : Complexity.Language.Program signatures}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    (guardFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control .bool},
      Complexity.Language.Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control result},
      Complexity.Language.Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured)
    {invariant bodyPre : Mutable → Heap → Prop}
    {guardPost : Mutable → Heap → Bool → Mutable × Captured → Heap → Prop}
    {bodyNormal : Mutable → Heap → Mutable × Captured → Heap → Prop}
    {bodyReturned : Mutable → Heap → Value result → Mutable × Captured → Heap → Prop}
    {potential guardBound : Mutable → Heap → Nat}
    {bodyBound : Mutable → Heap → Mutable → Heap → Nat}
    (guardSpec : Complexity.Language.Stmt.BlockSpec
      (fun mutable => Complexity.Language.Stmt.observe view guard program (mutable, captures))
      invariant (fun _ _ _ _ => False) guardPost)
    (bodySpec : Complexity.Language.Stmt.BlockSpec
      (fun mutable => Complexity.Language.Stmt.observe view body program (mutable, captures))
      bodyPre bodyNormal bodyReturned)
    (enterBody : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyPre afterGuard afterGuardHeap)
    (guardCost : ∀ mutable heap, invariant mutable heap →
      StmtCostBound program guard ⟨view.symm (mutable, captures), heap⟩
        (guardBound mutable heap))
    (bodyCost : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      StmtCostBound program body ⟨view.symm (afterGuard, captures), afterGuardHeap⟩
        (bodyBound mutable heap afterGuard afterGuardHeap))
    (preserve : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyNormal afterGuard afterGuardHeap (afterBody, captures) afterBodyHeap →
      invariant afterBody afterBodyHeap)
    (falseExit : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap false (afterGuard, captures) afterGuardHeap →
      guardBound mutable heap + 11 ≤ potential mutable heap)
    (normalStep : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyNormal afterGuard afterGuardHeap (afterBody, captures) afterBodyHeap →
      guardBound mutable heap + bodyBound mutable heap afterGuard afterGuardHeap +
        potential afterBody afterBodyHeap + 10 ≤ potential mutable heap)
    (returnExit : ∀ mutable heap afterGuard afterGuardHeap finalMutable finalHeap value,
      invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyReturned afterGuard afterGuardHeap value (finalMutable, captures) finalHeap →
      guardBound mutable heap + bodyBound mutable heap afterGuard afterGuardHeap + 17 ≤
        potential mutable heap)
    {mutable : Mutable} {heap : Heap} (initial : invariant mutable heap) :
    StmtCostBound program (.while guard body) ⟨view.symm (mutable, captures), heap⟩
      (potential mutable heap) := by
  apply while_observe_fixed view (Equiv.refl _) guardFrame bodyFrame captures
    (invariant := invariant) (potential := potential) (guardBound := guardBound)
    (bodyBound := bodyBound)
  · exact guardCost
  · intro mutable heap afterGuard afterGuardHeap current tested
    exact bodyCost _ _ _ _ current (guardSpec.post_of_eq current tested)
  · intro mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap current tested iterated
    have ready := guardSpec.post_of_eq current tested
    exact preserve _ _ _ _ _ _ current ready
      (bodySpec.post_of_eq (enterBody _ _ _ _ current ready) iterated)
  · intro mutable heap afterGuard afterGuardHeap current tested
    exact falseExit _ _ _ _ current (guardSpec.post_of_eq current tested)
  · intro mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap current tested iterated
    have ready := guardSpec.post_of_eq current tested
    exact normalStep _ _ _ _ _ _ current ready
      (bodySpec.post_of_eq (enterBody _ _ _ _ current ready) iterated)
  · intro mutable heap afterGuard afterGuardHeap finalMutable finalHeap value current tested iterated
    have ready := guardSpec.post_of_eq current tested
    exact returnExit _ _ _ _ _ _ value current ready
      (bodySpec.post_of_eq (enterBody _ _ _ _ current ready) iterated)
  · exact initial

/-- Uniform component bounds and a decreasing round count give a linear loop
budget. The source contracts supply the actual transition facts; the shared
cost rule pays for normal continuation, false exit and an early function return.
Neither the round count nor the budget is used to define source correctness. -/
theorem while_contract_fixed_linear
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured : Type} (view : Env Γ ≃ Mutable × Captured)
    {program : Complexity.Language.Program signatures}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    (guardFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control .bool},
      Complexity.Language.Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : Complexity.Language.State Γ} {control : Control result},
      Complexity.Language.Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured)
    {invariant bodyPre : Mutable → Heap → Prop}
    {guardPost : Mutable → Heap → Bool → Mutable × Captured → Heap → Prop}
    {bodyNormal : Mutable → Heap → Mutable × Captured → Heap → Prop}
    {bodyReturned : Mutable → Heap → Value result → Mutable × Captured → Heap → Prop}
    (guardSpec : Complexity.Language.Stmt.BlockSpec
      (fun mutable => Complexity.Language.Stmt.observe view guard program (mutable, captures))
      invariant (fun _ _ _ _ => False) guardPost)
    (bodySpec : Complexity.Language.Stmt.BlockSpec
      (fun mutable => Complexity.Language.Stmt.observe view body program (mutable, captures))
      bodyPre bodyNormal bodyReturned)
    (enterBody : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyPre afterGuard afterGuardHeap)
    (guardBound bodyBound : Nat) (remaining : Mutable → Heap → Nat)
    (guardCost : ∀ mutable heap, invariant mutable heap →
      StmtCostBound program guard ⟨view.symm (mutable, captures), heap⟩ guardBound)
    (bodyCost : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      StmtCostBound program body ⟨view.symm (afterGuard, captures), afterGuardHeap⟩ bodyBound)
    (preserve : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyNormal afterGuard afterGuardHeap (afterBody, captures) afterBodyHeap →
      invariant afterBody afterBodyHeap)
    (decreases : ∀ mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap,
      invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      bodyNormal afterGuard afterGuardHeap (afterBody, captures) afterBodyHeap →
      remaining afterBody afterBodyHeap + 1 ≤ remaining mutable heap)
    (positive : ∀ mutable heap afterGuard afterGuardHeap, invariant mutable heap →
      guardPost mutable heap true (afterGuard, captures) afterGuardHeap →
      0 < remaining mutable heap)
    {mutable : Mutable} {heap : Heap} (initial : invariant mutable heap) :
    StmtCostBound program (.while guard body) ⟨view.symm (mutable, captures), heap⟩
      (whileLinearBound guardBound bodyBound (remaining mutable heap)) := by
  apply while_contract_fixed view guardFrame bodyFrame captures guardSpec bodySpec enterBody
    (guardBound := fun _ _ => guardBound) (bodyBound := fun _ _ _ _ => bodyBound)
    (potential := fun mutable heap => whileLinearBound guardBound bodyBound (remaining mutable heap))
  · exact guardCost
  · exact bodyCost
  · exact preserve
  · intro mutable heap afterGuard afterGuardHeap current tested
    exact whileLinearBound_exit guardBound bodyBound (remaining mutable heap)
  · intro mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap current tested iterated
    exact whileLinearBound_step guardBound bodyBound
      (decreases mutable heap afterGuard afterGuardHeap afterBody afterBodyHeap current tested iterated)
  · intro mutable heap afterGuard afterGuardHeap finalMutable finalHeap value current tested returned
    exact whileLinearBound_return guardBound bodyBound
      (positive mutable heap afterGuard afterGuardHeap current tested)
  · exact initial

end StmtCostBound

end Ram.LanguageCompiler
