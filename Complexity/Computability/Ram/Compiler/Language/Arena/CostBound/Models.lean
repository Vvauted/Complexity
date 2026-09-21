/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Loop
import Complexity.Language.Eval.Locals.While.Represented

/-!
# Arena cost bounds from mathematical loop contracts

The guard and body contracts used for source correctness also transport cost
bounds through their actual intermediate heaps. Authors supply a mathematical
invariant, component bounds and a remaining-budget inequality. The representation
need not determine source handles, and the heap need not remain unchanged.

This is a consequence of the existing arena loop rule, not another traversal or
cost semantics. It bounds supplied completed executions without a second
termination proof. Word ranges, capacity and arena readiness remain separate.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

universe u

/-- Reuse the mathematical guard and normal-body contracts of source correctness
to bound the same allocating loop. Component budgets and the potential depend
only on the mathematical state; their certificates concern the actual heaps.
No well-founded relation or proposed budget is needed by the source contracts. -/
theorem while_model {Model : Type u} {signatures : List Signature}
    {Γ : List Ty} {result : Ty} {Locals : Type}
    (view : Env Γ ≃ Locals) (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (stateRel : Model → Locals → Heap → Prop) (test : Model → Bool) (next : Model → Model)
    (guardSpec : ∀ model,
      Complexity.Language.Stmt.BlockSpec
        (fun locals => Complexity.Language.Stmt.observe view guard program locals) (stateRel model)
        (fun _ _ _ _ => False)
        (fun _ _ again output finish => again = test model ∧ stateRel model output finish))
    (bodySpec : ∀ model, test model = true →
      Complexity.Language.Stmt.BlockSpec
        (fun locals => Complexity.Language.Stmt.observe view body program locals) (stateRel model)
        (fun _ _ output finish => stateRel (next model) output finish)
        (fun _ _ _ _ _ => False))
    (invariant : Model → Prop)
    (preserved : ∀ model, invariant model → test model = true → invariant (next model))
    {w heapLimit depth : Nat} (guardBound bodyBound potential : Model → Nat)
    (guardCost : ∀ model locals heap, invariant model → stateRel model locals heap →
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩
        (guardBound model))
    (bodyCost : ∀ model locals heap, invariant model → test model = true →
      stateRel model locals heap →
      StmtArenaCostBound program w heapLimit depth body ⟨view.symm locals, heap⟩
        (bodyBound model))
    (falseExit : ∀ model, invariant model → test model = false →
      guardBound model + 11 ≤ potential model)
    (normalStep : ∀ model, invariant model → test model = true →
      guardBound model + bodyBound model + potential (next model) + 10 ≤ potential model)
    {model : Model} {locals : Locals} {heap : Heap}
    (initial : invariant model) (represented : stateRel model locals heap) :
    StmtArenaCostBound program w heapLimit depth (.while guard body)
      ⟨view.symm locals, heap⟩ (potential model) := by
  have guardPost (model : Model) (start finish : Complexity.Language.State Γ)
      (again : Bool) (related : stateRel model (view start.locals) start.heap)
      (execution : Complexity.Language.Exec program guard start finish (.returned again)) :
      again = test model ∧ stateRel model (view finish.locals) finish.heap := by
    apply (guardSpec model).post_of_exec view id
      (finish := finish) (control := .returned again) related
    simpa only [id_eq, Equiv.symm_apply_apply] using execution
  apply «while»
    (invariant := fun model state =>
      invariant model ∧ stateRel model (view state.locals) state.heap)
    (guardBound := fun model _ => guardBound model)
    (bodyBound := fun model _ _ => bodyBound model)
    (potential := fun model _ => potential model) (initialIndex := model)
  · rintro model state ⟨valid, related⟩
    have bounded : StmtArenaCostBound program w heapLimit depth guard
        ⟨view.symm (view state.locals), state.heap⟩ (guardBound model) :=
      guardCost model (view state.locals) state.heap valid related
    simp only [Equiv.symm_apply_apply] at bounded
    exact @bounded
  · rintro model state afterGuard ⟨valid, related⟩ tested
    obtain ⟨active, guarded⟩ := guardPost model state afterGuard true related tested
    have bounded : StmtArenaCostBound program w heapLimit depth body
        ⟨view.symm (view afterGuard.locals), afterGuard.heap⟩ (bodyBound model) :=
      bodyCost model (view afterGuard.locals) afterGuard.heap valid active.symm guarded
    simp only [Equiv.symm_apply_apply] at bounded
    exact @bounded
  · rintro model state afterGuard ⟨valid, related⟩ tested
    exact falseExit model valid (guardPost model state afterGuard false related tested).1.symm
  · rintro model state afterGuard afterBody ⟨valid, related⟩ tested iterated
    obtain ⟨active, guarded⟩ := guardPost model state afterGuard true related tested
    have advanced : stateRel (next model) (view afterBody.locals) afterBody.heap := by
      apply (bodySpec model active.symm).post_of_exec view id
        (finish := afterBody) (control := .normal) guarded
      simpa only [id_eq, Equiv.symm_apply_apply] using iterated
    exact ⟨next model, ⟨preserved model valid active.symm, advanced⟩,
      normalStep model valid active.symm⟩
  · rintro model state afterGuard finish value ⟨_, related⟩ tested returned
    obtain ⟨active, guarded⟩ := guardPost model state afterGuard true related tested
    have impossible : False := by
      apply (bodySpec model active.symm).post_of_exec view id
        (finish := finish) (control := .returned value) guarded
      simpa only [id_eq, Equiv.symm_apply_apply] using returned
    exact impossible.elim
  · exact ⟨initial, by simpa only [Equiv.apply_symm_apply] using represented⟩

end Ram.LanguageCompiler.StmtArenaCostBound
