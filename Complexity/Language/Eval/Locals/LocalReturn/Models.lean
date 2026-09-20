/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Specification

/-!
# Mathematical contracts for local-return rounds

These consequence rules connect a heap-indexed mathematical state to the
existing visible completion contracts. The guard contract explicitly preserves
its model and actual heap and may use the invariant to justify its accesses.
A body may change the heap: only its continuing
branch supplies another invariant and a decrease. Its completed branch retains
the returned value, final mathematical state and actual heap.

Neither rule introduces an evaluator, a pure body transition or a resource
budget. The frontend composes these contracts using the existing local-return
while rule and its checked execution frames.
-/

namespace Complexity.Language.Stmt.BlockSpec

universe u

/-- Carry a heap-dependent invariant through a guard whose supplied contract
preserves the mathematical state and heap. No equality of raw locals follows
from their mathematical representation. -/
theorem guard_model_invariant {Model : Type u} {Visible Locals : Type}
    {action : Visible → StateT Heap Part (Control .bool × Locals)}
    (visible : Locals → Visible) (stateRel : Model → Visible → Heap → Prop)
    (invariant normal : Model → Heap → Prop) (test : Model → Bool)
    (guardSpec : ∀ model heap, invariant model heap →
      BlockSpec action (fun start current => stateRel model start current ∧ current = heap)
        (fun _ _ _ _ => False)
        (fun _ entry again output finish => ∃ next,
          stateRel next (visible output) finish ∧ again = test model ∧
            next = model ∧ finish = entry))
    (exit : ∀ model heap, invariant model heap → test model = false → normal model heap)
    (model : Model) :
    BlockSpec action (fun start heap => stateRel model start heap ∧ invariant model heap)
      (fun _ _ _ _ => False)
      (fun _ _ again output finish =>
        if again then stateRel model (visible output) finish ∧
          invariant model finish ∧ test model = true
        else ∃ next, stateRel next (visible output) finish ∧ normal next finish) := by
  rintro start heap ⟨represented, valid⟩
  refine ((guardSpec model heap valid).mono
    (returned' := fun _ _ again output finish =>
      if again then stateRel model (visible output) finish ∧
        invariant model finish ∧ test model = true
      else ∃ next, stateRel next (visible output) finish ∧ normal next finish)
    (fun _ _ initial => initial) (fun _ _ _ _ _ impossible => impossible) ?_)
      start heap ⟨represented, rfl⟩
  rintro _ startHeap again output finish ⟨_, sameStart⟩
    ⟨next, represented, decision, sameModel, sameHeap⟩
  subst next startHeap finish
  cases again with
  | true => exact ⟨represented, valid, decision.symm⟩
  | false => exact ⟨model, represented, exit model heap valid decision.symm⟩

/-- Turn supplied mathematical body contracts into the continuing/completed
postcondition of the existing local-return rule. The invariant and decrease
are required only on continuing rounds; both branches retain their actual
final heap and mathematical representation. -/
theorem body_model_invariant {Model : Type u} {Visible Locals LocalResult : Type}
    {result : Ty} {action : Visible → StateT Heap Part (Control result × Locals)}
    (visible : Locals → Visible) (pending : Locals → Option LocalResult)
    (stateRel : Model → Visible → Heap → Prop) (invariant : Model → Heap → Prop)
    (test : Model → Bool) (step relation : Model → Model → Prop)
    (completed : LocalResult → Model → Heap → Prop)
    (bodySpec : ∀ model heap, invariant model heap → test model = true →
      BlockSpec action (fun start current => stateRel model start current ∧ current = heap)
        (fun _ _ output finish => match pending output with
          | none => ∃ next, stateRel next (visible output) finish ∧
              step model next ∧ invariant next finish
          | some value => ∃ next, stateRel next (visible output) finish ∧
              completed value next finish)
        (fun _ _ _ _ _ => False))
    (decreases : ∀ model next heap, invariant model heap → test model = true →
      step model next → relation next model)
    (model : Model) :
    BlockSpec action
      (fun start heap => stateRel model start heap ∧ invariant model heap ∧ test model = true)
      (fun _ _ output finish => match pending output with
        | none => ∃ next, True ∧
            (stateRel next (visible output) finish ∧ invariant next finish) ∧ relation next model
        | some value => ∃ next, stateRel next (visible output) finish ∧
            completed value next finish)
      (fun _ _ _ _ _ => False) := by
  rintro start heap ⟨represented, valid, active⟩
  refine ((bodySpec model heap valid active).mono
    (normal' := fun _ _ output finish => match pending output with
      | none => ∃ next, True ∧
          (stateRel next (visible output) finish ∧ invariant next finish) ∧ relation next model
      | some value => ∃ next, stateRel next (visible output) finish ∧
          completed value next finish)
    (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible))
      start heap ⟨represented, rfl⟩
  intro _ _ output finish _ updated
  cases stopped : pending output with
  | none =>
      simp only [stopped] at updated ⊢
      obtain ⟨next, related, advanced, preserved⟩ := updated
      exact ⟨next, trivial, ⟨related, preserved⟩, decreases model next heap valid active advanced⟩
  | some value => simpa only [stopped] using updated

end Complexity.Language.Stmt.BlockSpec
