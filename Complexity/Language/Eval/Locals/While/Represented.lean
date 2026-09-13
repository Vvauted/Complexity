/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Specification

/-!
# While contracts with a heap-indexed mathematical state

A mathematical state may describe arrays, records or other observations of the
actual source locals and heap. It need not encode the source state, determine
its pointers, or be recoverable from arbitrary source values. A normal round
supplies a new mathematical state and proves well-founded progress there.

The guard and body retain their actual intermediate heaps. Their contracts may
update observations of immutable handles as well as mutable locals; no frame
follows merely from keeping a handle or extending the heap. False guards and
early body returns establish their respective postconditions directly.
The rule reuses the existing source while semantics and needs no time budget.
-/

namespace Complexity.Language

universe u

namespace TotalWP

/-- Well-founded progress on a related mathematical state proves the actual
source loop. The relation need not be a function in either direction. -/
theorem while_rel {Model : Type u} {signatures : List Signature} {Γ : List Ty}
    {result : Ty} {program : Program signatures}
    {guard : Stmt signatures Γ .bool} {body : Stmt signatures Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop}
    (stateRel : Model → State Γ → Prop) (invariant : Model → Prop)
    {relation : Model → Model → Prop} (wellFounded : WellFounded relation)
    (step : ∀ model current, invariant model → stateRel model current →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body
              (fun afterBody => ∃ next, invariant next ∧ stateRel next afterBody ∧
                relation next model) returned afterGuard
          else normal afterGuard) current)
    {model : Model} {entry : State Γ}
    (initial : invariant model) (represented : stateRel model entry) :
    TotalWP program (.while guard body) normal returned entry := by
  induction model using wellFounded.induction generalizing entry with
  | h model ih =>
      apply (while_iff guard body).mpr
      apply (step model entry initial represented).mono_post (fun _ h => h.elim)
      intro again afterGuard property
      cases again with
      | false => exact property
      | true =>
          refine property.mono_post ?_ (fun _ _ h => h)
          rintro afterBody ⟨next, valid, related, smaller⟩
          exact ih next smaller valid related

end TotalWP

namespace Stmt

open scoped Part.TotalCorrectness

/-- Compose actual guard and body contracts while measuring progress only on
their mathematical model. `ready` keeps the complete round's starting state,
including the heap before an effectful guard. It is not a heap-frame assertion.
Each normal body exit supplies its own related next model. -/
theorem observe_while_rel_contract {Model : Type u} {signatures : List Signature}
    {Γ : List Ty} {result : Ty} {Locals : Type}
    (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (stateRel : Model → Locals → Heap → Prop) (invariant : Model → Prop)
    {relation : Model → Model → Prop} (wellFounded : WellFounded relation)
    (ready : Model → Locals → Heap → Locals → Heap → Prop)
    (normal : Locals → Heap → Prop) (returned : Value result → Locals → Heap → Prop)
    (guardSpec : ∀ model, invariant model →
      BlockSpec (fun locals => observe view guard program locals) (stateRel model)
        (fun _ _ _ _ => False)
        (fun start heap again afterGuard finish =>
          if again then ready model start heap afterGuard finish
          else normal afterGuard finish))
    (bodySpec : ∀ model start heap, invariant model → stateRel model start heap →
      BlockSpec (fun locals => observe view body program locals) (ready model start heap)
        (fun _ _ afterBody finish => ∃ next, invariant next ∧
          stateRel next afterBody finish ∧ relation next model)
        (fun _ _ => returned))
    (model : Model) (initial : invariant model) :
    BlockSpec (fun locals => observe view (.while guard body) program locals)
      (stateRel model) (fun _ _ => normal) (fun _ _ => returned) := by
  intro locals heap represented
  have step : ∀ currentModel (entry : State Γ), invariant currentModel →
      stateRel currentModel (view entry.locals) entry.heap →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body
              (fun afterBody => ∃ next, invariant next ∧
                stateRel next (view afterBody.locals) afterBody.heap ∧
                  relation next currentModel)
              (fun value finish => returned value (view finish.locals) finish.heap) afterGuard
          else normal (view afterGuard.locals) afterGuard.heap) entry := by
    intro currentModel entry valid observed
    have guarded := TotalWP.of_blockSpec view id (guardSpec currentModel valid) observed
      (normal := fun _ => False)
      (returned := fun again afterGuard =>
        if again then
          TotalWP program body
            (fun afterBody => ∃ next, invariant next ∧
              stateRel next (view afterBody.locals) afterBody.heap ∧ relation next currentModel)
            (fun value finish => returned value (view finish.locals) finish.heap) afterGuard
        else normal (view afterGuard.locals) afterGuard.heap)
      (fun _ _ impossible => impossible.elim) (by
        intro again afterGuard afterGuardHeap property
        cases again with
        | false =>
            simpa only [Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply] using property
        | true =>
            apply TotalWP.of_blockSpec view id
              (bodySpec currentModel (view entry.locals) entry.heap valid observed) property
            · intro output finish next
              simpa only [Equiv.apply_symm_apply] using next
            · intro value output finish post
              simpa only [Equiv.apply_symm_apply] using post)
    simpa only [id_eq, Equiv.symm_apply_apply] using guarded
  have actual := TotalWP.while_rel
    (fun currentModel state => stateRel currentModel (view state.locals) state.heap)
    invariant wellFounded step initial
    (entry := ⟨view.symm locals, heap⟩)
    (by simpa only [Equiv.apply_symm_apply] using represented)
  obtain ⟨finish, control, execution, property⟩ := actual
  have executed : observe view (.while guard body) program locals heap =
      Part.some ((control, view finish.locals), finish.heap) :=
    observe_eq_some_iff.mpr (by
      simpa only [Equiv.symm_apply_apply] using execution)
  apply Part.TotalCorrectness.stateT_triple_of_eq executed
  cases control <;> exact property

end Stmt

end Complexity.Language
