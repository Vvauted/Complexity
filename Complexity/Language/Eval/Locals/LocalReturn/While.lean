/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.LocalReturn

/-!
# While contracts with local completion

A continuing iteration supplies a related mathematical state and well-founded
progress. An iteration which stores a local result instead proves its exit
postcondition: the actual next guard returns false, without requiring an
invariant or a decrease for that completed state.

The rules retain the original guard, body, complete locals, heaps and normal
source control. A supplied execution of the stopped guard must certify the
real false-guard step; no new phase type, evaluator or loop is introduced.
`LocalReturn.guard_stopped` supplies this fact for the existing guarded source
fragment. Source faults, guard fallthrough and enclosing function returns are
not successful local completion.
-/

namespace Complexity.Language

universe u

namespace Stmt.LocalReturn

/-- A stored local result makes the actual guarded fragment return false,
without evaluating the original test or changing the state. -/
theorem guard_stopped {signatures : List Signature} {Γ : List Ty} {τ : Ty}
    {program : Program signatures} (pending : Atom Γ (.option τ))
    (test : Stmt signatures Γ .bool) (state : State Γ) (value : Value τ)
    (stopped : pending.eval state.locals = some value) :
    Exec program (guard pending test) state state (.returned false) := by
  apply (Stmt.observe_eq_some_iff
    (view := Equiv.refl (Env Γ))
    (locals := state.locals) (finalLocals := state.locals)
    (heap := state.heap) (finalHeap := state.heap)).mp
  rw [observe_guard_some (Equiv.refl (Env Γ))
    program pending test state.locals value stopped]
  rfl

end Stmt.LocalReturn

namespace TotalWP

/-- Prove the actual loop using well-founded progress only for continuing
iterations. A stored result closes the loop through its real false guard,
retaining normal source control and the completed state's actual heap. -/
theorem while_completion {Model : Type u} {signatures : List Signature}
    {Γ : List Ty} {τ result : Ty} {program : Program signatures}
    {guard : Stmt signatures Γ .bool} {body : Stmt signatures Γ result}
    (pending : Atom Γ (.option τ))
    (stateRel : Model → State Γ → Prop) (invariant : Model → Prop)
    {relation : Model → Model → Prop} (wellFounded : WellFounded relation)
    (post : Option (Value τ) → State Γ → Prop)
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Exec program guard state state (.returned false))
    (step : ∀ model current, invariant model → stateRel model current →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body
              (fun afterBody => match pending.eval afterBody.locals with
                | none => ∃ next, invariant next ∧ stateRel next afterBody ∧
                    relation next model
                | some value => post (some value) afterBody)
              (fun _ _ => False) afterGuard
          else post (pending.eval afterGuard.locals) afterGuard) current)
    {model : Model} {entry : State Γ}
    (initial : invariant model) (represented : stateRel model entry) :
    TotalWP program (.while guard body)
      (fun finish => post (pending.eval finish.locals) finish)
      (fun _ _ => False) entry := by
  induction model using wellFounded.induction generalizing entry with
  | h model ih =>
      apply (while_iff guard body).mpr
      apply (step model entry initial represented).mono_post (fun _ h => h.elim)
      intro again afterGuard property
      cases again with
      | false => exact property
      | true =>
          refine property.mono_post ?_ (fun _ _ h => h)
          intro afterBody completed
          cases stopped : pending.eval afterBody.locals with
          | none =>
              simp only [stopped] at completed
              obtain ⟨next, valid, related, smaller⟩ := completed
              exact ih next smaller valid related
          | some value =>
              simp only [stopped] at completed
              refine ⟨afterBody, .normal,
                .whileFalse (stoppedGuard afterBody value stopped), ?_⟩
              change post (pending.eval afterBody.locals) afterBody
              simpa only [stopped] using completed

end TotalWP

namespace Stmt

open scoped Part.TotalCorrectness

/-- Compose ordinary-local guard and body contracts for the same loop. The
mathematical relation may describe heap-backed values and need not encode the
source environment. Only a body with no stored local result must supply a
smaller model; a stored result supplies the exit postcondition directly.
`inputLocals` merely selects complete entry coordinates for the existing action. -/
theorem observe_while_completion_contract {Model : Type u}
    {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    {Input Locals : Type} (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (pending : Atom Γ (.option τ))
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Exec program guard state state (.returned false))
    (stateRel : Model → Locals → Heap → Prop) (invariant : Model → Prop)
    {relation : Model → Model → Prop} (wellFounded : WellFounded relation)
    (ready : Model → Locals → Heap → Locals → Heap → Prop)
    (post : Option (Value τ) → Locals → Heap → Prop)
    (guardSpec : ∀ model, invariant model →
      BlockSpec (fun locals => observe view guard program locals) (stateRel model)
        (fun _ _ _ _ => False)
        (fun start heap again afterGuard finish =>
          if again then ready model start heap afterGuard finish
          else post (pending.eval (view.symm afterGuard)) afterGuard finish))
    (bodySpec : ∀ model start heap, invariant model → stateRel model start heap →
      BlockSpec (fun locals => observe view body program locals) (ready model start heap)
        (fun _ _ afterBody finish => match pending.eval (view.symm afterBody) with
          | none => ∃ next, invariant next ∧ stateRel next afterBody finish ∧
              relation next model
          | some value => post (some value) afterBody finish)
        (fun _ _ _ _ _ => False))
    (inputLocals : Input → Locals) (model : Model) (initial : invariant model) :
    BlockSpec (fun input => observe view (.while guard body) program (inputLocals input))
      (fun input heap => stateRel model (inputLocals input) heap)
      (fun _ _ output finish => post (pending.eval (view.symm output)) output finish)
      (fun _ _ _ _ _ => False) := by
  intro input heap represented
  have step : ∀ currentModel (entry : State Γ), invariant currentModel →
      stateRel currentModel (view entry.locals) entry.heap →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body
              (fun afterBody => match pending.eval afterBody.locals with
                | none => ∃ next, invariant next ∧
                    stateRel next (view afterBody.locals) afterBody.heap ∧
                      relation next currentModel
                | some value => post (some value) (view afterBody.locals) afterBody.heap)
              (fun _ _ => False) afterGuard
          else post (pending.eval afterGuard.locals)
            (view afterGuard.locals) afterGuard.heap) entry := by
    intro currentModel entry valid observed
    have guarded := TotalWP.of_blockSpec view id (guardSpec currentModel valid) observed
      (normal := fun _ => False)
      (returned := fun again afterGuard =>
        if again then
          TotalWP program body
            (fun afterBody => match pending.eval afterBody.locals with
              | none => ∃ next, invariant next ∧
                  stateRel next (view afterBody.locals) afterBody.heap ∧
                    relation next currentModel
              | some value => post (some value) (view afterBody.locals) afterBody.heap)
            (fun _ _ => False) afterGuard
        else post (pending.eval afterGuard.locals)
          (view afterGuard.locals) afterGuard.heap)
      (fun _ _ impossible => impossible.elim) (by
        intro again afterGuard afterGuardHeap property
        cases again with
        | false =>
            simpa only [Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply] using property
        | true =>
            apply TotalWP.of_blockSpec view id
              (bodySpec currentModel (view entry.locals) entry.heap valid observed) property
            · intro output finish next
              cases completion : pending.eval (view.symm output) <;>
                simpa only [Equiv.apply_symm_apply, completion] using next
            · intro _ _ _ impossible
              exact impossible.elim)
    simpa only [id_eq, Equiv.symm_apply_apply] using guarded
  have actual := TotalWP.while_completion pending
    (fun currentModel state => stateRel currentModel (view state.locals) state.heap)
    invariant wellFounded
    (fun completion state => post completion (view state.locals) state.heap)
    stoppedGuard step initial (entry := ⟨view.symm (inputLocals input), heap⟩)
    (by simpa only [Equiv.apply_symm_apply] using represented)
  obtain ⟨finish, control, execution, property⟩ := actual
  have executed : observe view (.while guard body) program (inputLocals input) heap =
      Part.some ((control, view finish.locals), finish.heap) :=
    observe_eq_some_iff.mpr (by
      simpa only [Equiv.symm_apply_apply] using execution)
  apply Part.TotalCorrectness.stateT_triple_of_eq executed
  cases control <;> simpa only [Equiv.symm_apply_apply] using property

/-- Use visible guard and body contracts without exposing compiler completion
slots. The supplied frames concern the same actual observations: a guard
restores a continuing entry, and a body with no pending result restores the
next entry. Completed bodies need neither a next invariant nor a decrease.
The original full locals, actual normal control and final heap are retained. -/
theorem observe_while_visible_completion_contract {Model : Type u}
    {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    {Locals Visible : Type} (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (pending : Atom Γ (.option τ))
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Exec program guard state state (.returned false))
    (visible : Locals → Visible) (entry : Visible → Locals)
    (reconstruct : Locals → Option (Value τ) → Visible → Locals)
    (visibleEntry : ∀ start, visible (entry start) = start)
    (pendingEntry : ∀ start, pending.eval (view.symm (entry start)) = none)
    (reconstructNone : ∀ start output, reconstruct (entry start) none output = entry output)
    (guardFrame : ∀ start heap output finish again,
      observe view guard program (entry start) heap = Part.some ((.returned again, output), finish) →
      entry (visible output) = output)
    (bodyFrame : ∀ start heap output finish,
      observe view body program (entry start) heap = Part.some ((.normal, output), finish) →
      reconstruct (entry start) (pending.eval (view.symm output)) (visible output) = output)
    (stateRel : Model → Visible → Heap → Prop) (invariant : Model → Prop)
    {relation : Model → Model → Prop} (wellFounded : WellFounded relation)
    (ready : Model → Visible → Heap → Visible → Heap → Prop)
    (normal : Visible → Heap → Prop) (returned : Value τ → Visible → Heap → Prop)
    (guardSpec : ∀ model, invariant model →
      BlockSpec (fun start => observe view guard program (entry start)) (stateRel model)
        (fun _ _ _ _ => False)
        (fun start heap again output finish =>
          if again then ready model start heap (visible output) finish
          else normal (visible output) finish))
    (bodySpec : ∀ model start heap, invariant model → stateRel model start heap →
      BlockSpec (fun input => observe view body program (entry input)) (ready model start heap)
        (fun _ _ output finish => match pending.eval (view.symm output) with
          | none => ∃ next, invariant next ∧ stateRel next (visible output) finish ∧
              relation next model
          | some value => returned value (visible output) finish)
        (fun _ _ _ _ _ => False))
    (model : Model) (initial : invariant model) :
    BlockSpec (fun start => observe view (.while guard body) program (entry start))
      (stateRel model)
      (fun _ _ output finish => match pending.eval (view.symm output) with
        | none => normal (visible output) finish
        | some value => returned value (visible output) finish)
      (fun _ _ _ _ _ => False) := by
  let sourceRel := fun model locals heap =>
    entry (visible locals) = locals ∧ stateRel model (visible locals) heap
  let sourceReady := fun model start heap output finish =>
    entry (visible output) = output ∧ ready model (visible start) heap (visible output) finish
  let sourcePost := fun completion locals heap => match completion with
    | none => normal (visible locals) heap
    | some value => returned value (visible locals) heap
  have guarded : ∀ currentModel, invariant currentModel →
      BlockSpec (fun locals => observe view guard program locals) (sourceRel currentModel)
        (fun _ _ _ _ => False)
        (fun start heap again output finish =>
          if again then sourceReady currentModel start heap output finish
          else sourcePost (pending.eval (view.symm output)) output finish) := by
    intro currentModel valid locals heap represented
    apply (Part.TotalCorrectness.stateT_triple_iff _ _ _).mpr
    intro current sameHeap
    subst current
    obtain ⟨⟨control, output⟩, finish, evaluated, property⟩ :=
      (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
        ((guardSpec currentModel valid).«at» (visible locals) heap represented.2) heap rfl
    have rawEvaluated : observe view guard program locals heap =
        Part.some ((control, output), finish) := by
      simpa only [represented.1] using evaluated
    refine ⟨(control, output), finish, rawEvaluated, ?_⟩
    cases control with
    | normal => exact property
    | fault _ => exact property
    | returned again =>
        have fixed := guardFrame (visible locals) heap output finish again evaluated
        cases again with
        | true => exact ⟨fixed, property⟩
        | false =>
            have empty : pending.eval (view.symm output) = none := by
              rw [← fixed]
              exact pendingEntry (visible output)
            simpa only [Bool.false_eq_true, ↓reduceIte, sourcePost, empty] using property
  have iterated : ∀ currentModel start heap, invariant currentModel →
      sourceRel currentModel start heap →
      BlockSpec (fun locals => observe view body program locals) (sourceReady currentModel start heap)
        (fun _ _ output finish => match pending.eval (view.symm output) with
          | none => ∃ next, invariant next ∧ sourceRel next output finish ∧ relation next currentModel
          | some value => sourcePost (some value) output finish)
        (fun _ _ _ _ _ => False) := by
    intro currentModel start heap valid represented locals startHeap prepared
    apply (Part.TotalCorrectness.stateT_triple_iff _ _ _).mpr
    intro current sameHeap
    subst current
    obtain ⟨⟨control, output⟩, finish, evaluated, property⟩ :=
      (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
        ((bodySpec currentModel (visible start) heap valid represented.2).«at»
          (visible locals) startHeap prepared.2) startHeap rfl
    have rawEvaluated : observe view body program locals startHeap =
        Part.some ((control, output), finish) := by
      simpa only [prepared.1] using evaluated
    refine ⟨(control, output), finish, rawEvaluated, ?_⟩
    cases control with
    | returned _ => exact property
    | fault _ => exact property
    | normal =>
        have fixed := bodyFrame (visible locals) startHeap output finish evaluated
        cases completion : pending.eval (view.symm output) with
        | none =>
            have restored : entry (visible output) = output := by
              simpa only [completion, reconstructNone] using fixed
            simp only [completion] at property ⊢
            obtain ⟨next, validNext, relatedNext, smaller⟩ := property
            exact ⟨next, validNext, ⟨restored, relatedNext⟩, smaller⟩
        | some value =>
            simpa only [completion, sourcePost] using property
  have actual := observe_while_completion_contract view program guard body pending
    stoppedGuard sourceRel invariant wellFounded sourceReady sourcePost guarded iterated entry model initial
  refine actual.mono ?_ ?_ ?_
  · intro start heap represented
    exact ⟨by simp only [visibleEntry], by simpa only [visibleEntry] using represented⟩
  · intro _ _ output finish _ property
    cases completion : pending.eval (view.symm output) <;>
      simpa only [completion, sourcePost] using property
  · intro _ _ _ _ _ _ impossible
    exact impossible

end Stmt

end Complexity.Language
