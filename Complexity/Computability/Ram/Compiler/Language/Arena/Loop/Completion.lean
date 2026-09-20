/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop
import Complexity.Language.Eval.Locals.LocalReturn.While

/-!
# Arena readiness through visible local-completion contracts

An existing finite loop execution supplies termination. Its source contracts
describe the visible guard and body states, including a locally returned value.
The generated frames restore the full continuing state; a completed state takes
the actual stopped guard. Clients supply only the readiness of those real
fragments, retaining their word ranges, heap effects and scratch capacity.

This rule reuses the fixed-boundary arena loop theorem. It adds neither an
execution relation nor another termination or instruction-budget proof.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

universe u

/-- Lift visible local-completion contracts to readiness of the same finite
loop. Only continuing rounds reestablish the invariant. Completed rounds need
readiness of the real stopped guard, not readiness of an unreachable body.
The source frames retain every private slot in the actual execution. -/
theorem while_completion_of_exec {Model : Type u}
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {Locals Visible LocalResult : Type}
    {w heapLimit depth cursor : Nat}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    (view : Env Γ ≃ Locals) (visible : Locals → Visible) (entry : Visible → Locals)
    (pending : Locals → Option LocalResult)
    (reconstruct : Locals → Option LocalResult → Visible → Locals)
    (reconstructNone : ∀ start output, reconstruct (entry start) none output = entry output)
    (guardFrame : ∀ start {heap finish control},
      Complexity.Language.Exec program guard ⟨view.symm (entry start), heap⟩ finish control →
      entry (visible (view finish.locals)) = view finish.locals)
    (bodyFrame : ∀ {start finish control},
      Complexity.Language.Exec program body start finish control →
      reconstruct (view start.locals) (pending (view finish.locals))
        (visible (view finish.locals)) = view finish.locals)
    (stoppedGuard : ∀ state value, pending (view state.locals) = some value →
      Complexity.Language.Exec program guard state state (.returned false))
    (stateRel : Model → Visible → Heap → Prop)
    (prepared : Model → Visible → Heap → Visible → Heap → Prop)
    (completed : LocalResult → Visible → Heap → Prop)
    (guardSpec : ∀ model,
      Stmt.BlockSpec (fun start => Stmt.observe view guard program (entry start))
        (stateRel model) (fun _ _ _ _ => False)
        (fun start heap again output finish =>
          again = true → prepared model start heap (visible output) finish))
    (bodySpec : ∀ model start heap, stateRel model start heap →
      Stmt.BlockSpec (fun input => Stmt.observe view body program (entry input))
        (prepared model start heap)
        (fun _ _ output finish => match pending output with
          | none => ∃ next, stateRel next (visible output) finish
          | some value => completed value (visible output) finish)
        (fun _ _ _ _ _ => False))
    (guardReady : ∀ model start heap, stateRel model start heap →
      ∀ finish decision
        (tested : Complexity.Language.Exec program guard
          ⟨view.symm (entry start), heap⟩ finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    (bodyReady : ∀ model start heap, stateRel model start heap →
      ∀ input inputHeap, prepared model start heap input inputHeap →
      ∀ finish control
        (iterated : Complexity.Language.Exec program body
          ⟨view.symm (entry input), inputHeap⟩ finish control),
        ControlFits w control → ArenaReady iterated w heapLimit depth cursor cursor)
    (completedReady : ∀ state value, pending (view state.locals) = some value →
      completed value (visible (view state.locals)) state.heap →
      ∀ finish decision
        (tested : Complexity.Language.Exec program guard state finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    {model : Model} {start : Visible} {heap : Heap}
    {finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body)
      ⟨view.symm (entry start), heap⟩ finish control)
    (initial : stateRel model start heap) (successful : ControlFits w control) :
    ArenaReady execution w heapLimit depth cursor cursor := by
  let invariant := fun state : Complexity.Language.State Γ =>
    (∃ model start, state.locals = view.symm (entry start) ∧ stateRel model start state.heap) ∨
    (∃ value, pending (view state.locals) = some value ∧
      completed value (visible (view state.locals)) state.heap)
  have guardPrepared (model : Model) (start : Visible) (heap : Heap)
      (valid : stateRel model start heap) {after : Complexity.Language.State Γ}
      (tested : Complexity.Language.Exec program guard
        ⟨view.symm (entry start), heap⟩ after (.returned true)) :
      after = ⟨view.symm (entry (visible (view after.locals))), after.heap⟩ ∧
        prepared model start heap (visible (view after.locals)) after.heap := by
    refine ⟨?_, (Stmt.BlockSpec.post_of_exec view entry (guardSpec model) valid tested) rfl⟩
    apply Complexity.Language.State.ext
    · simpa only [Equiv.symm_apply_apply] using
        congrArg view.symm (guardFrame start tested).symm
    · rfl
  apply while_of_exec (invariant := invariant) execution
  · rintro ⟨locals, startHeap⟩ after decision running tested
    rcases running with ⟨model, start, rfl, valid⟩ | ⟨value, stopped, done⟩
    · exact guardReady model start startHeap valid after decision tested
    · exact completedReady _ value stopped done after decision tested
  · rintro ⟨locals, startHeap⟩ afterGuard afterBody outcome running tested iterated fits
    rcases running with ⟨model, start, rfl, valid⟩ | ⟨value, stopped, done⟩
    · obtain ⟨same, ready⟩ := guardPrepared model start startHeap valid tested
      have actual : Complexity.Language.Exec program body
          ⟨view.symm (entry (visible (view afterGuard.locals))), afterGuard.heap⟩
          afterBody outcome := by
        simpa only [← same] using iterated
      simpa only [← same] using
        bodyReady model start startHeap valid _ _ ready afterBody outcome actual fits
    · cases (tested.deterministic (stoppedGuard _ value stopped)).2
  · rintro ⟨locals, startHeap⟩ afterGuard afterBody running tested iterated
    rcases running with ⟨model, start, rfl, valid⟩ | ⟨value, stopped, done⟩
    · obtain ⟨same, ready⟩ := guardPrepared model start startHeap valid tested
      have actual : Complexity.Language.Exec program body
          ⟨view.symm (entry (visible (view afterGuard.locals))), afterGuard.heap⟩
          afterBody .normal := by
        simpa only [← same] using iterated
      have updated := Stmt.BlockSpec.post_of_exec view entry
        (bodySpec model start startHeap valid) ready actual
      cases completion : pending (view afterBody.locals) with
      | none =>
          simp only [completion] at updated
          obtain ⟨next, related⟩ := updated
          have restored : entry (visible (view afterBody.locals)) = view afterBody.locals := by
            simpa only [Equiv.apply_symm_apply, completion, reconstructNone] using bodyFrame actual
          left
          refine ⟨next, visible (view afterBody.locals), ?_, related⟩
          simpa only [Equiv.symm_apply_apply] using congrArg view.symm restored.symm
      | some value =>
          simp only [completion] at updated
          exact Or.inr ⟨value, completion, updated⟩
    · cases (tested.deterministic (stoppedGuard _ value stopped)).2
  · exact Or.inl ⟨model, start, rfl, initial⟩
  · exact successful

end Ram.LanguageCompiler.ArenaReady
