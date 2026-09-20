/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop.Completion
import Complexity.Language.Eval.Locals.LocalReturn.Models

/-!
# Arena readiness from mathematical local contracts

The same heap-indexed guard and body contracts used for source correctness
supply invariant preservation for an existing finite loop execution. Clients
add only fragment readiness at their actual mathematical input and heap. A
continuing body preserves the invariant; a completed body instead supplies its
result condition at the actual final heap.

This rule does not repeat the loop induction or a termination argument. It
uses the visible completion readiness rule and the existing mathematical
contract consequences. A representation need not determine the raw locals.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

universe u

/-- Reuse mathematical local contracts through an effectful guard. The body
starts at the guard's actual final heap and mathematical observation, related
to the original round by `prepared`. Only continuing rounds reestablish the
invariant. The existing finite execution supplies termination; readiness does
not need a second decrease proof. -/
theorem while_completion_model_effects_of_exec {Model : Type u}
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
    (representation : Model → Visible → Heap → Prop)
    (invariant : Model → Heap → Prop)
    (prepared : Model → Heap → Model → Heap → Prop)
    (normal : Model → Heap → Prop)
    (step : Model → Model → Prop) (completed : LocalResult → Model → Heap → Prop)
    (guardSpec : ∀ model heap, invariant model heap →
      Stmt.BlockSpec (fun start => Stmt.observe view guard program (entry start))
        (fun start current => representation model start current ∧ current = heap)
        (fun _ _ _ _ => False)
        (fun _ initial again output finish => ∃ next,
          representation next (visible output) finish ∧
            if again then prepared model initial next finish else normal next finish))
    (bodySpec : ∀ model heap, invariant model heap →
      ∀ tested after, prepared model heap tested after →
        Stmt.BlockSpec (fun start => Stmt.observe view body program (entry start))
          (fun start current => representation tested start current ∧ current = after)
          (fun _ _ output finish => match pending output with
            | none => ∃ next, representation next (visible output) finish ∧
                step model next ∧ invariant next finish
            | some value => ∃ next, representation next (visible output) finish ∧
                completed value next finish)
          (fun _ _ _ _ _ => False))
    (guardReady : ∀ model heap, invariant model heap →
      ∀ start, representation model start heap → ∀ finish decision
        (tested : Complexity.Language.Exec program guard
          ⟨view.symm (entry start), heap⟩ finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    (bodyReady : ∀ model heap, invariant model heap →
      ∀ tested after, prepared model heap tested after →
        ∀ start, representation tested start after → ∀ finish control
          (iterated : Complexity.Language.Exec program body
            ⟨view.symm (entry start), after⟩ finish control),
          ControlFits w control → ArenaReady iterated w heapLimit depth cursor cursor)
    (completedReady : ∀ model state value, pending (view state.locals) = some value →
      representation model (visible (view state.locals)) state.heap →
      completed value model state.heap → ∀ finish decision
        (tested : Complexity.Language.Exec program guard state finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    {model : Model} {start : Visible} {heap : Heap}
    {finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body)
      ⟨view.symm (entry start), heap⟩ finish control)
    (represented : representation model start heap) (initial : invariant model heap)
    (successful : ControlFits w control) :
    ArenaReady execution w heapLimit depth cursor cursor := by
  apply while_completion_of_exec view visible entry pending reconstruct reconstructNone
    guardFrame bodyFrame stoppedGuard
    (stateRel := fun model start heap => representation model start heap ∧ invariant model heap)
    (prepared := fun model _ heap output finish =>
      ∃ tested, representation tested output finish ∧ prepared model heap tested finish)
    (completed := fun value output finish =>
      ∃ model, representation model output finish ∧ completed value model finish)
    (model := model) (execution := execution)
  · intro model
    have checked := Stmt.BlockSpec.guard_model_effects visible representation
      invariant normal prepared guardSpec model
    refine checked.mono (fun _ _ valid => valid)
      (fun _ _ _ _ _ impossible => impossible) ?_
    intro _ _ again output finish _ property active
    simpa only [active, ↓reduceIte] using property
  · rintro model _ heap ⟨_, valid⟩
    have checked := Stmt.BlockSpec.body_model_effects visible pending representation
      invariant prepared step (fun next current => step current next) completed bodySpec
      (fun _ _ _ _ _ _ _ advanced => advanced) model heap valid
    refine checked.mono (fun _ _ valid => valid) ?_
      (fun _ _ _ _ _ _ impossible => impossible)
    intro _ _ output finish _ property
    cases stopped : pending output with
    | none =>
        simp only [stopped] at property ⊢
        obtain ⟨next, _, related, _⟩ := property
        exact ⟨next, related⟩
    | some value => simpa only [stopped] using property
  · rintro model start heap ⟨related, valid⟩
    exact guardReady model heap valid start related
  · rintro model _ heap ⟨_, valid⟩ input after ⟨tested, related, ready⟩
    exact bodyReady model heap valid tested after ready input related
  · rintro state value stopped ⟨model, related, done⟩
    exact completedReady model state value stopped related done
  · exact ⟨represented, initial⟩
  · exact successful

/-- Reuse mathematical local contracts for the same finite completion-aware
loop. The guard contract preserves the model and heap; the body may change
both. Readiness concerns each fragment's actual input, retaining its ranges,
call nesting and scratch capacity independently of source termination. -/
theorem while_completion_model_of_exec {Model : Type u}
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
    (representation : Model → Visible → Heap → Prop)
    (invariant : Model → Heap → Prop) (test : Model → Bool)
    (step : Model → Model → Prop) (completed : LocalResult → Model → Heap → Prop)
    (guardSpec : ∀ model heap, invariant model heap →
      Stmt.BlockSpec (fun start => Stmt.observe view guard program (entry start))
        (fun start current => representation model start current ∧ current = heap)
        (fun _ _ _ _ => False)
        (fun _ initial again output finish => ∃ next,
          representation next (visible output) finish ∧ again = test model ∧
            next = model ∧ finish = initial))
    (bodySpec : ∀ model heap, invariant model heap → test model = true →
      Stmt.BlockSpec (fun start => Stmt.observe view body program (entry start))
        (fun start current => representation model start current ∧ current = heap)
        (fun _ _ output finish => match pending output with
          | none => ∃ next, representation next (visible output) finish ∧
              step model next ∧ invariant next finish
          | some value => ∃ next, representation next (visible output) finish ∧
              completed value next finish)
        (fun _ _ _ _ _ => False))
    (guardReady : ∀ model heap, invariant model heap →
      ∀ start, representation model start heap → ∀ finish decision
        (tested : Complexity.Language.Exec program guard
          ⟨view.symm (entry start), heap⟩ finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    (bodyReady : ∀ model heap, invariant model heap → test model = true →
      ∀ start, representation model start heap → ∀ finish control
        (iterated : Complexity.Language.Exec program body
          ⟨view.symm (entry start), heap⟩ finish control),
        ControlFits w control → ArenaReady iterated w heapLimit depth cursor cursor)
    (completedReady : ∀ model state value, pending (view state.locals) = some value →
      representation model (visible (view state.locals)) state.heap →
      completed value model state.heap → ∀ finish decision
        (tested : Complexity.Language.Exec program guard state finish (.returned decision)),
        ArenaReady tested w heapLimit depth cursor cursor)
    {model : Model} {start : Visible} {heap : Heap}
    {finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body)
      ⟨view.symm (entry start), heap⟩ finish control)
    (represented : representation model start heap) (initial : invariant model heap)
    (successful : ControlFits w control) :
    ArenaReady execution w heapLimit depth cursor cursor := by
  apply while_completion_model_effects_of_exec view visible entry pending reconstruct reconstructNone
    guardFrame bodyFrame stoppedGuard
    (representation := representation) (invariant := invariant)
    (prepared := fun model heap tested after =>
      tested = model ∧ after = heap ∧ invariant tested after ∧ test model = true)
    (normal := fun _ _ => True) (step := step) (completed := completed)
    (guardReady := guardReady) (completedReady := completedReady)
    (execution := execution) (represented := represented) (initial := initial)
    (successful := successful)
  · intro model heap valid
    refine (guardSpec model heap valid).mono (fun _ _ initial => initial)
      (fun _ _ _ _ _ impossible => impossible) ?_
    rintro _ initial again output finish ⟨_, sameInitial⟩
      ⟨next, related, decision, sameModel, sameHeap⟩
    refine ⟨next, related, ?_⟩
    cases again with
    | false => trivial
    | true =>
        refine ⟨sameModel, sameHeap, ?_, decision.symm⟩
        simpa only [sameModel, sameHeap, sameInitial] using valid
  · intro model heap valid tested after ready
    obtain ⟨sameModel, sameHeap, _, active⟩ := ready
    subst tested after
    exact bodySpec model heap valid active
  · intro model heap valid tested after ready
    obtain ⟨sameModel, sameHeap, _, active⟩ := ready
    subst tested after
    exact bodyReady model heap valid active

end Ram.LanguageCompiler.ArenaReady
