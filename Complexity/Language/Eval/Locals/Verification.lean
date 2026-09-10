/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Specification

/-!
# Loop correctness with ordinary local values

The invariant and decrease relation below concern ordinary local coordinates
and the actual shared heap. They are transported through the lossless view to
the existing source well-founded loop rule. No loop interpreter, source product
type, machine representation or proposed instruction budget is introduced.

The guard specification starts before the guard and retains its actual locals
and heap. A false guard establishes the final postcondition there. A true guard
runs the body from that state; only normal completion must restore the invariant
and decrease relative to the state before the guard. Early body returns instead
establish their result postcondition, while faults and missing guard returns
cannot prove these strict specifications.

`observe_while_contract` separates the guard and body into ordinary relational
`BlockSpec` contracts. Its `ready` predicate retains the complete iteration's
starting state, so the body can establish well-founded progress without a
nested native triple or manual control-outcome transport in the author's proof.
-/

namespace Complexity.Language.Stmt

open scoped Part.TotalCorrectness

variable {signatures : List Signature} {Γ : List Ty} {result : Ty} {Locals : Type}

/-- Prove the actual source loop using an invariant and well-founded decrease
over ordinary locals and shared heaps. The guard and body are the same block
observations used in the loop equation, not supplied executable callbacks. -/
@[spec] theorem observe_while_spec (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (invariant : Locals → Heap → Prop)
    (relation : (Locals × Heap) → (Locals × Heap) → Prop) (wellFounded : WellFounded relation)
    (post : Std.Do.PostCond (Control result × Locals) (.arg Heap .pure))
    (step : ∀ startLocals startHeap, invariant startLocals startHeap →
      Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
        (observe view guard program startLocals) (fun current => ⟨current = startHeap⟩)
        (fun guardOutcome afterGuardHeap => ⟨match guardOutcome.1 with
          | .returned again =>
              if again then
                Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
                  (observe view body program guardOutcome.2)
                  (fun current => ⟨current = afterGuardHeap⟩)
                  (fun bodyOutcome afterBodyHeap => ⟨match bodyOutcome.1 with
                    | .normal => invariant bodyOutcome.2 afterBodyHeap ∧
                        relation (bodyOutcome.2, afterBodyHeap) (startLocals, startHeap)
                    | .returned value =>
                        (post.1 (.returned value, bodyOutcome.2) afterBodyHeap).down
                    | .fault _ => False⟩, ⟨⟩)
              else (post.1 (.normal, guardOutcome.2) afterGuardHeap).down
          | .normal => False
          | .fault _ => False⟩, ⟨⟩))
    (locals : Locals) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.while guard body) program locals)
      (fun heap => ⟨invariant locals heap⟩) post := by
  have sourceStep : ∀ start : State Γ, invariant (view start.locals) start.heap →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body
              (fun next => invariant (view next.locals) next.heap ∧
                relation (view next.locals, next.heap) (view start.locals, start.heap))
              (fun value finish => (post.1 (.returned value, view finish.locals) finish.heap).down)
              afterGuard
          else (post.1 (.normal, view afterGuard.locals) afterGuard.heap).down) start := by
    intro start initial
    have guardSpec := step (view start.locals) start.heap initial
    simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
      Part.TotalCorrectness.wp] at guardSpec
    obtain ⟨⟨⟨guardControl, afterGuardLocals⟩, afterGuardHeap⟩, member, guardPost⟩ :=
      guardSpec start.heap rfl
    have test : Exec program guard start ⟨view.symm afterGuardLocals, afterGuardHeap⟩
        guardControl := by
      simpa only [Equiv.symm_apply_apply] using mem_observe_iff.mp member
    refine ⟨⟨view.symm afterGuardLocals, afterGuardHeap⟩, guardControl, test, ?_⟩
    cases guardControl with
    | normal => exact guardPost
    | fault error => exact guardPost
    | returned again =>
        cases again with
        | false =>
            simpa only [Control.Satisfies, Equiv.apply_symm_apply] using guardPost
        | true =>
            obtain ⟨⟨⟨bodyControl, afterBodyLocals⟩, afterBodyHeap⟩, member, bodyPost⟩ :=
              guardPost afterGuardHeap rfl
            refine ⟨⟨view.symm afterBodyLocals, afterBodyHeap⟩, bodyControl,
              mem_observe_iff.mp member, ?_⟩
            cases bodyControl with
            | normal =>
                simpa only [Control.Satisfies, Equiv.apply_symm_apply] using bodyPost
            | returned value =>
                simpa only [Control.Satisfies, Equiv.apply_symm_apply] using bodyPost
            | fault error => exact bodyPost
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro heap initial
  have sourceInitial : invariant (view (view.symm locals)) heap := by
    simpa only [Equiv.apply_symm_apply] using initial
  obtain ⟨finish, control, execution, property⟩ :=
    TotalWP.while_wellFounded (entry := ⟨view.symm locals, heap⟩)
      (InvImage.wf (fun current : State Γ => (view current.locals, current.heap)) wellFounded)
      sourceStep sourceInitial
  refine ⟨((control, view finish.locals), finish.heap), ?_, ?_⟩
  · apply mem_observe_iff.mpr
    simpa only [Equiv.symm_apply_apply] using execution
  · cases control with
    | normal => exact property
    | returned value => exact property
    | fault error => exact False.elim property

/-- A natural-valued mathematical variant is a specialization of the same
well-founded rule. It measures a complete guard/body iteration, not runtime
instructions, fuel or a budget required for functional correctness. -/
theorem observe_while_variant_spec (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (invariant : Locals → Heap → Prop) (variant : Locals → Heap → Nat)
    (post : Std.Do.PostCond (Control result × Locals) (.arg Heap .pure))
    (step : ∀ startLocals startHeap, invariant startLocals startHeap →
      Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
        (observe view guard program startLocals) (fun current => ⟨current = startHeap⟩)
        (fun guardOutcome afterGuardHeap => ⟨match guardOutcome.1 with
          | .returned again =>
              if again then
                Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
                  (observe view body program guardOutcome.2)
                  (fun current => ⟨current = afterGuardHeap⟩)
                  (fun bodyOutcome afterBodyHeap => ⟨match bodyOutcome.1 with
                    | .normal => invariant bodyOutcome.2 afterBodyHeap ∧
                        variant bodyOutcome.2 afterBodyHeap < variant startLocals startHeap
                    | .returned value =>
                        (post.1 (.returned value, bodyOutcome.2) afterBodyHeap).down
                    | .fault _ => False⟩, ⟨⟩)
              else (post.1 (.normal, guardOutcome.2) afterGuardHeap).down
          | .normal => False
          | .fault _ => False⟩, ⟨⟩))
    (locals : Locals) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.while guard body) program locals)
      (fun heap => ⟨invariant locals heap⟩) post :=
  observe_while_spec view program guard body invariant
    (measure fun current : Locals × Heap => variant current.1 current.2).rel
    (measure fun current : Locals × Heap => variant current.1 current.2).wf post step locals

/-- Compose independent mathematical contracts for a loop guard and body.
The guard exposes its actual result and final state. A true result establishes
`ready`, which relates that state to the complete iteration's starting state;
a false result establishes the normal postcondition at the guard's actual exit.

The body contract starts at this real intermediate state. Only normal body
completion restores the invariant and decreases the well-founded relation;
early returns establish their own postcondition. The contracts and conclusion
refer to the existing observations, without outcome-tuple or nested-WP work in
the mathematical premises. -/
theorem observe_while_contract (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (invariant : Locals → Heap → Prop)
    (relation : (Locals × Heap) → (Locals × Heap) → Prop) (wellFounded : WellFounded relation)
    (ready : Locals → Heap → Locals → Heap → Prop)
    (normal : Locals → Heap → Prop) (returned : Value result → Locals → Heap → Prop)
    (guardSpec : BlockSpec (fun locals => observe view guard program locals) invariant
      (fun _ _ _ _ => False)
      (fun start startHeap again afterGuard afterGuardHeap =>
        if again then ready start startHeap afterGuard afterGuardHeap
        else normal afterGuard afterGuardHeap))
    (bodySpec : ∀ start startHeap, invariant start startHeap →
      BlockSpec (fun locals => observe view body program locals) (ready start startHeap)
        (fun _ _ finish heap => invariant finish heap ∧
          relation (finish, heap) (start, startHeap))
        (fun _ _ => returned)) :
    BlockSpec (fun locals => observe view (.while guard body) program locals) invariant
      (fun _ _ => normal) (fun _ _ => returned) := by
  intro locals heap initial
  have specification := observe_while_spec view program guard body invariant relation wellFounded
    (fun outcome heap => ⟨match outcome.1 with
      | .normal => normal outcome.2 heap
      | .returned value => returned value outcome.2 heap
      | .fault _ => False⟩, ⟨⟩)
    (by
      intro start startHeap input
      refine (guardSpec start startHeap input).mono (fun _ same => same) ?_
      constructor
      · rintro ⟨control, afterGuard⟩ afterGuardHeap property
        cases control with
        | normal => exact property
        | fault error => exact property
        | returned again =>
            cases again with
            | false => exact property
            | true => exact bodySpec start startHeap input afterGuard afterGuardHeap property
      · trivial)
    locals
  exact specification.mono (fun _ same => same.symm ▸ initial)
    ⟨fun _ _ property => property, trivial⟩

/-- Use a natural mathematical variant with the same separate guard and body
contracts. Its strict decrease is measured across a complete guard/body round,
so an effectful guard cannot silently change the comparison's starting state. -/
theorem observe_while_variant_contract (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (invariant : Locals → Heap → Prop) (variant : Locals → Heap → Nat)
    (ready : Locals → Heap → Locals → Heap → Prop)
    (normal : Locals → Heap → Prop) (returned : Value result → Locals → Heap → Prop)
    (guardSpec : BlockSpec (fun locals => observe view guard program locals) invariant
      (fun _ _ _ _ => False)
      (fun start startHeap again afterGuard afterGuardHeap =>
        if again then ready start startHeap afterGuard afterGuardHeap
        else normal afterGuard afterGuardHeap))
    (bodySpec : ∀ start startHeap, invariant start startHeap →
      BlockSpec (fun locals => observe view body program locals) (ready start startHeap)
        (fun _ _ finish heap => invariant finish heap ∧
          variant finish heap < variant start startHeap)
        (fun _ _ => returned)) :
    BlockSpec (fun locals => observe view (.while guard body) program locals) invariant
      (fun _ _ => normal) (fun _ _ => returned) :=
  observe_while_contract view program guard body invariant
    (measure fun current : Locals × Heap => variant current.1 current.2).rel
    (measure fun current : Locals × Heap => variant current.1 current.2).wf
    ready normal returned guardSpec bodySpec

end Complexity.Language.Stmt
