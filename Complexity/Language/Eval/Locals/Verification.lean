/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals

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

end Complexity.Language.Stmt
