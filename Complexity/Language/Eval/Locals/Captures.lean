/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Verification

/-!
# Fixed captures in ordinary-local loop specifications

A lossless local view can group mutable values with captured values. When the
actual guard and body executions preserve the captures, the author supplies an
invariant and a well-founded decrease relation only for mutable values and the
current heap. The frame
premises establish the fixed capture equations internally; they do not require
the heap or borrowed buffer contents to remain unchanged.

`Stmt.observe_reindex` relates this grouped view to an existing lexical-order
view by mapping the same actual outcome. The fixed-capture rule then reuses the
ordinary-local well-founded rule with a strengthened internal invariant and
Lean's `InvImage.wf`. The natural-valued variant interface is its `measure`
specialization. There is no new observer, execution relation, loop induction or
proposed runtime budget.

The corresponding `observe_while_fixed_contract` rule composes independent
guard and body contracts while keeping these same checked capture frames.
Their predicates need only the mutable values and actual endpoint heaps.
-/

namespace Complexity.Language.Stmt

open scoped Part.TotalCorrectness

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}

/-- A lossless change of local coordinates maps the same actual block outcome.
The actual final heap and control are unchanged, including on returns and faults. -/
theorem observe_reindex {Locals Reindexed : Type} (view : Env Γ ≃ Locals)
    (reindex : Locals ≃ Reindexed) (stmt : Stmt signatures Γ result)
    (program : Program signatures) (locals : Reindexed) :
    observe (view.trans reindex) stmt program locals =
      (fun outcome => (outcome.1, reindex outcome.2)) <$>
        observe view stmt program (reindex.symm locals) := by
  funext heap
  simp only [observe, Equiv.symm_trans_apply, Equiv.trans_apply,
    Functor.map, StateT.map, Bind.bind, Pure.pure,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]

/-- Apply a grouped block contract to its original ordinary-local action.
The actual execution frame fixes the captured values, so continuation premises
quantify only the final mutable values and heap. This reconstruction retains
the same complete source state; it does not assume that the heap is unchanged. -/
theorem observe_fixed_spec {Locals Mutable Captured : Type}
    (view : Env Γ ≃ Locals) (regroup : Locals ≃ Mutable × Captured)
    (program : Program signatures) (stmt : Stmt signatures Γ result)
    (frame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program stmt entry finish control →
        ((view.trans regroup) finish.locals).2 = ((view.trans regroup) entry.locals).2)
    (captures : Captured)
    {pre : Mutable → Heap → Prop}
    {normal : Mutable → Heap → Mutable → Heap → Prop}
    {returned : Mutable → Heap → Value result → Mutable → Heap → Prop}
    (specification : BlockSpec
      (fun mutable => observe (view.trans regroup) stmt program (mutable, captures)) pre
      (fun start heap output finish => normal start heap output.1 finish)
      (fun start heap value output finish => returned start heap value output.1 finish))
    (mutable : Mutable) (post : Std.Do.PostCond (Control result × Locals) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view stmt program (regroup.symm (mutable, captures)))
      (fun heap => ⟨pre mutable heap ∧
        (∀ output finish, normal mutable heap output finish →
          (post.1 (.normal, regroup.symm (output, captures)) finish).down) ∧
        (∀ value output finish, returned mutable heap value output finish →
          (post.1 (.returned value, regroup.symm (output, captures)) finish).down)⟩)
      post := by
  apply (Part.TotalCorrectness.stateT_triple_iff _ _ _).mpr
  rintro heap ⟨initial, normalPost, returnedPost⟩
  obtain ⟨⟨control, ⟨output, outputCaptures⟩⟩, finish, observed, property⟩ :=
    (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
      (specification.«at» mutable heap initial) heap rfl
  have execution := observe_eq_some_iff.mp observed
  have sameCaptures : outputCaptures = captures := by
    simpa only [Equiv.apply_symm_apply] using frame execution
  subst outputCaptures
  refine ⟨(control, regroup.symm (output, captures)), finish, ?_, ?_⟩
  · apply observe_eq_some_iff.mpr
    simpa only [Equiv.symm_trans_apply] using execution
  · cases control with
    | normal => exact normalPost output finish property
    | returned value => exact returnedPost value output finish property
    | fault error => exact False.elim property

/-- Fixed captures need not appear in the author's invariant or decrease relation.
The frame premises concern the actual guard/body executions; the specifications
still run those same blocks and retain their actual mutable values and heap.
Only a normal body completion must restore the invariant and decrease relative
to the state before the guard. Lean's existing well-founded relations can be
used directly, without reducing progress to a natural-valued variant. -/
theorem observe_while_fixed_spec {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (invariant : Mutable → Heap → Prop)
    (relation : (Mutable × Heap) → (Mutable × Heap) → Prop)
    (wellFounded : WellFounded relation)
    (post : Std.Do.PostCond (Control result × Mutable) (.arg Heap .pure))
    (step : ∀ startMutable startHeap, invariant startMutable startHeap →
      Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
        (observe view guard program (startMutable, captures))
        (fun current => ⟨current = startHeap⟩)
        (fun guardOutcome afterGuardHeap => ⟨match guardOutcome.1 with
          | .returned again =>
              if again then
                Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
                  (observe view body program (guardOutcome.2.1, captures))
                  (fun current => ⟨current = afterGuardHeap⟩)
                  (fun bodyOutcome afterBodyHeap => ⟨match bodyOutcome.1 with
                    | .normal => invariant bodyOutcome.2.1 afterBodyHeap ∧
                        relation (bodyOutcome.2.1, afterBodyHeap) (startMutable, startHeap)
                    | .returned value =>
                        (post.1 (.returned value, bodyOutcome.2.1) afterBodyHeap).down
                    | .fault _ => False⟩, ⟨⟩)
              else (post.1 (.normal, guardOutcome.2.1) afterGuardHeap).down
          | .normal => False
          | .fault _ => False⟩, ⟨⟩))
    (mutable : Mutable) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.while guard body) program (mutable, captures))
      (fun heap => ⟨invariant mutable heap⟩)
      (fun outcome heap => post.1 (outcome.1, outcome.2.1) heap, ⟨⟩) := by
  have specification := observe_while_spec view program guard body
    (fun locals heap => locals.2 = captures ∧ invariant locals.1 heap)
    (InvImage relation (fun current : (Mutable × Captured) × Heap =>
      (current.1.1, current.2)))
    (InvImage.wf (fun current : (Mutable × Captured) × Heap =>
      (current.1.1, current.2)) wellFounded)
    (fun outcome heap => post.1 (outcome.1, outcome.2.1) heap, ⟨⟩)
    (by
      rintro ⟨startMutable, startCaptured⟩ startHeap ⟨sameCapture, initial⟩
      change startCaptured = captures at sameCapture
      subst startCaptured
      have guardSpec := step startMutable startHeap initial
      simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
        Part.TotalCorrectness.wp] at guardSpec ⊢
      intro currentHeap sameHeap
      subst currentHeap
      obtain ⟨⟨⟨guardControl, ⟨afterGuard, afterGuardCaptured⟩⟩, afterGuardHeap⟩,
        guardMember, guardPost⟩ := guardSpec startHeap rfl
      have captureEq : afterGuardCaptured = captures := by
        simpa only [Equiv.apply_symm_apply] using guardFrame (mem_observe_iff.mp guardMember)
      subst afterGuardCaptured
      refine ⟨((guardControl, (afterGuard, captures)), afterGuardHeap), guardMember, ?_⟩
      cases guardControl with
      | normal => exact guardPost
      | fault error => exact guardPost
      | returned again =>
          cases again with
          | false => exact guardPost
          | true =>
              intro currentHeap sameHeap
              subst currentHeap
              obtain ⟨⟨⟨bodyControl, ⟨afterBody, afterBodyCaptured⟩⟩, afterBodyHeap⟩,
                bodyMember, bodyPost⟩ := guardPost afterGuardHeap rfl
              have captureEq : afterBodyCaptured = captures := by
                simpa only [Equiv.apply_symm_apply] using bodyFrame (mem_observe_iff.mp bodyMember)
              subst afterBodyCaptured
              refine ⟨((bodyControl, (afterBody, captures)), afterBodyHeap), bodyMember, ?_⟩
              cases bodyControl with
              | normal => exact ⟨⟨rfl, bodyPost.1⟩, bodyPost.2⟩
              | returned value => exact bodyPost
              | fault error => exact bodyPost)
    (mutable, captures)
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp] at specification ⊢
  intro heap initial
  exact specification heap ⟨True.intro, initial⟩

/-- Fixed captures need not appear in the author's invariant or variant.
The frame premises concern the actual guard/body executions; the specifications
still run those same blocks and retain their actual mutable values and heap.
Only a normal body completion must restore the invariant and decrease. -/
theorem observe_while_fixed_variant_spec {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (invariant : Mutable → Heap → Prop) (variant : Mutable → Heap → Nat)
    (post : Std.Do.PostCond (Control result × Mutable) (.arg Heap .pure))
    (step : ∀ startMutable startHeap, invariant startMutable startHeap →
      Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
        (observe view guard program (startMutable, captures))
        (fun current => ⟨current = startHeap⟩)
        (fun guardOutcome afterGuardHeap => ⟨match guardOutcome.1 with
          | .returned again =>
              if again then
                Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
                  (observe view body program (guardOutcome.2.1, captures))
                  (fun current => ⟨current = afterGuardHeap⟩)
                  (fun bodyOutcome afterBodyHeap => ⟨match bodyOutcome.1 with
                    | .normal => invariant bodyOutcome.2.1 afterBodyHeap ∧
                        variant bodyOutcome.2.1 afterBodyHeap < variant startMutable startHeap
                    | .returned value =>
                        (post.1 (.returned value, bodyOutcome.2.1) afterBodyHeap).down
                    | .fault _ => False⟩, ⟨⟩)
              else (post.1 (.normal, guardOutcome.2.1) afterGuardHeap).down
          | .normal => False
          | .fault _ => False⟩, ⟨⟩))
    (mutable : Mutable) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.while guard body) program (mutable, captures))
      (fun heap => ⟨invariant mutable heap⟩)
      (fun outcome heap => post.1 (outcome.1, outcome.2.1) heap, ⟨⟩) :=
  observe_while_fixed_spec view program guard body guardFrame bodyFrame captures invariant
    (measure fun current : Mutable × Heap => variant current.1 current.2).rel
    (measure fun current : Mutable × Heap => variant current.1 current.2).wf post step mutable

/-- Separate guard and body contracts with fixed captured values. Their
mathematical predicates mention only mutable coordinates and actual heaps;
the proved execution frames retain the captures internally. The guard may
change both mutable values and heap, and body returns need no decrease. -/
theorem observe_while_fixed_contract {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (invariant : Mutable → Heap → Prop)
    (relation : (Mutable × Heap) → (Mutable × Heap) → Prop)
    (wellFounded : WellFounded relation)
    (ready : Mutable → Heap → Mutable → Heap → Prop)
    (normal : Mutable → Heap → Prop) (returned : Value result → Mutable → Heap → Prop)
    (guardSpec : BlockSpec (fun mutable => observe view guard program (mutable, captures))
      invariant (fun _ _ _ _ => False)
      (fun start startHeap again afterGuard afterGuardHeap =>
        if again then ready start startHeap afterGuard.1 afterGuardHeap
        else normal afterGuard.1 afterGuardHeap))
    (bodySpec : ∀ start startHeap, invariant start startHeap →
      BlockSpec (fun mutable => observe view body program (mutable, captures)) (ready start startHeap)
        (fun _ _ finish heap => invariant finish.1 heap ∧
          relation (finish.1, heap) (start, startHeap))
        (fun _ _ value finish heap => returned value finish.1 heap)) :
    BlockSpec (fun mutable => observe view (.while guard body) program (mutable, captures))
      invariant (fun _ _ finish heap => normal finish.1 heap)
      (fun _ _ value finish heap => returned value finish.1 heap) := by
  intro mutable heap initial
  have specification := observe_while_fixed_spec view program guard body guardFrame bodyFrame
    captures invariant relation wellFounded
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
            | true => exact bodySpec start startHeap input afterGuard.1 afterGuardHeap property
      · trivial)
    mutable
  exact specification.mono (fun _ same => same.symm ▸ initial)
    ⟨fun _ _ property => property, trivial⟩

/-- A natural-valued variant specializes the same independent contracts and
fixed-capture rule. Progress compares the actual final body state to the state
before its guard, while false guards finish at their actual updated state. -/
theorem observe_while_fixed_variant_contract {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (invariant : Mutable → Heap → Prop) (variant : Mutable → Heap → Nat)
    (ready : Mutable → Heap → Mutable → Heap → Prop)
    (normal : Mutable → Heap → Prop) (returned : Value result → Mutable → Heap → Prop)
    (guardSpec : BlockSpec (fun mutable => observe view guard program (mutable, captures))
      invariant (fun _ _ _ _ => False)
      (fun start startHeap again afterGuard afterGuardHeap =>
        if again then ready start startHeap afterGuard.1 afterGuardHeap
        else normal afterGuard.1 afterGuardHeap))
    (bodySpec : ∀ start startHeap, invariant start startHeap →
      BlockSpec (fun mutable => observe view body program (mutable, captures)) (ready start startHeap)
        (fun _ _ finish heap => invariant finish.1 heap ∧
          variant finish.1 heap < variant start startHeap)
        (fun _ _ value finish heap => returned value finish.1 heap)) :
    BlockSpec (fun mutable => observe view (.while guard body) program (mutable, captures))
      invariant (fun _ _ finish heap => normal finish.1 heap)
      (fun _ _ value finish heap => returned value finish.1 heap) :=
  observe_while_fixed_contract view program guard body guardFrame bodyFrame captures invariant
    (measure fun current : Mutable × Heap => variant current.1 current.2).rel
    (measure fun current : Mutable × Heap => variant current.1 current.2).wf
    ready normal returned guardSpec bodySpec

end Complexity.Language.Stmt
