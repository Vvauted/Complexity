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

end Complexity.Language.Stmt
