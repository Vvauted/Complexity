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
`observe_while_fixed_rel_contract` instead keeps its invariant and progress on
a heap-indexed mathematical model, without requiring a lossless model encoding.
`observe_while_fixed_count_frame_contract` specializes the same variant rule
to a count advancing by one and a supplied transitive heap frame. It composes
existing step contracts without inferring their contents effects.
-/

namespace Complexity.Language.Stmt

open scoped Part.TotalCorrectness

universe u

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

private theorem blockSpec_with_captures {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (stmt : Stmt signatures Γ result)
    (frame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program stmt entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured)
    {pre : Mutable → Heap → Prop}
    {normal : Mutable → Heap → Mutable → Heap → Prop}
    {returned : Mutable → Heap → Value result → Mutable → Heap → Prop}
    (specification : BlockSpec (fun mutable => observe view stmt program (mutable, captures))
      pre (fun start heap output finish => normal start heap output.1 finish)
      (fun start heap value output finish => returned start heap value output.1 finish)) :
    BlockSpec (fun locals => observe view stmt program locals)
      (fun locals heap => locals.2 = captures ∧ pre locals.1 heap)
      (fun start heap output finish => output.2 = captures ∧ normal start.1 heap output.1 finish)
      (fun start heap value output finish =>
        output.2 = captures ∧ returned start.1 heap value output.1 finish) := by
  rintro ⟨mutable, actual⟩ heap ⟨sameCaptures, initial⟩
  change actual = captures at sameCaptures
  subst actual
  have fixed := observe_fixed_spec view (Equiv.refl _) program stmt frame captures
    specification mutable
    (fun outcome finish => ⟨match outcome.1 with
      | .normal => outcome.2.2 = captures ∧ normal mutable heap outcome.2.1 finish
      | .returned value =>
          outcome.2.2 = captures ∧ returned mutable heap value outcome.2.1 finish
      | .fault _ => False⟩, ⟨⟩)
  apply fixed.mono
  · rintro current rfl
    exact ⟨initial, fun _ _ property => ⟨rfl, property⟩,
      fun _ _ _ property => ⟨rfl, property⟩⟩
  · exact ⟨fun _ _ property => property, trivial⟩

/-- Independent contracts for a fixed-capture loop with a relational
mathematical state. Captures are preserved by the actual guard and body frames;
the invariant and well-founded relation mention only the mathematical model.
Guards may update mutable values and the heap. Normal body exits provide a
related next model and decrease, whereas false guards and early returns prove
their postconditions at the actual endpoint without a decrease obligation. -/
theorem observe_while_fixed_rel_contract {Model : Type u} {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (stateRel : Model → Mutable → Heap → Prop)
    (invariant : Model → Prop) {relation : Model → Model → Prop}
    (wellFounded : WellFounded relation)
    (ready : Model → Mutable → Heap → Mutable → Heap → Prop)
    (normal : Mutable → Heap → Prop) (returned : Value result → Mutable → Heap → Prop)
    (guardSpec : ∀ model, invariant model →
      BlockSpec (fun mutable => observe view guard program (mutable, captures))
        (stateRel model) (fun _ _ _ _ => False)
        (fun start heap again afterGuard finish =>
          if again then ready model start heap afterGuard.1 finish
          else normal afterGuard.1 finish))
    (bodySpec : ∀ model start heap, invariant model → stateRel model start heap →
      BlockSpec (fun mutable => observe view body program (mutable, captures))
        (ready model start heap)
        (fun _ _ afterBody finish => ∃ next, invariant next ∧
          stateRel next afterBody.1 finish ∧ relation next model)
        (fun _ _ value afterBody finish => returned value afterBody.1 finish))
    (model : Model) (initial : invariant model) :
    BlockSpec (fun mutable => observe view (.while guard body) program (mutable, captures))
      (stateRel model) (fun _ _ finish heap => normal finish.1 heap)
      (fun _ _ value finish heap => returned value finish.1 heap) := by
  intro mutable heap represented
  apply observe_while_rel_contract view program guard body
    (fun current locals heap => locals.2 = captures ∧ stateRel current locals.1 heap)
    invariant wellFounded
    (fun current start heap afterGuard finish =>
      afterGuard.2 = captures ∧ ready current start.1 heap afterGuard.1 finish)
    (fun locals heap => normal locals.1 heap)
    (fun value locals heap => returned value locals.1 heap)
    ?_ ?_ model initial (mutable, captures) heap ⟨rfl, represented⟩
  · intro current valid
    apply (blockSpec_with_captures view program guard guardFrame captures
      (pre := stateRel current) (normal := fun _ _ _ _ => False)
      (returned := fun start heap again afterGuard finish =>
        if again then ready current start heap afterGuard finish else normal afterGuard finish)
      (guardSpec current valid)).mono (fun _ _ property => property)
    · intro _ _ _ _ _ property
      exact property.2
    · intro _ _ again _ _ _ property
      cases again with
      | false => exact property.2
      | true => exact property
  · rintro current ⟨start, actual⟩ startHeap valid ⟨sameCaptures, related⟩
    change actual = captures at sameCaptures
    subst actual
    apply (blockSpec_with_captures view program body bodyFrame captures
      (pre := ready current start startHeap)
      (normal := fun _ _ afterBody finish => ∃ next, invariant next ∧
        stateRel next afterBody finish ∧ relation next current)
      (returned := fun _ _ value afterBody finish => returned value afterBody finish)
      (bodySpec current start startHeap valid related)).mono (fun _ _ property => property)
    · rintro _ _ _ _ _ ⟨sameCaptures, next, nextValid, nextRelated, smaller⟩
      exact ⟨next, nextValid, ⟨sameCaptures, nextRelated⟩, smaller⟩
    · intro _ _ _ _ _ _ property
      exact property.2

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
  apply observe_while_fixed_rel_contract view program guard body guardFrame bodyFrame captures
    (fun model mutable heap => mutable = model.1 ∧ heap = model.2)
    (fun model => invariant model.1 model.2) wellFounded
    (fun _ => ready) normal returned ?_ ?_ (mutable, heap) initial mutable heap ⟨rfl, rfl⟩
  · rintro ⟨start, startHeap⟩ valid
    apply guardSpec.mono
    · rintro _ _ ⟨rfl, rfl⟩
      exact valid
    · intro _ _ _ _ _ property
      exact property
    · intro _ _ _ _ _ _ property
      exact property
  · rintro ⟨start, startHeap⟩ current currentHeap valid ⟨same, sameHeap⟩
    subst current
    subst currentHeap
    apply (bodySpec start startHeap valid).mono (fun _ _ property => property)
    · intro _ _ finish finishHeap _ property
      exact ⟨(finish.1, finishHeap), property.1, ⟨rfl, rfl⟩, property.2⟩
    · intro _ _ _ _ _ _ property
      exact property

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

/-- Compose a bounded counting loop with a transitive heap frame. The supplied
guard contract preserves the observed count and heap, and establishes the
invariant on its actual updated locals. Each normal body step advances that
count by one and supplies its actual heap frame. The invariant and exit fact
remain mathematical obligations, while capture transport and accumulated
frames are handled by the existing variant rule. No successful early return is
admitted by these contracts. -/
theorem observe_while_fixed_count_frame_contract {Mutable Captured : Type}
    (view : Env Γ ≃ Mutable × Captured) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (guardFrame : ∀ {entry finish : State Γ} {control : Control .bool},
      Exec program guard entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (bodyFrame : ∀ {entry finish : State Γ} {control : Control result},
      Exec program body entry finish control →
        (view finish.locals).2 = (view entry.locals).2)
    (captures : Captured) (count : Mutable → Nat) (limit : Nat)
    (invariant : Mutable → Heap → Prop)
    (frame : Heap → Heap → Prop)
    (frameTrans : ∀ {initial middle finish},
      frame initial middle → frame middle finish → frame initial finish)
    (normal : Heap → Prop)
    (guardSpec : BlockSpec (fun index => observe view guard program (index, captures))
      invariant (fun _ _ _ _ => False)
      (fun start heap again next finish => count next.1 = count start ∧ finish = heap ∧
        invariant next.1 finish ∧ (again = true ↔ count next.1 < limit)))
    (bodySpec : BlockSpec (fun index => observe view body program (index, captures))
      (fun start heap => invariant start heap ∧ count start < limit)
      (fun start heap next finish => count next.1 = count start + 1 ∧
        invariant next.1 finish ∧ frame heap finish)
      (fun _ _ _ _ _ => False))
    (exit : ∀ start heap, invariant start heap → limit ≤ count start → normal heap)
    (initial : Heap) :
    BlockSpec (fun index => observe view (.while guard body) program (index, captures))
      (fun index heap => invariant index heap ∧ frame initial heap)
      (fun _ _ _ finish => normal finish ∧ frame initial finish)
      (fun _ _ _ _ _ => False) := by
  refine observe_while_fixed_variant_contract view program guard body guardFrame bodyFrame captures
    (fun index heap => invariant index heap ∧ frame initial heap)
    (fun start _ => limit - count start)
    (fun start heap next finish => count next = count start ∧ finish = heap ∧
      invariant next finish ∧ count next < limit)
    (fun _ finish => normal finish ∧ frame initial finish) (fun _ _ _ => False) ?_ ?_
  · apply guardSpec.mono
    · intro _ _ current
      exact current.1
    · intro _ _ _ _ _ impossible
      exact impossible
    · intro index heap again next finish current tested
      rcases tested with ⟨sameIndex, sameHeap, nextInvariant, available⟩
      subst finish
      by_cases active : again = true
      · simp only [if_pos active]
        exact ⟨sameIndex, trivial, nextInvariant, available.mp active⟩
      · simp only [if_neg active]
        exact ⟨exit next.1 heap nextInvariant
          (Nat.le_of_not_gt (fun bound => active (available.mpr bound))), current.2⟩
  · intro index heap current
    apply bodySpec.mono
    · rintro start afterGuard ⟨_, _, nextInvariant, active⟩
      exact ⟨nextInvariant, active⟩
    · rintro start afterGuard next finish ⟨sameIndex, rfl, _, available⟩
        ⟨advanced, nextInvariant, preserved⟩
      exact ⟨⟨nextInvariant, frameTrans current.2 preserved⟩, by dsimp only; omega⟩
    · intro _ _ _ _ _ _ impossible
      exact impossible

end Complexity.Language.Stmt
