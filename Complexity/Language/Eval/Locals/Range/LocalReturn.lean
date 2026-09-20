/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Range.Represented
import Complexity.Language.Eval.Locals.LocalReturn.While

/-!
# Finite ranges with a local completion slot

The native finite range uses Lean's existing `forIn`. Its optional result is
represented by the actual pending slot, not by an enclosing function return.
The source body finishes normally on both paths. Only continuing rounds advance
the mathematical cursor; `stateRel` connects this cursor and mutable model to
the complete actual locals. A completed round takes the real masked false guard.
All state and result observations refer to the actual final heap.

The proof specializes the existing completion-aware while rule, using the
remaining native result as its invariant. It introduces neither another loop
induction nor a source evaluator, and makes no resource or word-width claim.
-/

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result τ : Ty}
variable {Mutable Locals α : Type}

/-- Relate a finite range to the same locally completing source loop. Running
entries have an empty pending slot, separately from `stateRel`, which also
describes completed states. The body retains normal source control; its native
optional result is observed in the actual slot at the same final heap. -/
theorem observe_while_completion_rel_forIn_range_step
    (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (pending : Atom Γ (.option τ))
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Exec program guard state state (.returned false))
    (stop stride : Nat) (positive : 0 < stride)
    (stateRel : Nat → Mutable → Locals → Heap → Prop)
    (resultRep : Representation α τ)
    (step : Nat → Mutable → Option α × Mutable)
    (guardRel : ∀ index mutable locals heap, stateRel index mutable locals heap →
      pending.eval (view.symm locals) = none →
      ∃ after finish,
        observe view guard program locals heap =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index mutable after finish ∧ pending.eval (view.symm after) = none)
    (bodyRel : ∀ index mutable locals heap, index < stop →
      stateRel index mutable locals heap → pending.eval (view.symm locals) = none →
      ∃ after finish,
        observe view body program locals heap = Part.some ((.normal, after), finish) ∧
        stateRel (if (step index mutable).1.isSome then index else index + stride)
          (step index mutable).2 after finish ∧
        resultRep.option.Rel (step index mutable).1 (pending.eval (view.symm after)) finish)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (initial : stateRel start mutable locals heap)
    (running : pending.eval (view.symm locals) = none) :
    ∃ after finish,
      observe view (.while guard body) program locals heap =
        Part.some ((.normal, after), finish) ∧
      (let outcome := Id.run (forIn (m := Id)
        ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
        ((none, (start, mutable)) : Option α × (Nat × Mutable))
        (fun index state =>
          let iteration := step index state.2.2
          iteration.1.elim
            (pure (ForInStep.yield (none, (index + stride, iteration.2))))
            (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
       stateRel outcome.2.1 outcome.2.2 after finish ∧
         resultRep.option.Rel outcome.1 (pending.eval (view.symm after)) finish) := by
  let advance (index : Nat) (state : Option α × (Nat × Mutable)) :
      Id (ForInStep (Option α × (Nat × Mutable))) :=
    let iteration := step index state.2.2
    iteration.1.elim
      (pure (.yield (none, (index + stride, iteration.2))))
      (fun value => pure (.done (some value, (index, iteration.2))))
  let remaining (index : Nat) (value : Mutable) := Id.run (forIn (m := Id)
    ({ start := index, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
    ((none, (index, value)) : Option α × (Nat × Mutable)) advance)
  have remaining_done (index : Nat) (value : Mutable) (outside : ¬ index < stop) :
      remaining index value = (none, (index, value)) := by
    have empty : (stop - index + stride - 1) / stride = 0 :=
      Nat.div_eq_of_lt (by omega)
    simp only [remaining, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      empty, List.range'_zero, List.forIn_nil, Id.run, Id.instMonad]
  have remaining_step (index : Nat) (value : Mutable) (inside : index < stop) :
      remaining index value =
        (step index value).1.elim
          (remaining (index + stride) (step index value).2)
          (fun result => (some result, (index, (step index value).2))) := by
    have sizeStep := Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside
    change (stop - index + stride - 1) / stride =
      (stop - (index + stride) + stride - 1) / stride + 1 at sizeStep
    simp only [remaining, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run]
    rw [sizeStep, List.range'_succ, List.forIn_cons]
    cases one : step index value with
    | mk completion next =>
        cases completion <;>
          simp only [advance, one, Option.elim_none, Option.elim_some, Id.instMonad]
  let expected := remaining start mutable
  let sourceRel (model : Nat × Mutable) (state : State Γ) : Prop :=
    stateRel model.1 model.2 (view state.locals) state.heap ∧
      pending.eval state.locals = none
  let post (completion : Option (Value τ)) (state : State Γ) : Prop :=
    stateRel expected.2.1 expected.2.2 (view state.locals) state.heap ∧
      resultRep.option.Rel expected.1 completion state.heap
  have total : TotalWP program (.while guard body)
      (fun finish => post (pending.eval finish.locals) finish) (fun _ _ => False)
      ⟨view.symm locals, heap⟩ := by
    refine TotalWP.while_completion pending sourceRel
      (fun model => remaining model.1 model.2 = expected)
      (measure fun model : Nat × Mutable => stop - model.1).wf post stoppedGuard
      (model := (start, mutable)) ?_ rfl ?_
    · rintro ⟨index, value⟩ ⟨actual, current⟩ same ⟨related, empty⟩
      obtain ⟨afterGuard, guardHeap, guarded, retained, stillEmpty⟩ :=
        guardRel index value (view actual) current related
          (by simpa only [Equiv.symm_apply_apply] using empty)
      have tested : Exec program guard ⟨actual, current⟩
          ⟨view.symm afterGuard, guardHeap⟩ (.returned (decide (index < stop))) := by
        simpa only [Equiv.symm_apply_apply] using observe_eq_some_iff.mp guarded
      refine ⟨_, _, tested, ?_⟩
      change if decide (index < stop) then _ else _
      by_cases inside : index < stop
      · simp only [inside, decide_true, ↓reduceIte]
        obtain ⟨afterBody, bodyHeap, iterated, advanced, returned⟩ :=
          bodyRel index value afterGuard guardHeap inside retained stillEmpty
        have executed : Exec program body ⟨view.symm afterGuard, guardHeap⟩
            ⟨view.symm afterBody, bodyHeap⟩ .normal := observe_eq_some_iff.mp iterated
        refine ⟨_, _, executed, ?_⟩
        change match pending.eval (view.symm afterBody) with
          | none => ∃ next, remaining next.1 next.2 = expected ∧
              sourceRel next ⟨view.symm afterBody, bodyHeap⟩ ∧
              (measure fun model : Nat × Mutable => stop - model.1).rel next (index, value)
          | some result => post (some result) ⟨view.symm afterBody, bodyHeap⟩
        have outcome := remaining_step index value inside
        cases one : step index value with
        | mk completion next =>
            cases completion with
            | none =>
                have absent : pending.eval (view.symm afterBody) = none := by
                  cases stored : pending.eval (view.symm afterBody) with
                  | none => rfl
                  | some result =>
                      simp only [one, Representation.option, stored] at returned
                rw [absent]
                refine ⟨(index + stride, next), ?_, ?_, ?_⟩
                · simpa only [one, Option.elim_none] using outcome.symm.trans same
                · refine ⟨?_, absent⟩
                  simpa only [sourceRel, one, Option.isSome_none, Bool.false_eq_true,
                    if_false, Equiv.apply_symm_apply] using advanced
                · change stop - (index + stride) < stop - index
                  omega
            | some result =>
                have completed : expected = (some result, (index, next)) := by
                  simpa only [one, Option.elim_some] using same.symm.trans outcome
                cases stored : pending.eval (view.symm afterBody) with
                | none =>
                    simp only [one, Representation.option, stored] at returned
                | some actualResult =>
                    change stateRel expected.2.1 expected.2.2
                      (view (view.symm afterBody)) bodyHeap ∧
                        resultRep.option.Rel expected.1 (some actualResult) bodyHeap
                    rw [completed]
                    constructor
                    · simpa only [one, Option.isSome_some, if_true,
                        Equiv.apply_symm_apply] using advanced
                    · simpa only [one, stored] using returned
      · simp only [inside, decide_false, Bool.false_eq_true, ↓reduceIte]
        have completed : expected = (none, (index, value)) :=
          same.symm.trans (remaining_done index value inside)
        change stateRel expected.2.1 expected.2.2 (view (view.symm afterGuard)) guardHeap ∧
          resultRep.option.Rel expected.1 (pending.eval (view.symm afterGuard)) guardHeap
        rw [completed, stillEmpty]
        exact ⟨by simpa only [Equiv.apply_symm_apply] using retained, trivial⟩
    · simpa only [sourceRel, Equiv.apply_symm_apply] using And.intro initial running
  obtain ⟨finish, control, execution, property⟩ := total
  cases control with
  | normal =>
      refine ⟨view finish.locals, finish.heap, ?_, ?_⟩
      · apply observe_eq_some_iff.mpr
        simpa only [Equiv.symm_apply_apply] using execution
      · simpa only [post, expected, remaining, advance, Equiv.symm_apply_apply] using property
  | returned value => exact False.elim property
  | fault error => exact False.elim property

end Complexity.Language.Stmt
