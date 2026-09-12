/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CostBound.Locals
import Complexity.Language.Eval.Locals.Range

/-!
# Cost bounds from native finite-range observations

The guard and body equations used for pure native range correspondence also
justify the existing source loop cost rule. Uniform component bounds are paid
by `StmtCostBound.whileLinearBound` with Lean's actual `Std.Legacy.Range.size`.
Normal iterations advance the cursor; an early function return retains its
actual cursor and is charged by the existing return rule. No new execution
semantics, cost model, block contract or author-supplied count proof is needed.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace StmtCostBound

/-- Bound the same pure finite source loop described by its native guard and
body observations. Only native return values are encoded; actual local and
heap transitions retain the behavior stated by those observations. -/
theorem while_range_encoded
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured α : Type} (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat) (positive : 0 < stride)
    (encode : α → Value result) (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable,
      Complexity.Language.Stmt.observe view guard program ((index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      Complexity.Language.Stmt.observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (guardBound bodyBound : Nat)
    (guardCost : ∀ index mutable heap,
      StmtCostBound program guard ⟨view.symm ((index, mutable), captures), heap⟩ guardBound)
    (bodyCost : ∀ index mutable heap, index < stop →
      StmtCostBound program body ⟨view.symm ((index, mutable), captures), heap⟩ bodyBound)
    (start : Nat) (mutable : Mutable) (heap : Heap) :
    StmtCostBound program (.while guard body)
      ⟨view.symm ((start, mutable), captures), heap⟩
      (whileLinearBound guardBound bodyBound
        (⟨start, stop, stride, positive⟩ : Std.Legacy.Range).size) := by
  have guardTrue {index : Nat} {state : Mutable} {entry finish : Heap}
      {after : (Nat × Mutable) × Captured}
      (tested : Complexity.Language.Stmt.observe view guard program
        ((index, state), captures) entry = Part.some ((.returned true, after), finish)) :
      index < stop ∧ after = ((index, state), captures) ∧ finish = entry := by
    rw [guardEq index state] at tested
    have same := Part.some_injective tested
    have controlEq := congrArg (fun outcome => outcome.1.1) same
    have inside : index < stop := by
      simpa only [Control.returned.injEq, decide_eq_true_eq] using controlEq
    exact ⟨inside, (congrArg (fun outcome => outcome.1.2) same).symm,
      (congrArg Prod.snd same).symm⟩
  have bodyNormal {index : Nat} {state : Mutable} {entry finish : Heap}
      {after : (Nat × Mutable) × Captured} (inside : index < stop)
      (iterated : Complexity.Language.Stmt.observe view body program
        ((index, state), captures) entry = Part.some ((.normal, after), finish)) :
      ∃ next, after = ((index + stride, next), captures) ∧ finish = entry := by
    rw [bodyEq index state inside] at iterated
    cases outcome : step index state with
    | mk returned next =>
        cases returned with
        | none =>
            simp only [outcome] at iterated
            have same := Part.some_injective iterated
            exact ⟨next, (congrArg (fun output => output.1.2) same).symm,
              (congrArg Prod.snd same).symm⟩
        | some value =>
            simp only [outcome] at iterated
            have impossible : (Control.returned (encode value) : Control result) = .normal :=
              congrArg (fun output => output.1.1) (Part.some_injective iterated)
            cases impossible
  apply while_observe view
    (invariant := fun locals _ => locals.2 = captures)
    (guardBound := fun _ _ => guardBound)
    (bodyBound := fun _ _ _ _ => bodyBound)
    (potential := fun locals _ => whileLinearBound guardBound bodyBound
      (⟨locals.1.1, stop, stride, positive⟩ : Std.Legacy.Range).size)
  · rintro ⟨⟨index, state⟩, fixed⟩ entry current
    change fixed = captures at current
    subst fixed
    exact guardCost index state entry
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after finish current tested
    change fixed = captures at current
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    exact bodyCost index state _ inside
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after afterHeap finish finishHeap
      current tested iterated
    change fixed = captures at current
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    obtain ⟨next, rfl, rfl⟩ := bodyNormal inside iterated
    rfl
  · intro locals entry after finish current tested
    exact whileLinearBound_exit _ _ _
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after afterHeap finish finishHeap
      current tested iterated
    change fixed = captures at current
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    obtain ⟨next, rfl, rfl⟩ := bodyNormal inside iterated
    apply whileLinearBound_step
    exact (Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside).symm.le
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after afterHeap finish finishHeap value
      current tested returned
    change fixed = captures at current
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    apply whileLinearBound_return
    have rounds := Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside
    exact lt_of_lt_of_eq (Nat.zero_lt_succ _) rounds.symm
  · rfl

end StmtCostBound

end Ram.LanguageCompiler
