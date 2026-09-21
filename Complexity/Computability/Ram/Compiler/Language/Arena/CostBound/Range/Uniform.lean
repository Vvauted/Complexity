/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Range
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Range.Completion
import Complexity.Computability.Ram.Compiler.Language.CostBound.Locals

/-!
# Uniform arena bounds for represented finite ranges

The actual guard and body may allocate, return from the function or carry a saved
local result. Uniform component bounds, for example those inferred by
`ram_source_arena_cost`, combine with the generated single-round relations through
the existing range rules. The remaining-round count is Lean's existing finite-range
size. A direct function return uses its own control charge without a subsequent
guard. Early local completion still pays for its actual final masked guard; the
same uniform guard bound covers both the running and stopped paths.

The linear expression is a proved upper bound, not an instruction annotation or
a second evaluator. Source correctness, arena readiness and capacity remain
independent of the proposed component bounds.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

/-- Uniform guard and whole-body certificates give the existing linear bound
for normal or directly returning finite ranges. A returning round pays the
actual function-return charge, without requiring a subsequent guard or another
loop induction. Positive stride supplies the ordinary finite-range size. -/
theorem while_range_rel_linear
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Locals α : Type} {w heapLimit depth : Nat}
    (view : Env Γ ≃ Locals) (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (stop stride : Nat) (positive : 0 < stride)
    (stateRel : Nat → Mutable → Locals → Heap → Prop)
    (resultRep : Representation α result)
    (step : Nat → Mutable → Option α × Mutable)
    (guardRel : ∀ index mutable locals heap, stateRel index mutable locals heap →
      ∃ after finish,
        Complexity.Language.Stmt.observe view guard program locals heap =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index mutable after finish)
    (bodyRel : ∀ index mutable locals heap, index < stop →
      stateRel index mutable locals heap →
      ∃ control after finish,
        Complexity.Language.Stmt.observe view body program locals heap =
          Part.some ((control, after), finish) ∧
        stateRel (if (step index mutable).1.isSome then index else index + stride)
          (step index mutable).2 after finish ∧
        control.Represents resultRep (step index mutable).1 finish)
    (guardBound bodyBound : Nat)
    (guardCost : ∀ locals heap,
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩ guardBound)
    (bodyCost : ∀ locals heap,
      StmtArenaCostBound program w heapLimit depth body ⟨view.symm locals, heap⟩ bodyBound)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (represented : stateRel start mutable locals heap) :
    StmtArenaCostBound program w heapLimit depth (.while guard body)
      ⟨view.symm locals, heap⟩
      (StmtCostBound.whileLinearBound guardBound bodyBound
        ({ start, stop, step := stride, step_pos := positive } : Std.Legacy.Range).size) := by
  let remaining (index : Nat) :=
    ({ start := index, stop, step := stride, step_pos := positive } : Std.Legacy.Range).size
  have decreases (index : Nat) (inside : index < stop) :
      remaining (index + stride) + 1 = remaining index :=
    (Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop, step := stride, step_pos := positive } inside).symm
  apply while_range_rel view program guard body stop stride stateRel resultRep step guardRel bodyRel
    (invariant := fun _ _ => True)
    (guardBound := fun _ _ => guardBound) (bodyBound := fun _ _ => bodyBound)
    (potential := fun index _ => StmtCostBound.whileLinearBound guardBound bodyBound (remaining index))
    (start := start) (mutable := mutable) (locals := locals) (heap := heap)
  · intro index mutable locals heap _ _
    exact guardCost locals heap
  · intro index mutable locals heap _ _ _
    exact bodyCost locals heap
  · intro index mutable _ _
    exact StmtCostBound.whileLinearBound_exit _ _ _
  · intro index mutable _ inside _
    exact ⟨trivial, StmtCostBound.whileLinearBound_step _ _ (decreases index inside).le⟩
  · intro index mutable _ inside _
    apply StmtCostBound.whileLinearBound_return
    exact lt_of_lt_of_eq (Nat.zero_lt_succ _) (decreases index inside)
  · exact represented
  · trivial

/-- A finite represented range with uniform guard and whole-body certificates
has the existing linear loop bound. This includes local completion and its
subsequent false guard, without requiring another loop induction or author-
written potential inequalities. The positive stride determines the ordinary
range size; this statement still bounds supplied completed executions. -/
theorem while_range_completion_rel_linear
    {signatures : List Signature} {Γ : List Ty} {result τ : Ty}
    {Mutable Locals α : Type} {w heapLimit depth : Nat}
    (view : Env Γ ≃ Locals) (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (pending : Atom Γ (.option τ))
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Complexity.Language.Exec program guard state state (.returned false))
    (stop stride : Nat) (positive : 0 < stride)
    (stateRel : Nat → Mutable → Locals → Heap → Prop)
    (resultRep : Representation α τ)
    (step : Nat → Mutable → Option α × Mutable)
    (guardRel : ∀ index mutable locals heap, stateRel index mutable locals heap →
      pending.eval (view.symm locals) = none →
      ∃ after finish,
        Complexity.Language.Stmt.observe view guard program locals heap =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index mutable after finish ∧ pending.eval (view.symm after) = none)
    (bodyRel : ∀ index mutable locals heap, index < stop →
      stateRel index mutable locals heap → pending.eval (view.symm locals) = none →
      ∃ after finish,
        Complexity.Language.Stmt.observe view body program locals heap =
          Part.some ((.normal, after), finish) ∧
        stateRel (if (step index mutable).1.isSome then index else index + stride)
          (step index mutable).2 after finish ∧
        resultRep.option.Rel (step index mutable).1 (pending.eval (view.symm after)) finish)
    (guardBound bodyBound : Nat)
    (guardCost : ∀ locals heap,
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩ guardBound)
    (bodyCost : ∀ locals heap,
      StmtArenaCostBound program w heapLimit depth body ⟨view.symm locals, heap⟩ bodyBound)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (represented : stateRel start mutable locals heap)
    (running : pending.eval (view.symm locals) = none) :
    StmtArenaCostBound program w heapLimit depth (.while guard body)
      ⟨view.symm locals, heap⟩
      (StmtCostBound.whileLinearBound guardBound bodyBound
        ({ start, stop, step := stride, step_pos := positive } : Std.Legacy.Range).size) := by
  let remaining (index : Nat) :=
    ({ start := index, stop, step := stride, step_pos := positive } : Std.Legacy.Range).size
  have decreases (index : Nat) (inside : index < stop) :
      remaining (index + stride) + 1 = remaining index :=
    (Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop, step := stride, step_pos := positive } inside).symm
  apply while_range_completion_rel view program guard body pending stoppedGuard
    stop stride stateRel resultRep step guardRel bodyRel
    (invariant := fun _ _ => True)
    (guardBound := fun _ _ => guardBound) (bodyBound := fun _ _ => bodyBound)
    (potential := fun index _ => StmtCostBound.whileLinearBound guardBound bodyBound (remaining index))
    (completedGuardBound := fun _ _ _ => guardBound)
    (start := start) (mutable := mutable) (locals := locals) (heap := heap)
  · intro index mutable locals heap _ _ _
    exact guardCost locals heap
  · intro index mutable locals heap _ _ _ _
    exact bodyCost locals heap
  · intro index mutable value locals heap _ _
    exact guardCost locals heap
  · intro index mutable _ _
    exact StmtCostBound.whileLinearBound_exit _ _ _
  · intro index mutable _ inside _
    exact ⟨trivial, StmtCostBound.whileLinearBound_step _ _ (decreases index inside).le⟩
  · intro index mutable value _ inside _
    have positiveRemaining : 1 ≤ remaining index := by
      have next := decreases index inside
      omega
    have paid := StmtCostBound.whileLinearBound_step guardBound bodyBound
      (next := 0) positiveRemaining
    change guardBound + bodyBound + guardBound + 21 ≤
      StmtCostBound.whileLinearBound guardBound bodyBound (remaining index)
    unfold StmtCostBound.whileLinearBound at paid ⊢
    omega
  · exact represented
  · exact running
  · trivial

end Ram.LanguageCompiler.StmtArenaCostBound
