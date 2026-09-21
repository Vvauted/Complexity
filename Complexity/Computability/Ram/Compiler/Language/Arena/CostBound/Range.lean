/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Loop
import Complexity.Language.Eval.Locals.Range.Represented

/-!
# Arena cost bounds from represented finite ranges

The heap-indexed guard and body observations used for finite-range
correspondence also connect mathematical potentials to the existing arena
loop bound. Each round may have an index- and state-dependent cost, including
allocating calls. The body certificate covers the actual complete iteration,
including its cursor update; the loop rule adds only its existing control costs.

Normal rounds advance the cursor and preserve the mathematical invariant.
Direct function returns retain their actual result and heap and do not run a
subsequent guard. Saved local completion has a different final guard path and
is not covered by this rule. No new execution semantics or termination argument
is introduced, and arena readiness remains a separate premise of the cost
observation being bounded.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

/-- Bound the same represented range using ordinary mathematical per-round
budgets. The source observation premises are those of
`Stmt.observe_while_rel_forIn_range_step`; their actual heaps may change.
The mathematical invariant and budget inequalities are independent of raw
handles. `bodyBound` pays for the whole source body, not just its callee.
Only already completed executions are bounded, so no positive-stride or
termination premise is needed by this cost implication. -/
theorem while_range_rel
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Locals α : Type} {w heapLimit depth : Nat}
    (view : Env Γ ≃ Locals) (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (stop stride : Nat) (stateRel : Nat → Mutable → Locals → Heap → Prop)
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
    (invariant : Nat → Mutable → Prop)
    (guardBound bodyBound potential : Nat → Mutable → Nat)
    (guardCost : ∀ index mutable locals heap, invariant index mutable →
      stateRel index mutable locals heap →
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩
        (guardBound index mutable))
    (bodyCost : ∀ index mutable locals heap, invariant index mutable → index < stop →
      stateRel index mutable locals heap →
      StmtArenaCostBound program w heapLimit depth body ⟨view.symm locals, heap⟩
        (bodyBound index mutable))
    (falseExit : ∀ index mutable, invariant index mutable → ¬ index < stop →
      guardBound index mutable + 11 ≤ potential index mutable)
    (normalStep : ∀ index mutable, invariant index mutable → index < stop →
      (step index mutable).1 = none →
      invariant (index + stride) (step index mutable).2 ∧
        guardBound index mutable + bodyBound index mutable +
          potential (index + stride) (step index mutable).2 + 10 ≤ potential index mutable)
    (returnExit : ∀ index mutable, invariant index mutable → index < stop →
      (step index mutable).1.isSome = true →
      guardBound index mutable + bodyBound index mutable + 17 ≤ potential index mutable)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (represented : stateRel start mutable locals heap) (initial : invariant start mutable) :
    StmtArenaCostBound program w heapLimit depth (.while guard body)
      ⟨view.symm locals, heap⟩ (potential start mutable) := by
  have guardResult {index : Nat} {current : Mutable}
      {entry finish : Complexity.Language.State Γ} {decision : Bool}
      (related : stateRel index current (view entry.locals) entry.heap)
      (execution : Complexity.Language.Exec program guard entry finish (.returned decision)) :
      decision = decide (index < stop) ∧
        stateRel index current (view finish.locals) finish.heap := by
    obtain ⟨after, finalHeap, observed, retained⟩ :=
      guardRel index current (view entry.locals) entry.heap related
    have modeled : Complexity.Language.Exec program guard entry
        ⟨view.symm after, finalHeap⟩ (.returned (decide (index < stop))) := by
      simpa only [Equiv.symm_apply_apply] using
        (Complexity.Language.Stmt.observe_eq_some_iff.mp observed)
    have same := execution.deterministic modeled
    refine ⟨Control.returned.inj same.2, ?_⟩
    rw [same.1]
    simpa only [Equiv.apply_symm_apply] using retained
  have bodyResult {index : Nat} {current : Mutable}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (inside : index < stop)
      (related : stateRel index current (view entry.locals) entry.heap)
      (execution : Complexity.Language.Exec program body entry finish control) :
      stateRel (if (step index current).1.isSome then index else index + stride)
          (step index current).2 (view finish.locals) finish.heap ∧
        control.Represents resultRep (step index current).1 finish.heap := by
    obtain ⟨actual, after, finalHeap, observed, retained, returned⟩ :=
      bodyRel index current (view entry.locals) entry.heap inside related
    have modeled : Complexity.Language.Exec program body entry
        ⟨view.symm after, finalHeap⟩ actual := by
      simpa only [Equiv.symm_apply_apply] using
        (Complexity.Language.Stmt.observe_eq_some_iff.mp observed)
    have same := execution.deterministic modeled
    rw [same.1, same.2]
    simpa only [Equiv.apply_symm_apply] using And.intro retained returned
  apply StmtArenaCostBound.while
    (X := Nat × Mutable)
    (invariant := fun index state =>
      stateRel index.1 index.2 (view state.locals) state.heap ∧ invariant index.1 index.2)
    (guardBound := fun index _ => guardBound index.1 index.2)
    (bodyBound := fun index _ _ => bodyBound index.1 index.2)
    (potential := fun index _ => potential index.1 index.2)
    (initialIndex := (start, mutable))
  · rintro ⟨index, current⟩ state ⟨related, valid⟩
    have bounded : StmtArenaCostBound program w heapLimit depth guard
        ⟨view.symm (view state.locals), state.heap⟩ (guardBound index current) :=
      guardCost index current (view state.locals) state.heap valid related
    simp only [Equiv.symm_apply_apply] at bounded
    exact @bounded
  · rintro ⟨index, current⟩ state afterGuard ⟨related, valid⟩ tested
    obtain ⟨decision, retained⟩ := guardResult related tested
    have inside : index < stop := by
      simpa only [decide_eq_true_eq] using decision.symm
    have bounded : StmtArenaCostBound program w heapLimit depth body
        ⟨view.symm (view afterGuard.locals), afterGuard.heap⟩ (bodyBound index current) :=
      bodyCost index current (view afterGuard.locals) afterGuard.heap valid inside retained
    simp only [Equiv.symm_apply_apply] at bounded
    exact @bounded
  · rintro ⟨index, current⟩ state afterGuard ⟨related, valid⟩ tested
    obtain ⟨decision, _⟩ := guardResult related tested
    exact falseExit index current valid
      (by simpa only [decide_eq_false_iff_not] using decision.symm)
  · rintro ⟨index, current⟩ state afterGuard afterBody ⟨related, valid⟩ tested iterated
    obtain ⟨decision, retained⟩ := guardResult related tested
    have inside : index < stop := by
      simpa only [decide_eq_true_eq] using decision.symm
    obtain ⟨nextRelated, returned⟩ := bodyResult inside retained iterated
    have normal : (step index current).1 = none := by
      cases completion : (step index current).1 with
      | none => rfl
      | some value => simp only [completion, Control.Represents] at returned
    obtain ⟨nextValid, budget⟩ := normalStep index current valid inside normal
    refine ⟨(index + stride, (step index current).2), ⟨?_, nextValid⟩, budget⟩
    simpa only [normal, Option.isSome_none, Bool.false_eq_true, if_false] using nextRelated
  · rintro ⟨index, current⟩ state afterGuard finish value ⟨related, valid⟩ tested iterated
    obtain ⟨decision, retained⟩ := guardResult related tested
    have inside : index < stop := by
      simpa only [decide_eq_true_eq] using decision.symm
    obtain ⟨_, returned⟩ := bodyResult inside retained iterated
    have completed : (step index current).1.isSome = true := by
      cases completion : (step index current).1 with
      | none => simp only [completion, Control.Represents] at returned
      | some value => rfl
    exact returnExit index current valid inside completed
  · exact ⟨by simpa only [Equiv.apply_symm_apply] using represented, initial⟩

end Ram.LanguageCompiler.StmtArenaCostBound
