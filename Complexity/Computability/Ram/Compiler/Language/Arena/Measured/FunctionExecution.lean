/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution

/-!
# Publishing measured arena executions with independent specifications

A measured body, its structural cost bound and an independent source contract
describe the same invocation. `ArenaMeasured.execute_le` publishes its actual
typed RAM outcome, transports the body's heap/value/cursor observations, and
adds the existing initialization, outer-call and halt costs exactly once.
`ArenaMeasured.execute_eq` retains a measured exact count instead of replacing
it with an upper bound.

Mathematical specifications continue to use `FunctionTotal`. In particular,
an instantiated `RepresentedFunction.Total` or `RepresentedFunction.Refines`
contract needs no alternative result representation. The published outcome
retains all existing final memory and placement fields for a later invocation.
-/

namespace Ram.LanguageCompiler.ArenaMeasured

open Complexity.Language

/-- Publish a measured exact count together with the independently specified
mathematical result. All retained observations concern the same final heap,
value and cursor; initialization, the outer call and halt are counted once. -/
theorem execute_eq {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor coreSteps : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {placement : Nat → Word w} {entry : Source.State w}
    {P : Heap → Value (signatures[fn.val]'fn.isLt).result → Nat → Prop}
    {pre : Env (signatures[fn.val]'fn.isLt).params → Heap → Prop}
    {post : Env (signatures[fn.val]'fn.isLt).params → Heap →
      Value (signatures[fn.val]'fn.isLt).result → Heap → Prop}
    (measured : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧
          P finish.heap value finalCursor ∧ steps = coreSteps)
      ⟨args, heap⟩ cursor)
    (specification : FunctionTotal program fn pre post)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (hpre : pre args heap) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      P outcome.heap outcome.value outcome.cursor ∧
      post args heap outcome.value outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.bodySteps = coreSteps + 2 ∧
      outcome.result.steps =
        LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          (coreSteps + 2) + 1 := by
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, observed, rfl⟩ :=
    exists_returned_iff.mp measured
  obtain ⟨outcome, valueEq, heapEq, cursorEq, bodyEq⟩ := cost.execute launch
  refine ⟨outcome, ?_, outcome.post specification hpre, ?_, bodyEq, ?_⟩
  · simpa only [valueEq, heapEq, cursorEq] using observed
  · rw [heapEq]
    exact execution.heap_shapeExtends
  · rw [outcome.steps_eq, bodyEq]

/-- Retain the actual returning execution and its observations while applying
an independent structural bound to that same cost witness. -/
theorem exists_returned_le {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor bound : Nat} {Γ : List Ty} {result : Ty}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry : Complexity.Language.State Γ}
    {P : Complexity.Language.State Γ → Value result → Nat → Prop}
    (measured : ArenaMeasured program w heapLimit depth stmt
      (fun finish control finalCursor _ =>
        ∃ value, control = .returned value ∧ P finish value finalCursor) entry cursor)
    (bounded : StmtArenaCostBound program w heapLimit depth stmt entry bound) :
    ∃ finish value finalCursor steps,
      ∃ execution : Complexity.Language.Exec program stmt entry finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit depth cursor finalCursor,
          ArenaExecutionCost ready steps ∧ steps ≤ bound ∧ P finish value finalCursor := by
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  exact ⟨finish, value, finalCursor, steps, execution, ready, cost,
    bounded execution ready cost, observed⟩

/-- Publish a bound already retained by the measured execution, including its
two initialization instructions. The independent source specification describes
the same result; the caller's frame and final halt are added exactly once. -/
theorem execute_le_of_bound {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor bound : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {placement : Nat → Word w} {entry : Source.State w}
    {P : Heap → Value (signatures[fn.val]'fn.isLt).result → Nat → Prop}
    {pre : Env (signatures[fn.val]'fn.isLt).params → Heap → Prop}
    {post : Env (signatures[fn.val]'fn.isLt).params → Heap →
      Value (signatures[fn.val]'fn.isLt).result → Heap → Prop}
    (measured : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧ steps + 2 ≤ bound ∧
          P finish.heap value finalCursor)
      ⟨args, heap⟩ cursor)
    (specification : FunctionTotal program fn pre post)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (hpre : pre args heap) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      P outcome.heap outcome.value outcome.cursor ∧
      post args heap outcome.value outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.bodySteps ≤ bound ∧
      outcome.result.steps ≤
        LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          bound + 1 := by
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, budget, observed⟩ :=
    exists_returned_iff.mp measured
  have exactMeasured : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor coreSteps =>
        ∃ value, control = .returned value ∧
          P finish.heap value finalCursor ∧ coreSteps = steps)
      ⟨args, heap⟩ cursor :=
    exists_returned_iff.mpr
      ⟨finish, value, finalCursor, steps, execution, ready, cost, observed, rfl⟩
  obtain ⟨outcome, observed, property, shape, bodyEq, stepsEq⟩ :=
    exactMeasured.execute_eq specification launch hpre
  refine ⟨outcome, observed, property, shape, ?_, ?_⟩
  · simpa only [bodyEq] using budget
  · rw [stepsEq]
    exact Nat.add_le_add_right (LocalCompiler.Function.callSteps_mono _ _ budget) 1

/-- Publish the actual measured invocation with its independent source
postcondition, retained observations and complete instruction bound. The cost
certificate bounds the same execution; it is not a termination premise for
the source specification or a choice of a different execution. -/
theorem execute_le {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor bound : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {placement : Nat → Word w} {entry : Source.State w}
    {P : Heap → Value (signatures[fn.val]'fn.isLt).result → Nat → Prop}
    {pre : Env (signatures[fn.val]'fn.isLt).params → Heap → Prop}
    {post : Env (signatures[fn.val]'fn.isLt).params → Heap →
      Value (signatures[fn.val]'fn.isLt).result → Heap → Prop}
    (measured : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor _ =>
        ∃ value, control = .returned value ∧ P finish.heap value finalCursor)
      ⟨args, heap⟩ cursor)
    (bounded : StmtArenaCostBound program w heapLimit depth (program.body fn)
      ⟨args, heap⟩ bound)
    (specification : FunctionTotal program fn pre post)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (hpre : pre args heap) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      P outcome.heap outcome.value outcome.cursor ∧
      post args heap outcome.value outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.bodySteps ≤ bound + 2 ∧
      outcome.result.steps ≤
        LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          (bound + 2) + 1 := by
  refine execute_le_of_bound (bound := bound + 2) ?_ specification launch hpre
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  exact exists_returned_iff.mpr ⟨finish, value, finalCursor, steps, execution, ready, cost,
    Nat.add_le_add_right (bounded execution ready cost) 2, observed⟩

end Ram.LanguageCompiler.ArenaMeasured
