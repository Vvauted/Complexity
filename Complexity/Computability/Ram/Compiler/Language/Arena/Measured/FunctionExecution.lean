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

Mathematical specifications continue to use `FunctionTotal`. In particular,
an instantiated `RepresentedFunction.Total` or `RepresentedFunction.Refines`
contract needs no alternative result representation. The published outcome
retains all existing final memory and placement fields for a later invocation.
-/

namespace Ram.LanguageCompiler.ArenaMeasured

open Complexity.Language

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
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  obtain ⟨outcome, valueEq, heapEq, cursorEq, bodyEq⟩ := cost.execute launch
  have bodyBound : outcome.bodySteps ≤ bound + 2 := by
    rw [bodyEq]
    exact Nat.add_le_add_right (bounded execution ready cost) 2
  refine ⟨outcome, ?_, outcome.post specification hpre, ?_, bodyBound, ?_⟩
  · simpa only [valueEq, heapEq, cursorEq] using observed
  · rw [heapEq]
    exact execution.heap_shapeExtends
  · rw [outcome.steps_eq]
    exact Nat.add_le_add_right
      (LocalCompiler.Function.callSteps_mono _ _ bodyBound) 1

end Ram.LanguageCompiler.ArenaMeasured
