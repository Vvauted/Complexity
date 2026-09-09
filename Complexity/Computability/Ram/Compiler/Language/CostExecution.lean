/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Execution
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation

/-!
# Source cost bounds for the actual compiled invocation

The source cost observation gives the generated function's existing `bodyTime`,
including its private return-flag wrapper and all internal calls. A separate
conditional source bound therefore applies to the same invocation as the
independent mathematical correctness theorem.

`FunctionRealizable.runUntil_le` reuses the existing unbounded runner theorem.
It does not set an execution budget or define behavior by a proposed cost. Its
complete bound adds the actual outer calling convention and final halt once.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Identify the existing semantic body-time observation from the source cost.
The target state and count are not selected to satisfy a proposed bound. -/
theorem ExecutionCost.bodyTime_eq_some {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit steps : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {args : Env signatures[fn].params} {initialHeap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : RealizedExec program w depth (program.body fn)
      ⟨args, initialHeap⟩ finish (.returned value)}
    (cost : ExecutionCost execution steps) (hw : 0 < w) (arguments : EnvFits w args)
    (entry : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap entry) :
    (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit
      (envWords placement args) entry =
      Part.some (steps + 2) := by
  obtain ⟨target, measured, _⟩ := cost.functionMeasuredExec 0 hw arguments entry represented
    (heapLimit := heapLimit)
  exact measured.bodyTime_eq_some

/-- Add a separate source-level time bound to the same halted invocation and
mathematical result. Realization, correctness and the bound may have independent
preconditions. No register simulation or second proof of source behavior is
required from the caller. -/
theorem FunctionRealizable.runUntil_le {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {feasible pre costPre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {bound : Env signatures[fn].params → Heap → Nat}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (timeBound : FunctionCostBound program fn costPre bound)
    (hw : 0 < w) (args : Env signatures[fn].params) (initialHeap : Heap)
    (arguments : EnvFits w args)
    (hfeasible : feasible args initialHeap) (hpre : pre args initialHeap)
    (hcost : costPre args initialHeap)
    (entry : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (value : Value signatures[fn].result) (finalHeap : Heap)
        (targetFinish : Source.State w) (bodySteps : Nat) (target : Ram.State w),
      program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      post args initialHeap value finalHeap ∧
      Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
        (envWords placement args) entry (valueWords placement value) targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
        some ⟨target,
          LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
            bodySteps + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords placement value ∧
      Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit
        (envWords placement args) entry =
        Part.some bodySteps ∧
      bodySteps ≤ bound args initialHeap ∧
      LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          bodySteps + 1 ≤
        LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          (bound args initialHeap) + 1 := by
  obtain ⟨finish, value, execution⟩ := realizable args initialHeap hfeasible
  obtain ⟨steps, cost⟩ := execution.exists_cost
  have sourceBound : steps + 2 ≤ bound args initialHeap :=
    timeBound args initialHeap hcost execution cost
  have sourceTime := cost.bodyTime_eq_some hw arguments entry represented
  obtain ⟨value', finalHeap, targetFinish, bodySteps, target, sourceEval, property,
      invocation, representedFinal, run, values,
      observed, actualTime⟩ :=
    realizable.runUntil specification hw args initialHeap arguments hfeasible hpre entry
      represented codeCapacity stackCapacity
  have same : bodySteps = steps + 2 := Part.some_injective (actualTime.symm.trans sourceTime)
  have bodyBound : bodySteps ≤ bound args initialHeap := by simpa only [same] using sourceBound
  exact ⟨value', finalHeap, targetFinish, bodySteps, target, sourceEval, property,
    invocation, representedFinal, run, values,
    observed, actualTime, bodyBound,
    Nat.add_le_add_right (LocalCompiler.Function.callSteps_mono _ _ bodyBound) 1⟩

end Ram.LanguageCompiler
