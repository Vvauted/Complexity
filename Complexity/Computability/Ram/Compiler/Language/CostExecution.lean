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
    {fn : Fin signatures.length} {args finish : Env signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : RealizedExec program w depth (program.body fn) args finish (.returned value)}
    (cost : ExecutionCost execution steps) (hw : 0 < w) (arguments : EnvFits w args)
    (entry : Source.State w) :
    (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit (envWords w args) entry =
      Part.some (steps + 2) := by
  obtain ⟨target, measured⟩ := cost.functionMeasuredExec 0 hw arguments entry
    (heapLimit := heapLimit)
  exact measured.bodyTime_eq_some

/-- Add a separate source-level time bound to the same halted invocation and
mathematical result. Realization, correctness and the bound may have independent
preconditions. No register simulation or second proof of source behavior is
required from the caller. -/
theorem FunctionRealizable.runUntil_le {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {fn : Fin signatures.length} {feasible pre costPre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop}
    {bound : Env signatures[fn].params → Nat}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (timeBound : FunctionCostBound program fn costPre bound)
    (hw : 0 < w) (args : Env signatures[fn].params) (arguments : EnvFits w args)
    (hfeasible : feasible args) (hpre : pre args) (hcost : costPre args)
    (entry : Source.State w)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (value : Value signatures[fn].result) (bodySteps : Nat) (target : Ram.State w),
      post args value ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords w args) entry =
        some ⟨target,
          LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
            bodySteps + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords w value ∧
      Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit (envWords w args) entry =
        Part.some bodySteps ∧
      bodySteps ≤ bound args ∧
      LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          bodySteps + 1 ≤
        LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
          (bound args) + 1 := by
  obtain ⟨finish, value, execution⟩ := realizable args hfeasible
  obtain ⟨steps, cost⟩ := execution.exists_cost
  have sourceBound : steps + 2 ≤ bound args := timeBound args hcost execution cost
  have sourceTime := cost.bodyTime_eq_some hw arguments entry (heapLimit := heapLimit)
  obtain ⟨value', bodySteps, target, property, run, values, observed, actualTime⟩ :=
    realizable.runUntil specification hw args arguments hfeasible hpre entry
      codeCapacity stackCapacity
  have same : bodySteps = steps + 2 := Part.some_injective (actualTime.symm.trans sourceTime)
  have bodyBound : bodySteps ≤ bound args := by simpa only [same] using sourceBound
  exact ⟨value', bodySteps, target, property, run, values, observed, actualTime, bodyBound,
    Nat.add_le_add_right (LocalCompiler.Function.callSteps_mono _ _ bodyBound) 1⟩

end Ram.LanguageCompiler
