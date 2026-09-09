/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Scalar
import Complexity.Computability.Ram.Compiler.Language.Execution
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Transferring the scalar source proof through generic lowering

The independent source program and its mathematical proofs are imported
unchanged. The additional proofs here concern the actual intermediate natural
values and sufficient call nesting. The helper's existing source contract
identifies its actual returned value; its mathematical behavior is not reproved.

The shared lowering theorems produce both callable IR execution and a halted RAM
runner with the same mathematical minimum. No register layout, receiver update
or algorithm-specific source-to-IR adapter appears in this proof. Separate
source-execution cost bounds apply to that same invocation, including its
internal helper call, outer calling convention and final halt.
-/

namespace Complexity.Language.Examples.Scalar

open Ram.LanguageCompiler

/-- The helper needs no nested call and its actual sum must fit the word width. -/
theorem increment_realizable {w : Nat} :
    FunctionRealizable program w 0 (0 : Fin 2)
      (fun args => Env.head args + 1 < 2 ^ w) := by
  ram_source_realize (n)
  all_goals omega

/-- One call level suffices. The intermediate increment, not merely the final
minimum, and the compared limit must both be representable. -/
theorem boundedIncrement_realizable {w : Nat} :
    FunctionRealizable program w 1 (1 : Fin 2)
      (fun args => Env.head args + 1 < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  ram_source_realize (n limit) using increment_realizable, increment_total
  all_goals omega

/-- The automatically lowered helper returns the same mathematical increment.
The entry state and heap boundary are arbitrary; no manual register proof is needed. -/
theorem increment_functionExec {w heapLimit : Nat} (hw : 0 < w) (n : Nat)
    (fits : n + 1 < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 0
      (lowerFunc program (0 : Fin 2))
      (envWords w (Env.cons (τ := .nat) n Env.empty)) entry
      (valueWords w (τ := .nat) (n + 1)) finish := by
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, finish, execution, result⟩ :=
    increment_realizable.functionExec (heapLimit := heapLimit)
      increment_total hw args arguments fits trivial entry
  have actualValue : (value : Nat) = n + 1 := result
  exact ⟨finish, actualValue ▸ execution⟩

/-- The same source helper-call and branch program has an actual generated
function execution returning the mathematical minimum. This uses the shared
compiler theorem and the unchanged source correctness proof. -/
theorem boundedIncrement_functionExec {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 1
      (lowerFunc program (1 : Fin 2))
      (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry
      (valueWords w (τ := .nat) (min (n + 1) limit)) finish := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, finish, execution, result⟩ :=
    boundedIncrement_realizable.functionExec (heapLimit := heapLimit)
      boundedIncrement_total hw args arguments ⟨sumFits, limitFits⟩ trivial entry
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨finish, actualValue ▸ execution⟩

/-- The actual compiled machine returns the source-level minimum and preserves
the shared entry state. Its measured instruction count refers to this same
execution, without assuming or claiming an instruction upper bound. -/
theorem boundedIncrement_runUntil {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords w (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, bodySteps, target, result, execution, values, observed, time⟩ :=
    boundedIncrement_realizable.runUntil boundedIncrement_total hw args arguments
      ⟨sumFits, limitFits⟩ trivial entry codeCapacity stackCapacity
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time⟩

/-- The helper body spends four transitions on addition, four on returning its
value and setting the flag, and two on flag initialization. -/
theorem increment_costBound :
    FunctionCostBound program (0 : Fin 2) (fun _ => True) (fun _ => 10) := by
  ram_source_cost (n)

/-- The caller reuses the helper's complete call bound. Its comparison, selected
return branch and initialization add at most thirteen transitions. -/
theorem boundedIncrement_costBound :
    FunctionCostBound program (1 : Fin 2) (fun _ => True)
      (fun _ => callCost program (0 : Fin 2) 10 + 13) := by
  ram_source_cost (n limit) using increment_costBound
  all_goals omega

/-- The same halted machine invocation returns the mathematical minimum and
satisfies the independent source cost bound, including the outer call and halt. -/
theorem boundedIncrement_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords w (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps ∧
      bodySteps ≤ callCost program (0 : Fin 2) 10 + 13 ∧
      Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) (callCost program (0 : Fin 2) 10 + 13) + 1 := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, bodySteps, target, result, execution, values, observed, time,
      bodyBound, invocationBound⟩ :=
    boundedIncrement_realizable.runUntil_le boundedIncrement_total boundedIncrement_costBound
      hw args arguments ⟨sumFits, limitFits⟩ trivial trivial entry codeCapacity stackCapacity
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time,
    bodyBound, invocationBound⟩

end Complexity.Language.Examples.Scalar
