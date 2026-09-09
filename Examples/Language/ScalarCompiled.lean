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

The source contracts preserve every initial heap. These pure backend consumers
instantiate the shared heap relation with no source objects, so arbitrary RAM
entry memory is admitted. Their read-only source bodies separately establish
that the actual target invocation preserves this entry state.
-/

namespace Complexity.Language.Examples.Scalar

open Ram.LanguageCompiler

private theorem program_noHeapWrites : ∀ fn, NoHeapWrites (program.body fn) := by
  intro fn
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) fn
  · change NoHeapWrites Implementation.incrementBody
    simp [Implementation.incrementBody, NoHeapWrites]
  · change NoHeapWrites Implementation.boundedIncrementBody
    simp [Implementation.boundedIncrementBody, NoHeapWrites]

/-- The helper needs no nested call and its actual sum must fit the word width. -/
theorem increment_realizable {w : Nat} :
    FunctionRealizable program w 0 (0 : Fin 2)
      (fun args _ => Env.head args + 1 < 2 ^ w) := by
  ram_source_realize (n)
  all_goals omega

/-- One call level suffices. The intermediate increment, not merely the final
minimum, and the compared limit must both be representable. -/
theorem boundedIncrement_realizable {w : Nat} :
    FunctionRealizable program w 1 (1 : Fin 2)
      (fun args _ => Env.head args + 1 < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  ram_source_realize (n limit) using increment_realizable, increment_total
  all_goals omega

/-- The automatically lowered helper returns the same mathematical increment.
The entry state and heap boundary are arbitrary; no manual register proof is needed. -/
theorem increment_functionExec {w heapLimit : Nat} (hw : 0 < w) (n : Nat) (_sourceHeap : Heap)
    (fits : n + 1 < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 0
      (lowerFunc program (0 : Fin 2))
      (envWords (fun _ => 0) (Env.cons (τ := .nat) n Env.empty)) entry
      (valueWords (fun _ => 0) (τ := .nat) (n + 1)) finish := by
  clear _sourceHeap
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, finish, _, execution, result, _⟩ :=
    increment_realizable.functionExec (heapLimit := heapLimit)
      increment_total hw args ⟨#[]⟩ arguments fits trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
  have actualValue : (value : Nat) = n + 1 := result.1
  exact ⟨finish, actualValue ▸ execution⟩

/-- The same source helper-call and branch program has an actual generated
function execution returning the mathematical minimum. This uses the shared
compiler theorem and the unchanged source correctness proof. -/
theorem boundedIncrement_functionExec {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 1
      (lowerFunc program (1 : Fin 2))
      (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry
      (valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit)) finish := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, finish, _, execution, result, _⟩ :=
    boundedIncrement_realizable.functionExec (heapLimit := heapLimit)
      boundedIncrement_total hw args ⟨#[]⟩ arguments ⟨sumFits, limitFits⟩ trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨finish, actualValue ▸ execution⟩

/-- The actual compiled machine returns the source-level minimum and preserves
the shared entry state. Its measured instruction count refers to this same
execution, without assuming or claiming an instruction upper bound. -/
theorem boundedIncrement_runUntil {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, targetFinish, bodySteps, target, _, result, invocation, _, execution,
      values, observed, time⟩ :=
    boundedIncrement_realizable.runUntil boundedIncrement_total hw args ⟨#[]⟩ arguments
      ⟨sumFits, limitFits⟩ trivial entry (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have unchanged : targetFinish = entry := invocation.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites program program_noHeapWrites)
    (lowerBody_noSharedWrites program _ (program_noHeapWrites _))
  subst targetFinish
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time⟩

/-- The helper body spends four transitions on addition, four on returning its
value and setting the flag, and two on flag initialization. -/
theorem increment_costBound :
    FunctionCostBound program (0 : Fin 2) (fun _ _ => True) (fun _ _ => 10) := by
  ram_source_cost (n)

/-- The caller reuses the helper's complete call bound. Local initialization,
comparison, the selected assignment, dispatch and return add at most nineteen transitions. -/
theorem boundedIncrement_costBound :
    FunctionCostBound program (1 : Fin 2) (fun _ _ => True)
      (fun _ _ => callCost program (0 : Fin 2) 10 + 19) := by
  ram_source_cost (n limit) using increment_costBound
  all_goals omega

/-- The same halted machine invocation returns the mathematical minimum and
satisfies the independent source cost bound, including the outer call and halt. -/
theorem boundedIncrement_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps ∧
      bodySteps ≤ callCost program (0 : Fin 2) 10 + 19 ∧
      Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) (callCost program (0 : Fin 2) 10 + 19) + 1 := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, targetFinish, bodySteps, target, _, result, invocation, _, execution,
      values, observed, time, bodyBound, invocationBound⟩ :=
    boundedIncrement_realizable.runUntil_le boundedIncrement_total boundedIncrement_costBound
      hw args ⟨#[]⟩ arguments ⟨sumFits, limitFits⟩ trivial trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have unchanged : targetFinish = entry := invocation.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites program program_noHeapWrites)
    (lowerBody_noSharedWrites program _ (program_noHeapWrites _))
  subst targetFinish
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time,
    bodyBound, invocationBound⟩

end Complexity.Language.Examples.Scalar
