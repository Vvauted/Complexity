/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Tactic.Ram.Run

/-!
# Calling the reusable array-sum function

The function declared in `Complexity.Computability.Ram.Array.Sum` iterates over
an array reference and returns its sum. The mathematical specification uses an
ordinary list; its value and execution count describe that same implementation.
The example reuses function contracts without opening the loop or its locals.

The array is already represented in memory. Neither the mathematical list nor
the host-side sample state is an executable loader. The function requires no
input/output driver; its unbounded runner additionally counts the actual outer
call, return and halt. Word sums retain their modular arithmetic semantics.
The ordinary `sum` function executes that same compiled call and returns a
natural number. Its termination proof is erased; neither a mathematical list
nor a proposed result or time budget is passed to the executable function.
-/

namespace Ram.Examples.ArraySum

open Source Source.Array

private theorem sum_callSteps (length : Nat) :
    LocalCompiler.Function.callSteps sumFunctions.registers
      sumFunctions.function.sum (18 * length + 8) + 1 = 18 * length + 67 := by
  simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
  decide

/-- Function application exposes the represented list's sum and unchanged
caller state, without a stream driver or an instruction budget. -/
theorem eval_eq {w heapLimit : Nat} {array : ArrayRef w}
    {xs : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    sumFunctions.eval.sum array heapLimit entry = Part.some (wordSum xs, entry) :=
  (sum_function_runs_of_ref (program := sumFunctions.program) (depth := 0)
    hw fit entry represented).eval_eq_some

/-- A represented array and sufficient stack space make the compiled function
halt. Only budget-free correctness is used to establish this fact. -/
theorem sum_halts {array : ArrayRef 32} {heapLimit : Nat} {entry : Source.State 32}
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧
      array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts sumFunctions.registers sumFunctions.program
      sumFunctions.functionIndex.sum sumFunctions.function.sum.params heapLimit
      (sumFunctions.arguments.sum array) entry := by
  obtain ⟨xs, represented, fit⟩ := safe
  ram_run_apply (LocalCompiler.Function.halts_of_contract
    (contract := sum_function_contract_of_ref (program := sumFunctions.program) (depth := 0)
      (by decide : 0 < 32) fit) (pre := ⟨rfl, represented⟩))
    [sumFunctions.function_lookup.sum]
  simpa using hstack

/-- Execute the compiled array-sum function and return its decoded word.
The logical safety proof is erased; the only data inputs are the reference,
heap boundary and preloaded state. No mathematical answer or fuel is supplied. -/
def sum (array : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32)
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧
      array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32) : Nat :=
  (sumFunctions.apply.sum array heapLimit entry (sum_halts safe hstack)).toNat

/-- The ordinary executable function equals the mathematical list sum modulo
the word range. The list specifies memory; it is not an execution parameter. -/
theorem sum_eq {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    sum array heapLimit entry ⟨xs, represented, fit⟩ hstack =
      (xs.map BitVec.toNat).sum % 2 ^ 32 := by
  have execution := sum_function_runs_of_ref (program := sumFunctions.program) (depth := 0)
    (by decide : 0 < 32) fit entry represented
  have result := by
    ram_run_apply (LocalCompiler.Function.apply_eq_of_execution
      (sum_halts ⟨xs, represented, fit⟩ hstack) (execution := execution))
      [sumFunctions.function_lookup.sum]
    simpa using hstack
  simpa only [sum, sumFunctions.apply.sum, wordSum_toNat] using congrArg BitVec.toNat result

/-- If the mathematical sum fits, the executable function returns that natural
number exactly. This is a property of the same modular implementation. -/
theorem sum_eq_of_sum_lt {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry)
    (hsum : (xs.map BitVec.toNat).sum < 2 ^ 32) :
    sum array heapLimit entry ⟨xs, represented, fit⟩ hstack =
      (xs.map BitVec.toNat).sum := by
  rw [sum_eq fit hstack represented, Nat.mod_eq_of_lt hsum]

/-- Execute the declared function on a preloaded array and observe its returned
natural number, full transition count and stopping reason. -/
def runSum (array : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32) :
    Option (Nat × Nat × StopReason) :=
  (sumFunctions.run.sum array heapLimit entry).map fun result =>
    ((result.state.regs 0).toNat, result.steps, result.reason)

/-- The compiled function returns the mathematical sum and its exact full
count. Stack capacity is a safety premise, not a supplied execution limit;
the count includes the enclosing call and halt but not host-side preloading. -/
theorem runSum_eq {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    runSum array heapLimit entry =
      some ((xs.map BitVec.toNat).sum % 2 ^ 32, 18 * xs.length + 67, .halted) := by
  have execution := sum_function_measured_of_ref (program := sumFunctions.program)
    (control := sumFunctions.registers) (depth := 0) (by decide : 0 < 32) fit entry represented
  have run := by
    ram_run_apply (LocalCompiler.Function.runUntil_eq_of_measured
      (fn := sumFunctions.functionIndex.sum) (execution := execution))
      [sumFunctions.function_lookup.sum]
    simpa using hstack
  obtain ⟨target, returned, value, _⟩ := run
  simp only [runSum, sumFunctions.run.sum,
    max_eq_right (by decide : 1 ≤ sumFunctions.registers), returned, Option.map_some, value,
    wordSum_toNat, sum_callSteps]

/-- The total executable application has the same complete transition count.
This independent time proof is not used to define `sum` or prove it terminates. -/
theorem runTotal_steps {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    (sumFunctions.runTotal.sum array heapLimit entry
      (sum_halts ⟨xs, represented, fit⟩ hstack)).steps = 18 * xs.length + 67 := by
  have execution := sum_function_runs_of_ref (program := sumFunctions.program) (depth := 0)
    (by decide : 0 < 32) fit entry represented
  have measured := sum_function_measured_of_ref (program := sumFunctions.program)
    (control := sumFunctions.registers) (depth := 0) (by decide : 0 < 32) fit entry represented
  have count := by
    ram_run_apply (LocalCompiler.Function.runTotal_steps_eq_of_execution
      (sum_halts ⟨xs, represented, fit⟩ hstack) (execution := execution)
      (time := measured.bodyTime_eq_some)) [sumFunctions.function_lookup.sum]
    simpa using hstack
  simpa only [sumFunctions.runTotal.sum, sum_callSteps] using count

-- The preloaded array contains 1, 2, 3. Constructing this host-side state is
-- explicit and is not included in the RAM function's transition count.
private def sampleState : Source.State 32 :=
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }

private theorem sample_represented :
    (⟨0, 3⟩ : ArrayRef 32).Rep 3 ([1, 2, 3] : List (Word 32)) sampleState := by
  refine ⟨by decide, ⟨by decide, ?_⟩, by decide⟩
  intro i hi
  have indices : i = 0 ∨ i = 1 ∨ i = 2 := by
    change i < 3 at hi
    omega
  rcases indices with rfl | rfl | rfl <;> rfl

#eval runSum ⟨0, 3⟩ 3 sampleState

-- The proof is erased. This executes the compiled function and returns an
-- ordinary natural number, without an Option or a mathematical result argument.
#eval sum ⟨0, 3⟩ 3 sampleState ⟨[1, 2, 3], sample_represented, by decide⟩ (by decide)

end Ram.Examples.ArraySum
