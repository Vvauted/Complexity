/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Compiler.Local.Function

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
-/

namespace Ram.Examples.ArraySum

open Source Source.Array

/-- Function application exposes the represented list's sum and unchanged
caller state, without a stream driver or an instruction budget. -/
theorem eval_eq {w heapLimit : Nat} {array : ArrayRef w}
    {xs : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    sumFunctions.eval.sum array heapLimit entry = Part.some (wordSum xs, entry) :=
  (sum_function_runs_of_ref (program := sumFunctions.program) (depth := 0)
    hw fit entry represented).eval_eq_some

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
  let code := LocalCompiler.rawLink sumFunctions.registers sumFunctions.program
    (LocalCompiler.Function.trampoline sumFunctions.functionIndex.sum
      sumFunctions.function.sum.params)
  have hcompile : LocalCompiler.Function.compile sumFunctions.registers sumFunctions.program
      sumFunctions.functionIndex.sum sumFunctions.function.sum.params = some code := by
    set_option maxRecDepth 4096 in decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  have execution := sum_function_measured_of_ref (program := sumFunctions.program)
    (control := sumFunctions.registers) (depth := 0) (by decide : 0 < 32) fit entry represented
  obtain ⟨target, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured hcompile sumFunctions.function_lookup.sum
      hcode (by simpa using hstack) execution
  have count : LocalCompiler.Function.callSteps sumFunctions.registers
      sumFunctions.function.sum (18 * xs.length + 8) + 1 = 18 * xs.length + 67 := by
    simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
    decide
  simp only [runSum, sumFunctions.run.sum,
    max_eq_right (by decide : 1 ≤ sumFunctions.registers), returned, Option.map_some, value,
    wordSum_toNat, count]

-- The preloaded array contains 1, 2, 3. Constructing this host-side state is
-- explicit and is not included in the RAM function's transition count.
#eval runSum ⟨0, 3⟩ 3
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }

end Ram.Examples.ArraySum
