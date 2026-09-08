/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Calling functions with array arguments

The library's `sumPair` takes two array references and calls the same `sum`
implementation twice. Its source calls pass one typed handle per array; the
existing compiler evaluates the two word fields at each call site.

The list concatenation below is only a mathematical description of the returned
sum. Neither concatenation, allocation nor data loading is claimed to occur in
the implementation. Read-only references may overlap. The runnable example
starts with four explicitly preloaded heap words and requires no I/O driver
or instruction budget.
-/

namespace Ram.Examples.ArrayArguments

open Source Source.Array

/-- Two real array calls compute the sum of the concatenated mathematical lists,
without constructing that concatenation in machine memory. -/
theorem eval_append {w heapLimit : Nat} {left right : ArrayRef w}
    {xs ys : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (leftArray : left.Rep heapLimit xs entry) (rightArray : right.Rep heapLimit ys entry) :
    sumFunctions.function.sumPair.eval sumFunctions.program heapLimit
      (sumFunctions.arguments.sumPair left right) entry =
        Part.some (wordSum (xs ++ ys), entry) := by
  rw [wordSum_append]
  exact (sumPair_function_runs (depth := 0) hw leftFit rightFit entry
    leftArray rightArray).eval_eq_some

/-- Execute the typed two-array function on already represented 32-bit data.
The returned count includes both inner calls, the outer call, return and halt. -/
def runSumPair (left right : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32) :
    Option (Nat × Nat × StopReason) :=
  (LocalCompiler.Function.runUntil sumFunctions.registers sumFunctions.program
    sumFunctions.functionIndex.sumPair sumFunctions.function.sumPair.params heapLimit
    (sumFunctions.arguments.sumPair left right) entry).map fun result =>
      ((result.state.regs 0).toNat, result.steps, result.reason)

/-- The executable call returns the mathematical concatenation sum and its
actual full transition count. Stack capacity is a safety premise, not a supplied
runtime limit. All calls and returns are counted; host-side preloading is not. -/
theorem runSumPair_eq {heapLimit : Nat} {left right : ArrayRef 32}
    {xs ys : List (Word 32)} {entry : Source.State 32}
    (leftFit : left.base.toNat + xs.length < 2 ^ 32)
    (rightFit : right.base.toNat + ys.length < 2 ^ 32)
    (hstack : heapLimit + 2 * ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (leftArray : left.Rep heapLimit xs entry) (rightArray : right.Rep heapLimit ys entry) :
    runSumPair left right heapLimit entry =
      some (((xs ++ ys).map BitVec.toNat).sum % 2 ^ 32,
        16 * (xs.length + ys.length) + 147, .halted) := by
  let code := LocalCompiler.rawLink sumFunctions.registers sumFunctions.program
    (LocalCompiler.Function.trampoline sumFunctions.functionIndex.sumPair
      sumFunctions.function.sumPair.params)
  have hcompile : LocalCompiler.Function.compile sumFunctions.registers sumFunctions.program
      sumFunctions.functionIndex.sumPair sumFunctions.function.sumPair.params = some code := by
    decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  have measured := sumPair_function_measured (control := sumFunctions.registers) (depth := 0)
    (by decide : 0 < 32) leftFit rightFit sumFunctions.function_lookup.sum
    entry leftArray rightArray
  obtain ⟨target, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured hcompile
      sumFunctions.function_lookup.sumPair hcode hstack measured
  have count : LocalCompiler.Function.callSteps sumFunctions.registers
      sumFunctions.function.sumPair (16 * (xs.length + ys.length) + 82) + 1 =
        16 * (xs.length + ys.length) + 147 := by
    unfold LocalCompiler.Function.callSteps
    rw [ABI.callLocals_steps_eq]
    change 4 + (16 * (xs.length + ys.length) + 82) + 3 + 7 * 6 + 4 + 11 + 1 = _
    omega
  simp only [runSumPair, returned, Option.map_some, value, ← wordSum_append,
    wordSum_toNat, count]

-- Heap cells 0, 1, 2, 3 contain 1, 2, 3, 4. Preparing this state is explicit
-- host-side preloading, not an uncharged RAM operation inside sumPair.
#eval runSumPair ⟨0, 2⟩ ⟨2, 2⟩ 4
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }

end Ram.Examples.ArrayArguments
