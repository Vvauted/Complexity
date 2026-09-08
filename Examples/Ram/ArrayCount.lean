/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Count
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Mathematical properties of a callable occurrence counter

These proofs use the existing array-count function and standard list facts.
They do not expand its traversal, registers or call frames. A decoded result
is a mathematical observation of the actual function, not a new executable
implementation. Each array is assumed to be present in memory already.
The executable example passes the target as an ordinary additional argument;
its complete count includes the actual function call and halt.
-/

namespace Ram.Examples.ArrayCount

open Source Source.Array

/-- Counting is insensitive to the order of the represented words. The heaps
and pointers may differ: this equates only returned counts, not shared states
or the work of constructing or permuting either array. -/
theorem eval_eq_of_perm {w heapLimit : Nat} {program : Program}
    {left right : ArrayRef w} {target : Word w} {xs ys : List (Word w)}
    {entry₁ entry₂ : Source.State w} (hw : 0 < w) (permutation : xs.Perm ys)
    (fit₁ : left.base.toNat + xs.length < 2 ^ w)
    (fit₂ : right.base.toNat + ys.length < 2 ^ w)
    (array₁ : left.Rep heapLimit xs entry₁)
    (array₂ : right.Rep heapLimit ys entry₂) :
    (countFunctions.function.count.evalTyped .word countFunctions.results_length.count
      program heapLimit
      (countFunctions.arguments.count left target) entry₁).map
        (fun result => result.1.toNat) =
    (countFunctions.function.count.evalTyped .word countFunctions.results_length.count
      program heapLimit
      (countFunctions.arguments.count right target) entry₂).map
        (fun result => result.1.toNat) := by
  rw [count_function_eval_toNat_of_ref hw fit₁ array₁,
    count_function_eval_toNat_of_ref hw fit₂ array₂,
    permutation.count_eq target]

/-- Execute the declared counter with a typed array and a scalar target.
The runner returns a value separately from the untouched output stream. -/
def runCount (array : ArrayRef 32) (target : Word 32) (heapLimit : Nat)
    (entry : Source.State 32) : Option (Nat × Nat × StopReason) :=
  (countFunctions.run.count array target heapLimit entry).map fun result =>
    ((DSL.ValueKind.decode .word
        (LocalCompiler.Function.returnedValues
          countFunctions.function.count.results.length result.state)
        ((LocalCompiler.Function.returnedValues_length _ _).trans
          countFunctions.results_length.count)).toNat,
      result.steps, result.reason)

/-- The real mixed-argument invocation returns the exact list count, with all
call, iteration and halt instructions included. The represented length bounds
the result, so the occurrence count cannot overflow a word. -/
theorem runCount_eq {heapLimit : Nat} {array : ArrayRef 32} {target : Word 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize countFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    runCount array target heapLimit entry =
      some (xs.count target, 20 * xs.length + 76, .halted) := by
  let code := LocalCompiler.rawLink countFunctions.registers countFunctions.program
    (LocalCompiler.Function.trampoline countFunctions.functionIndex.count
      countFunctions.function.count.params countFunctions.function.count.results.length)
  have hcompile : LocalCompiler.Function.compile countFunctions.registers countFunctions.program
      countFunctions.functionIndex.count countFunctions.function.count.params = some code := by
    set_option maxRecDepth 4096 in decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  have execution := count_function_measured_of_ref (program := countFunctions.program)
    (control := countFunctions.registers) (depth := 0) (target := target)
    (by decide : 0 < 32) fit entry represented
  obtain ⟨machine, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured hcompile countFunctions.function_lookup.count
      hcode (by simpa using hstack) execution
  have exactCount : xs.count target < 2 ^ 32 :=
    lt_of_le_of_lt List.count_le_length (by omega)
  have count : LocalCompiler.Function.callSteps countFunctions.registers
      countFunctions.function.count (20 * xs.length + 8) + 1 = 20 * xs.length + 76 := by
    simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
    decide
  simp only [runCount, countFunctions.run.count,
    max_eq_right (by decide : 1 ≤ countFunctions.registers), returned, Option.map_some, value,
    DSL.ValueKind.decode_word, Word.ofNat_toNat_of_lt exactCount, count]

-- The preloaded array is [1, 2, 1, 1], and the runtime target is 1.
#eval runCount ⟨0, 4⟩ 1 4
  { Source.State.initial [] with mem := fun address => if address.toNat = 1 then 2 else 1 }

end Ram.Examples.ArrayCount
