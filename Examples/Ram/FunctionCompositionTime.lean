/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Tactic.Ram.Time
import Complexity.Tactic.Ram.Run
import Examples.Ram.FunctionComposition

/-!
# Separate costs of a composition of imported functions

The same `FunctionComposition.functions` declaration makes two real source
calls. Their independently proved time bounds are transported through the
generated imports and applied at the actual call sites. Copy's budget-free
contract supplies the intermediate array representation needed by sum.
Neither callee loop nor its frame implementation is reopened.

The body bound includes both inner calls and their generated ABI overhead.
The final theorem additionally includes the enclosing call and halt of this
single compiled invocation. No host-side preloading or array conversion is
claimed as part of that execution.
-/

namespace Ram.Examples.FunctionComposition

open Source Source.Array

/-- The actual body first copies and then sums the resulting destination.
Previously proved callee bounds and real call blocks give its linear bound. -/
theorem function_timeBound {w control heapLimit : Nat} {source destination : ArrayRef w}
    {xs ys : List (Word w)} (hw : 0 < w) (sameLength : ys.length = xs.length)
    (fit : destination.base.toNat + xs.length < 2 ^ w)
    (disjoint : ArraysDisjoint source.base xs.length destination.base xs.length) :
    FunctionTimeBound control functions.program heapLimit 1 functions.function.copyThenSum
      (fun args entry => args = functions.arguments.copyThenSum source destination ∧
        source.Rep heapLimit xs entry ∧ destination.Rep heapLimit ys entry)
      (fun _ _ => 37 * xs.length + 104) := by
  ram_time_vc args entry ⟨rfl, sourceArray, destinationArray⟩
    [functions.body_eq.copyThenSum]
  have copyCorrect := copy_function_contract
    (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint
  have copyTime := (copy_function_timeBound
    (control := control) (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint).renameCalls functions.embeds.Copy copyCorrect
  have importedCopy := (copy_function_typed_contract
    (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint).renameCalls functions.embeds.Copy
  ram_time_apply importedCopy copyTime on (source.base, destination.base, source.length)
  · exact ⟨by simp only [sourceArray.length_eq], sourceArray.2, destinationArray.2⟩
  · exact ⟨by simp only [sourceArray.length_eq], sourceArray.2, destinationArray.2⟩
  · simp only [Func.renameCalls_results, copyFunctions.result_eq.copy]
    ram_bound
  · rintro _ middle ⟨_, destinationCopied, _, _, _⟩
    ram_time_vc [copyFunctions.result_eq.copy]
    have sumCorrect := sum_function_contract
      (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
      (base := destination.base) (xs := xs) hw fit
    have sumTime := (sum_function_timeBound
      (control := control) (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
      (base := destination.base) (xs := xs) hw fit).renameCalls functions.embeds.Sum sumCorrect
    ram_time_call sumTime
      [destinationArray.length_eq, sameLength, destinationCopied, sumFunctions.result_eq.sum]
    exact destinationCopied

/-- The bound includes every inner and outer call block and the final halt
of the same compiled invocation. Its termination proof remains budget-free. -/
theorem runTotal_steps_le {source destination : ArrayRef 32} {heapLimit : Nat}
    {entry : Source.State 32} (safe : Safe source destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (sameLength : ys.length = xs.length)
    (sourceArray : source.Rep heapLimit xs entry)
    (destinationArray : destination.Rep heapLimit ys entry)
    (disjoint : ArraysDisjoint source.base xs.length destination.base xs.length) :
    (functions.runTotal.copyThenSum source destination heapLimit entry
      (halts safe hstack)).steps ≤ 37 * xs.length + 160 := by
  have fit : destination.base.toNat + xs.length < 2 ^ 32 := by
    have within := destinationArray.2.2
    omega
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) sameLength fit disjoint _ entry
      ⟨rfl, sourceArray, destinationArray⟩
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (halts safe hstack) (execution := execution)
    (time := function_timeBound (by decide : 0 < 32) sameLength fit disjoint)
    (pre := ⟨rfl, sourceArray, destinationArray⟩))
    [functions.result_eq.copyThenSum]
  exact hstack

end Ram.Examples.FunctionComposition
