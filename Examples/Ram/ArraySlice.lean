/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Source.Function.Linking
import Complexity.Computability.Ram.Compiler.Local.Function.Total
import Complexity.Tactic.Ram.Time

/-!
# Computing with a local borrowed array

`sumSlice` constructs a local two-word subarray reference and calls the existing
sum implementation. Its specification is an ordinary list `drop` followed by
`take`; the implementation neither copies nor allocates the selected elements.
The reference arithmetic and local bindings are actual source instructions.

The function has no input/output driver. Its correctness proof reuses the
array representation and sum contract, while its separate time proof charges
the descriptor assignments, both calling conventions and halt. The initial
heap is preloaded; no host loader is included in these RAM counts.
-/

namespace Ram.Examples.ArraySlice

open Source Source.Array

/-- A local array value can be passed directly to a previously proved function. -/
ram_def functions := ram_functions% {
  include sumFunctions as Sum;
  fn sumSlice(xs : array, offset, count) {
    let window : array := subslice(xs, offset, count);
    let answer ← call Sum.sum(window);
    return answer;
  }
}

/-- Borrowing and summing a contained slice returns its mathematical list sum
and preserves every caller state field. No time bound enters this contract. -/
theorem function_contract {w heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat) :
    FunctionContract functions.program heapLimit 1 functions.function.sumSlice
      (fun args entry => args = functions.arguments.sumSlice array offset count ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = wordSum ((xs.drop offset.toNat).take count.toNat) ∧ finish = entry) := by
  ram_total_vc args entry ⟨rfl, represented⟩
    [functions.body_eq.sumSlice, functions.result_eq.sumSlice]
  have sliceRep := represented.subslice offset count span
  have sliceFit := represented.subslice_end_lt offset count span fit
  have sumContract := (sum_function_contract_of_ref
    (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sliceFit).renameCalls functions.embeds.Sum
  ram_total_apply sumContract [functions.function_lookup.Sum.sum, sliceRep, ArrayRef.subslice]

/-- The semantic value uses the same declared implementation and ordinary list slice. -/
theorem eval_eq {w heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.sumSlice array offset count heapLimit entry =
      Part.some (wordSum ((xs.drop offset.toNat).take count.toNat), entry) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    function_contract hw fit span _ entry ⟨rfl, represented⟩
  exact execution.eval_eq_some

private def code : Code :=
  LocalCompiler.rawLink functions.registers functions.program
    (LocalCompiler.Function.trampoline functions.functionIndex.sumSlice
      functions.function.sumSlice.params)

private theorem compile_sumSlice : LocalCompiler.Function.compile
    functions.registers functions.program functions.functionIndex.sumSlice
      functions.function.sumSlice.params = some code := by
  set_option maxRecDepth 4096 in decide

private theorem code_length_lt : code.length < 2 ^ 32 := by
  set_option maxRecDepth 4096 in decide

/-- The compiled invocation halts from represented data and sufficient stack
space. The argument uses only the budget-free function contract. -/
theorem sumSlice_halts {array : ArrayRef 32} {offset count : Word 32}
    {heapLimit : Nat} {entry : Source.State 32}
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧ array.base.toNat + xs.length < 2 ^ 32)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts functions.registers functions.program
      functions.functionIndex.sumSlice functions.function.sumSlice.params heapLimit
      (functions.arguments.sumSlice array offset count) entry := by
  obtain ⟨xs, represented, fit⟩ := safe
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) fit span _ entry ⟨rfl, represented⟩
  exact LocalCompiler.Function.halts_of_execution compile_sumSlice
    functions.function_lookup.sumSlice code_length_lt hstack execution

/-- An ordinary executable value from the compiled slice-and-sum function.
All proofs are erased; the runtime inputs are the reference, slice bounds,
heap boundary and existing state, not the mathematical list or its sum. -/
def sumSlice (array : ArrayRef 32) (offset count : Word 32) (heapLimit : Nat)
    (entry : Source.State 32)
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧ array.base.toNat + xs.length < 2 ^ 32)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) : Nat :=
  (functions.apply.sumSlice array offset count heapLimit entry
    (sumSlice_halts safe span hstack)).toNat

/-- Correctness is a value equation using standard list operations. The modular
sum is retained for all legal inputs, not just those whose sum fits a word. -/
theorem sumSlice_eq {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32} (offset count : Word 32)
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    sumSlice array offset count heapLimit entry ⟨xs, represented, fit⟩ span hstack =
      (((xs.drop offset.toNat).take count.toNat).map BitVec.toNat).sum % 2 ^ 32 := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    function_contract (by decide : 0 < 32) fit span _ entry ⟨rfl, represented⟩
  have returned := LocalCompiler.Function.apply_eq_of_execution
    (sumSlice_halts ⟨xs, represented, fit⟩ span hstack) compile_sumSlice
    functions.function_lookup.sumSlice code_length_lt hstack execution
  simpa only [sumSlice, functions.apply.sumSlice, wordSum_toNat] using
    congrArg BitVec.toNat returned

/-- Descriptor arithmetic and assignments precede the actual sum call.
The bound comes from that source body and the independently proved sum bound. -/
theorem function_timeBound {w control heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat) :
    FunctionTimeBound control functions.program heapLimit 1 functions.function.sumSlice
      (fun args entry => args = functions.arguments.sumSlice array offset count ∧
        array.Rep heapLimit xs entry)
      (fun _ _ => 18 * count.toNat + 72) := by
  ram_time_vc args entry ⟨rfl, represented⟩ [functions.body_eq.sumSlice]
  have sliceRep := represented.subslice offset count span
  have sliceFit := represented.subslice_end_lt offset count span fit
  have sumCorrect := sum_function_contract_of_ref
    (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0) hw sliceFit
  have sumTime := (sum_function_timeBound_of_ref
    (control := control) (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sliceFit).renameCalls functions.embeds.Sum sumCorrect
  ram_time_call sumTime [functions.function_lookup.Sum.sum, ArrayRef.subslice,
    sliceRep, sliceRep.1.symm, sumFunctions.result_eq.sum]
  all_goals exact sliceRep

/-- The same compiled invocation additionally charges its outer call, return
and halt. The slice list and the proposed bound are not runtime arguments. -/
theorem runTotal_steps_le {array : ArrayRef 32} {offset count : Word 32}
    {heapLimit : Nat} {entry : Source.State 32} {xs : List (Word 32)}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    (functions.runTotal.sumSlice array offset count heapLimit entry
      (sumSlice_halts ⟨xs, represented, fit⟩ span hstack)).steps ≤ 18 * count.toNat + 142 := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) fit span _ entry ⟨rfl, represented⟩
  have bounded := LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (sumSlice_halts ⟨xs, represented, fit⟩ span hstack) compile_sumSlice
    functions.function_lookup.sumSlice code_length_lt hstack execution
    (function_timeBound (by decide : 0 < 32) fit span) ⟨rfl, represented⟩
  have callCount : LocalCompiler.Function.callSteps functions.registers
      functions.function.sumSlice (18 * count.toNat + 72) + 1 = 18 * count.toNat + 142 := by
    ram_simp [LocalCompiler.Function.callSteps_eq, functions.result_eq.sumSlice]
  simpa only [functions.runTotal.sumSlice, callCount] using bounded

-- This host state preloads 1, 2, 3, 4, 5. The call selects the middle three
-- elements; its reported count excludes this host-side preparation.
#eval (functions.run.sumSlice (⟨0, 5⟩ : ArrayRef 32) 1 3 5
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }).map
    fun result => ((result.state.regs 0).toNat, result.steps, result.reason)

end Ram.Examples.ArraySlice
