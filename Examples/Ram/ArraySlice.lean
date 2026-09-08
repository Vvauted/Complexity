/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Source.Function.Linking
import Complexity.Computability.Ram.Verification.Function.Typed
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Tactic.Ram.Run
import Complexity.Tactic.Ram.Time

/-!
# Composing a returned borrowed array

`slice` returns a borrowed subarray reference. `sumSlice` calls it and passes
the actual returned array to the existing sum implementation. Its specification
is an ordinary list `drop` followed by `take`; neither function copies or
allocates the selected elements. Reference arithmetic and both returned fields
are evaluated by the same compiled function call.

The function has no input/output driver. Its correctness proof reuses the
array representation and sum contract, while its separate time proof charges
both inner calls, the outer calling convention and halt. The initial heap is
preloaded; no host loader is included in these RAM counts.
-/

namespace Ram.Examples.ArraySlice

open Source Source.Array

/-- A returned array value is passed directly to a previously proved function. -/
ram_def functions := ram_functions% {
  include sumFunctions as Sum;
  fn slice(xs : array, offset, count) : array {
    return subslice(xs, offset, count);
  }
  fn sumSlice(xs : array, offset, count) {
    let window ← call slice(xs, offset, count);
    let answer ← call Sum.sum(window);
    return answer;
  }
}

/-- The slice body itself is empty. Its address arithmetic and two-field return
are part of the actual calling convention, not an uncounted host computation. -/
theorem slice_timeBound {w control heapLimit depth : Nat}
    {P : List (Word w) → Source.State w → Prop} :
    FunctionTimeBound control functions.program heapLimit depth functions.function.slice
      P (fun _ _ => 0) := by
  apply FunctionTimeBound.of_body_at
  intro args entry _
  simpa only [functions.body_eq.slice] using
    (TimeBound.skip (control := control) (program := functions.program)
      (heapLimit := heapLimit) (depth := depth) (fun s => s = entry.enter args))

/-- The actual returned reference represents the mathematical list slice. The
postcondition carries that representation directly to its next client. -/
theorem slice_contract {w heapLimit depth : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)}
    (span : offset.toNat + count.toNat ≤ array.length.toNat) :
    TypedFunctionContract functions.program heapLimit depth functions.function.slice .array
      (fun input : ArrayRef w × Word w × Word w =>
        functions.arguments.slice input.1 input.2.1 input.2.2)
      (fun input entry => input = (array, offset, count) ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish => value = array.subslice offset count ∧
        value.Rep heapLimit ((xs.drop offset.toNat).take count.toNat) finish ∧
        finish = entry) := by
  apply TypedFunctionContract.of_wp functions.results_length.slice
  · rintro _ _ ⟨rfl, _⟩
    exact functions.arguments_length.slice array offset count
  · decide
  · rintro _ entry ⟨rfl, represented⟩
    ram_total_vc [functions.body_eq.slice, functions.result_eq.slice,
      functions.arguments.slice, Source.State.enter, Source.State.restore, DSL.ValueKind.decode,
      ArrayRef.subslice]
    simpa [ArrayRef.subslice] using represented.subslice offset count span

/-- The reusable slice function returns an ordinary typed reference, separately
from any caller or stream driver. Its shared state is unchanged. -/
theorem slice_eval_eq {w heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} {entry : Source.State w}
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.slice array offset count heapLimit entry =
      Part.some (array.subslice offset count, entry) := by
  obtain ⟨value, finish, execution, rfl, _, rfl⟩ :=
    slice_contract (depth := 0) span (array, offset, count) entry ⟨rfl, represented⟩
  exact execution.evalTyped_eq_some functions.results_length.slice

/-- Borrowing and summing a contained slice returns its mathematical list sum
and preserves every caller state field. No time bound enters this contract. -/
theorem function_contract {w heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat) :
    TypedFunctionContract functions.program heapLimit 1 functions.function.sumSlice .word
      (fun input : ArrayRef w × Word w × Word w =>
        functions.arguments.sumSlice input.1 input.2.1 input.2.2)
      (fun input entry => input = (array, offset, count) ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = wordSum ((xs.drop offset.toNat).take count.toNat) ∧ finish = entry) := by
  apply TypedFunctionContract.of_wp functions.results_length.sumSlice
  · rintro _ _ ⟨rfl, _⟩
    exact functions.arguments_length.sumSlice array offset count
  · decide
  · rintro _ entry ⟨rfl, represented⟩
    ram_total_vc [functions.body_eq.sumSlice, functions.result_eq.sumSlice]
    ram_total_apply
      ((slice_contract (heapLimit := heapLimit) (depth := 0) (xs := xs) span).wp_call
        (arg := (array, offset, count)))
      [functions.function_lookup.slice, functions.results_length.slice,
        functions.arguments.slice, functions.arguments.sumSlice, Source.State.enter, represented]
    rintro window middle rfl sliceRep rfl _
    have sliceFit := represented.subslice_end_lt offset count span fit
    have sumContract := (sum_function_contract_of_ref
      (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
      hw sliceFit).renameCalls functions.embeds.Sum
    ram_total_apply sumContract [functions.function_lookup.Sum.sum,
      functions.arguments.sumSlice, sliceRep, ArrayRef.subslice,
      Source.State.enter, Source.State.restore]

/-- The semantic value uses the same declared implementation and ordinary list slice. -/
theorem eval_eq {w heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.sumSlice array offset count heapLimit entry =
      Part.some (wordSum ((xs.drop offset.toNat).take count.toNat), entry) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    function_contract hw fit span (array, offset, count) entry ⟨rfl, represented⟩
  exact execution.evalTyped_eq_some functions.results_length.sumSlice

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
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (arg := (array, offset, count))
    (contract := function_contract (by decide : 0 < 32) fit span)
    (pre := ⟨rfl, represented⟩)) [functions.function_lookup.sumSlice]
  exact hstack

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
    function_contract (by decide : 0 < 32) fit span (array, offset, count) entry
      ⟨rfl, represented⟩
  have returned := by
    ram_run_apply (LocalCompiler.Function.applyTyped_eq_of_execution
      (kind := .word) (shape := functions.results_length.sumSlice)
      (sumSlice_halts ⟨xs, represented, fit⟩ span hstack) (execution := execution))
      [functions.function_lookup.sumSlice]
    exact hstack
  simpa only [sumSlice, functions.apply.sumSlice, wordSum_toNat] using
    congrArg BitVec.toNat returned

/-- The actual slice call precedes the sum call. The slice body costs zero, but
its argument handling, address calculation and two-field return are all charged. -/
theorem function_timeBound {w control heapLimit : Nat} {array : ArrayRef w}
    {offset count : Word w} {xs : List (Word w)} (hw : 0 < w)
    (fit : array.base.toNat + xs.length < 2 ^ w)
    (span : offset.toNat + count.toNat ≤ array.length.toNat) :
    FunctionTimeBound control functions.program heapLimit 1 functions.function.sumSlice
      (fun args entry => args = functions.arguments.sumSlice array offset count ∧
        array.Rep heapLimit xs entry)
      (fun _ _ => 18 * count.toNat + 119) := by
  ram_time_vc args entry ⟨rfl, represented⟩ [functions.body_eq.sumSlice]
  have sliceCorrect := slice_contract (heapLimit := heapLimit) (depth := 0) (xs := xs) span
  apply FunctionTimeBound.call_seq_at slice_timeBound
    (sliceCorrect.raw (array, offset, count))
    (nextBound := fun _ _ => 18 * count.toNat + 66)
  · exact functions.function_lookup.slice
  · simp [Expr.ReadsBelow]
  · refine ⟨?_, rfl, represented.enter _⟩
    ram_simp [functions.arguments.slice, functions.arguments.sumSlice, Source.State.enter]
  · rintro fields middle ⟨window, rfl, rfl, sliceRep, rfl⟩ _
    have sliceFit := represented.subslice_end_lt offset count span fit
    have sumCorrect := sum_function_contract_of_ref
      (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0) hw sliceFit
    have sumTime := (sum_function_timeBound_of_ref
      (control := control) (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
      hw sliceFit).renameCalls functions.embeds.Sum sumCorrect
    ram_time_call sumTime [functions.function_lookup.Sum.sum, ArrayRef.subslice, ArrayRef.args,
      sliceRep, sliceRep.1.symm, sumFunctions.result_eq.sum,
      functions.arguments.sumSlice, Source.State.enter, DSL.ValueKind.encode,
      Source.State.setRegs_cons, Source.State.setRegs_nil]
    all_goals simpa only [ArrayRef.subslice] using sliceRep
  · intro fields middle _ _
    ram_bound [functions.result_eq.slice, functions.locals_eq.slice]

/-- The same compiled invocation additionally charges its outer call, return
and halt. The slice list and the proposed bound are not runtime arguments. -/
theorem runTotal_steps_le {array : ArrayRef 32} {offset count : Word 32}
    {heapLimit : Nat} {entry : Source.State 32} {xs : List (Word 32)}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (span : offset.toNat + count.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    (functions.runTotal.sumSlice array offset count heapLimit entry
      (sumSlice_halts ⟨xs, represented, fit⟩ span hstack)).steps ≤ 18 * count.toNat + 189 := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) fit span (array, offset, count) entry
      ⟨rfl, represented⟩
  have bounded := by
    ram_run_apply (LocalCompiler.Function.runTotal_steps_le_of_timeBound
      (sumSlice_halts ⟨xs, represented, fit⟩ span hstack) (execution := execution)
      (time := function_timeBound (by decide : 0 < 32) fit span) (pre := ⟨rfl, represented⟩))
      [functions.function_lookup.sumSlice]
    exact hstack
  have callCount : LocalCompiler.Function.callSteps functions.registers
      functions.function.sumSlice (18 * count.toNat + 119) + 1 = 18 * count.toNat + 189 := by
    ram_simp [LocalCompiler.Function.callSteps_eq, functions.result_eq.sumSlice]
  simpa only [functions.runTotal.sumSlice, callCount] using bounded

-- This host state preloads 1, 2, 3, 4, 5. The call selects the middle three
-- elements; its reported count excludes this host-side preparation.
#eval (functions.run.sumSlice (⟨0, 5⟩ : ArrayRef 32) 1 3 5
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }).map
    fun result => ((result.state.regs 0).toNat, result.steps, result.reason)

end Ram.Examples.ArraySlice
