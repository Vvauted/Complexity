/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.Function
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
      (fun _ _ => 37 * xs.length + 107) := by
  rintro args entry ⟨rfl, sourceArray, destinationArray⟩ steps value finish
    ⟨_, _, callee, body, _, _, _⟩
  let entered := entry.enter (functions.arguments.copyThenSum source destination)
  let copyArgs : List Expr :=
    [.var functions.localReg.copyThenSum.source.base,
      .var functions.localReg.copyThenSum.destination.base,
      .var functions.localReg.copyThenSum.source.length]
  let sumArgs : List Expr :=
    [.var functions.localReg.copyThenSum.destination.base,
      .var functions.localReg.copyThenSum.destination.length]
  let next : Source.State w → Prop := fun middle =>
    ArrayAt heapLimit destination.base xs middle ∧
      middle.regs functions.localReg.copyThenSum.destination.base = destination.base ∧
      middle.regs functions.localReg.copyThenSum.destination.length = destination.length
  have copyCorrect := copy_function_contract
    (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint
  have copyTime := (copy_function_timeBound
    (control := control) (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint).renameCalls functions.embeds.Copy copyCorrect
  have importedCopy := copyCorrect.renameCalls functions.embeds.Copy
  have copyPre : copyArgs.map entered.eval = copyFunctions.arguments.copy source.base
      destination.base (BitVec.ofNat w xs.length) ∧
      ArrayAt heapLimit source.base xs entered ∧
      ArrayAt heapLimit destination.base ys entered := by
    refine ⟨?_, sourceArray.2, destinationArray.2⟩
    simp [copyArgs, entered, Source.State.eval, Expr.eval, Source.State.enter,
      functions.arguments.copyThenSum, copyFunctions.arguments.copy, sourceArray.length_eq]
  have firstTime := copyTime.call (dst := functions.localReg.copyThenSum.copied)
    (args := copyArgs) (R := fun s => s = entered) functions.function_lookup.Copy.copy
    (by rintro s rfl; exact copyPre)
  have firstCorrect := importedCopy.wp_call
    (dst := functions.localReg.copyThenSum.copied) (exprs := copyArgs)
    (post := next) functions.function_lookup.Copy.copy
    (by simp [copyArgs, Expr.ReadsBelow]) copyPre (by decide : 0 + 1 ≤ 1)
    (by
      rintro returned middle ⟨rfl, _, destinationCopied, _⟩ registers
      refine ⟨destinationCopied.setReg _ _, ?_, ?_⟩
      · rw [Source.State.setReg_ne _ _ _ _ (by decide), registers]
        rfl
      · rw [Source.State.setReg_ne _ _ _ _ (by decide), registers]
        rfl)
  have destinationLength : destination.length = BitVec.ofNat w xs.length := by
    rw [destinationArray.length_eq, sameLength]
  have sumCorrect := sum_function_contract
    (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
    (base := destination.base) (xs := xs) hw fit
  have sumTime := (sum_function_timeBound
    (control := control) (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
    (base := destination.base) (xs := xs) hw fit).renameCalls functions.embeds.Sum sumCorrect
  have secondTime := sumTime.call (dst := functions.localReg.copyThenSum.answer)
    (args := sumArgs) (R := next) functions.function_lookup.Sum.sum (by
      intro middle hnext
      refine ⟨?_, hnext.1⟩
      simp only [sumArgs, List.map_cons, List.map_nil, Source.State.eval, Expr.eval,
        hnext.2.1, hnext.2.2, destinationLength, sumFunctions.arguments.sum])
  rw [functions.body_eq.copyThenSum] at body
  cases body with
  | seq first second =>
      have firstBound := firstTime _ rfl _ _ first
      obtain ⟨middle, copied, nextPre⟩ := firstCorrect
      have same := copied.deterministic first.erase
      subst middle
      have secondBound := secondTime _ nextPre _ _ second
      dsimp only at firstBound secondBound
      rw [ABI.callLocals_steps_eq] at firstBound secondBound
      change _ ≤ 3 + (19 * xs.length + 2) + 1 + 7 * 3 + 3 + 11 at firstBound
      change _ ≤ 2 + (18 * xs.length + 8) + 1 + 7 * 6 + 2 + 11 at secondBound
      change _ ≤ 37 * xs.length + 107
      omega

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
      (halts safe hstack)).steps ≤ 37 * xs.length + 170 := by
  have fit : destination.base.toNat + xs.length < 2 ^ 32 := by
    have within := destinationArray.2.2
    omega
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) sameLength fit disjoint _ entry
      ⟨rfl, sourceArray, destinationArray⟩
  have bounded := LocalCompiler.Function.runTotal_steps_le_of_timeBound (halts safe hstack)
    compile_copyThenSum functions.function_lookup.copyThenSum code_length_lt hstack execution
    (function_timeBound (by decide : 0 < 32) sameLength fit disjoint)
    ⟨rfl, sourceArray, destinationArray⟩
  have callCount : LocalCompiler.Function.callSteps functions.registers
      functions.function.copyThenSum (37 * xs.length + 107) + 1 = 37 * xs.length + 170 := by
    rw [LocalCompiler.Function.callSteps_eq]
    change 37 * xs.length + 107 + 2 * 4 + 1 + 7 * 6 + 11 + 1 = 37 * xs.length + 170
    omega
  simpa only [functions.runTotal.copyThenSum, callCount] using bounded

end Ram.Examples.FunctionComposition
