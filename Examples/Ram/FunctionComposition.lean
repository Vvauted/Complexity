/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Function
import Complexity.Computability.Ram.Array.Model
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Source.Function.Linking
import Complexity.Computability.Ram.Compiler.Local.Function.Total

/-!
# Composing imported functions in one executable source

`functions` imports the existing copy and sum implementations and calls them
from a new function. Copy is called for its shared-memory effect, without a
dummy source binding for its return value. No callee body is duplicated. The
copy's mathematical postcondition supplies the destination representation needed
by sum, and their previously proved contracts are transported through the
generated embeddings.

This is one compiled RAM invocation, not two host-level runner calls. The
arrays are preloaded and disjoint; allocation and loading are not implemented
here. Correctness and termination do not depend on a proposed execution bound.
-/

namespace Ram.Examples.FunctionComposition

open Source Source.Array

/-- Copy an existing array and sum the destination through imported functions. -/
ram_def functions := ram_functions% {
  include copyFunctions as Copy;
  include sumFunctions as Sum;
  fn copyThenSum(source : array, destination : array) {
    call Copy.copy(source.base, destination.base, source.length);
    let answer ← call Sum.sum(destination);
    return answer;
  }
}

/-- Mathematical contents and framing describe the effect of the composed
implementation. No register index, stack layout or callee loop enters this proof. -/
theorem function_contract {w heapLimit : Nat} {source destination : ArrayRef w}
    {xs ys : List (Word w)} (hw : 0 < w) (sameLength : ys.length = xs.length)
    (fit : destination.base.toNat + xs.length < 2 ^ w)
    (disjoint : ArraysDisjoint source.base xs.length destination.base xs.length) :
    FunctionContract functions.program heapLimit 1 functions.function.copyThenSum
      (fun args entry => args = functions.arguments.copyThenSum source destination ∧
        source.Rep heapLimit xs entry ∧ destination.Rep heapLimit ys entry)
      (fun _ entry value finish => value = wordSum xs ∧
        ArrayAt heapLimit source.base xs finish ∧
        ArrayAt heapLimit destination.base xs finish ∧
        ArrayFrame destination.base xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  ram_total_vc args entry ⟨rfl, sourceArray, destinationArray⟩
    [functions.body_eq.copyThenSum, functions.result_eq.copyThenSum]
  have copyContract := (copy_function_contract
    (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
    hw sameLength sourceArray.length_lt disjoint).renameCalls functions.embeds.Copy
  ram_total_apply copyContract
    [functions.function_lookup.Copy.copy, sourceArray.length_eq,
      sourceArray.2, destinationArray.2]
  · exact ⟨sourceArray.2, destinationArray.2⟩
  · rintro value middle rfl sourceCopied destinationCopied frame input output registers
    have destinationRep : destination.Rep heapLimit xs middle :=
      ⟨destinationArray.1.trans sameLength, destinationCopied⟩
    have sumContract := (sum_function_contract_of_ref
      (program := sumFunctions.program) (heapLimit := heapLimit) (depth := 0)
      (array := destination) (xs := xs) hw fit).renameCalls functions.embeds.Sum
    ram_total_apply sumContract
      [functions.function_lookup.Sum.sum, destinationRep, registers]
    all_goals ram_simp [sourceCopied, destinationCopied, frame, input, output]
    exact ⟨sourceCopied, destinationCopied⟩

/-- The same compiled composition admits an ordinary mathematical return
equation, while retaining the actual copied shared state. -/
theorem eval_eq {w heapLimit : Nat} {source destination : ArrayRef w}
    {xs ys : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (sameLength : ys.length = xs.length)
    (fit : destination.base.toNat + xs.length < 2 ^ w)
    (disjoint : ArraysDisjoint source.base xs.length destination.base xs.length)
    (sourceArray : source.Rep heapLimit xs entry)
    (destinationArray : destination.Rep heapLimit ys entry) :
    ∃ finish, functions.eval.copyThenSum source destination heapLimit entry =
      Part.some (wordSum xs, finish) ∧
      arrayContents finish.mem destination.base xs.length = xs := by
  obtain ⟨value, finish, execution, rfl, _, copied, _⟩ :=
    function_contract hw sameLength fit disjoint _ entry ⟨rfl, sourceArray, destinationArray⟩
  exact ⟨finish, execution.eval_eq_some, copied.1.contents_eq⟩

/-- An imported function's own calls are relocated as well. The original
two-array theorem transfers without reopening either sum call or its loop. -/
theorem imported_sumPair_eval {w heapLimit : Nat} {left right : ArrayRef w}
    {xs ys : List (Word w)} {entry : Source.State w} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (leftArray : left.Rep heapLimit xs entry) (rightArray : right.Rep heapLimit ys entry) :
    functions.eval.Sum.sumPair left right heapLimit entry =
      Part.some (wordSum (xs ++ ys), entry) := by
  rw [wordSum_append]
  have original := sumPair_function_runs (depth := 0) hw leftFit rightFit entry leftArray rightArray
  exact (original.renameCalls functions.embeds.Sum).eval_eq_some

/-- Existing disjoint arrays with matching lengths. Their contents are logical
witnesses, not arguments used to execute the source program. -/
def Safe (source destination : ArrayRef 32) (heapLimit : Nat)
    (entry : Source.State 32) : Prop :=
  ∃ xs ys, ys.length = xs.length ∧ source.Rep heapLimit xs entry ∧
    destination.Rep heapLimit ys entry ∧
    ArraysDisjoint source.base xs.length destination.base xs.length

/-- Fixed code for the imported functions and the new composed call. -/
def code : Code :=
  LocalCompiler.rawLink functions.registers functions.program
    (LocalCompiler.Function.trampoline functions.functionIndex.copyThenSum
      functions.function.copyThenSum.params)

theorem compile_copyThenSum :
    LocalCompiler.Function.compile functions.registers functions.program
      functions.functionIndex.copyThenSum functions.function.copyThenSum.params = some code := by
  set_option maxRecDepth 4096 in decide

theorem code_length_lt : code.length < 2 ^ 32 := by
  set_option maxRecDepth 4096 in decide

variable {source destination : ArrayRef 32} {heapLimit : Nat} {entry : Source.State 32}

/-- Correctness of the source composition supplies normal termination of its
compiled invocation. This proof does not use the independent time bound. -/
theorem halts (safe : Safe source destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts functions.registers functions.program
      functions.functionIndex.copyThenSum functions.function.copyThenSum.params heapLimit
      (functions.arguments.copyThenSum source destination) entry := by
  obtain ⟨xs, ys, sameLength, sourceArray, destinationArray, disjoint⟩ := safe
  have fit : destination.base.toNat + xs.length < 2 ^ 32 := by
    have within := destinationArray.2.2
    omega
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (by decide : 0 < 32) sameLength fit disjoint _ entry
      ⟨rfl, sourceArray, destinationArray⟩
  exact LocalCompiler.Function.halts_of_execution compile_copyThenSum
    functions.function_lookup.copyThenSum code_length_lt hstack execution

/-- Ordinary execution returns both the computed sum and the copied shared
state from one compiled call. All proof arguments are erased at runtime. -/
def copyThenSum (source destination : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32)
    (safe : Safe source destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    Word 32 × Source.State 32 :=
  functions.applyState.copyThenSum source destination heapLimit entry (halts safe hstack)

/-- A mathematical postcondition of the actual executable result: the scalar
is the list sum and the destination contains the copied list. -/
theorem copyThenSum_spec (safe : Safe source destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (sameLength : ys.length = xs.length)
    (sourceArray : source.Rep heapLimit xs entry)
    (destinationArray : destination.Rep heapLimit ys entry)
    (disjoint : ArraysDisjoint source.base xs.length destination.base xs.length) :
    let result := copyThenSum source destination heapLimit entry safe hstack
    result.1.toNat = (xs.map BitVec.toNat).sum % 2 ^ 32 ∧
      arrayContents result.2.mem destination.base xs.length = xs ∧
      ArrayFrame destination.base xs.length entry.mem result.2.mem ∧
      result.2.input = entry.input ∧ result.2.outputRev = entry.outputRev := by
  have fit : destination.base.toNat + xs.length < 2 ^ 32 := by
    have within := destinationArray.2.2
    omega
  have post := LocalCompiler.Function.applyState_spec (halts safe hstack)
    compile_copyThenSum functions.function_lookup.copyThenSum code_length_lt hstack
    (function_contract (by decide : 0 < 32) sameLength fit disjoint)
    ⟨rfl, sourceArray, destinationArray⟩
  refine ⟨?_, post.2.2.1.1.contents_eq, post.2.2.2⟩
  change (LocalCompiler.Function.applyState functions.registers _ _ _ _ _ _ _).1.toNat = _
  exact (congrArg BitVec.toNat post.1).trans (wordSum_toNat xs)

-- Runtime data is explicitly preloaded; the function itself performs the copy.
private def sampleState : Source.State 32 :=
  { Source.State.initial [] with
    mem := fun address => if address.toNat < 3 then BitVec.ofNat 32 (address.toNat + 1) else 0 }

#eval (functions.run.copyThenSum
  (⟨0, 3⟩ : ArrayRef 32) ⟨3, 3⟩ 6 sampleState).map fun result =>
    ((result.state.regs 0).toNat, result.steps, result.reason,
      (arrayContents result.state.mem 3 3).map BitVec.toNat)

end Ram.Examples.FunctionComposition
