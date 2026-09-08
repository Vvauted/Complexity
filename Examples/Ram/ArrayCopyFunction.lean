/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Function
import Complexity.Computability.Ram.Array.Model
import Complexity.Computability.Ram.Compiler.Local.Function.Total
import Examples.Ram.ArraySum

/-!
# Executable array copy with a reusable returned state

`copy` executes the existing Unit-returning copy function and returns its actual
shared state through `applyState`. Ordinary list equations describe the copied memory;
the logical lists occur only in erased safety proofs, never as runtime arguments.
The implementation does not allocate or load either array.

`copyThenSum` is a host-level composition of two genuine compiled calls: it passes
copy's returned state directly to the existing executable sum function. It is not
a new single compiled RAM program. Host-side preloading and state projection are
not charged as RAM array-conversion instructions, and no whole-program cost is
claimed for this composition. Each original operation retains its separate cost
theorems. The existing raw-block copy example remains independent.
-/

namespace Ram.Examples.ArrayCopyFunction

open Source Source.Array

/-- The existing array assertions provide a safe non-overlapping copy of the
runtime length. No contents or proposed result become executable inputs. -/
def Safe (source destination length : Word 32) (heapLimit : Nat)
    (entry : Source.State 32) : Prop :=
  ∃ xs ys, length.toNat = xs.length ∧ ys.length = xs.length ∧
    ArrayAt heapLimit source xs entry ∧ ArrayAt heapLimit destination ys entry ∧
    ArraysDisjoint source xs.length destination xs.length

private def copyCode : Code :=
  LocalCompiler.rawLink copyFunctions.registers copyFunctions.program
    (LocalCompiler.Function.trampoline copyFunctions.functionIndex.copy
      copyFunctions.function.copy.params copyFunctions.function.copy.results.length)

private theorem compile_copy :
    LocalCompiler.Function.compile copyFunctions.registers copyFunctions.program
      copyFunctions.functionIndex.copy copyFunctions.function.copy.params = some copyCode := by
  set_option maxRecDepth 4096 in decide

private theorem copyCode_length_lt : copyCode.length < 2 ^ 32 := by
  set_option maxRecDepth 4096 in decide

variable {source destination length : Word 32} {heapLimit : Nat} {entry : Source.State 32}

/-- Budget-free copy correctness establishes normal termination of this
compiled call. No measured execution or proposed time bound is needed. -/
theorem copy_halts (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts copyFunctions.registers copyFunctions.program
      copyFunctions.functionIndex.copy copyFunctions.function.copy.params heapLimit
      (copyFunctions.arguments.copy source destination length) entry := by
  obtain ⟨xs, ys, count, sameLength, sourceArray, destinationArray, disjoint⟩ := safe
  have lengthFit : xs.length < 2 ^ 32 := by
    rw [← count]
    exact length.isLt
  have encoded : length = BitVec.ofNat 32 xs.length := by
    rw [← count]
    exact (Word.ofNat_toNat_self length).symm
  obtain ⟨finish, execution, _⟩ := copy_function_runs
    (program := copyFunctions.program) (depth := 0) (by decide : 0 < 32)
    sameLength lengthFit disjoint entry sourceArray destinationArray
  rw [← encoded] at execution
  exact LocalCompiler.Function.halts_of_execution compile_copy copyFunctions.function_lookup.copy
    copyCode_length_lt (by simpa using hstack) execution

/-- Execute the existing compiled copy and return its source-visible state.
The proof is erased, and the destination contents come from actual RAM stores. -/
def copy (source destination length : Word 32) (heapLimit : Nat) (entry : Source.State 32)
    (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32) : Source.State 32 :=
  (copyFunctions.applyState.copy source destination length heapLimit entry
    (copy_halts safe hstack)).2

/-- Typed Unit application retains the actual copied shared state. The empty
value does not replace execution: the destination contents, frame and streams
come from the same compiled invocation. -/
theorem copy_applyState_spec (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (count : length.toNat = xs.length)
    (sameLength : ys.length = xs.length)
    (sourceArray : ArrayAt heapLimit source xs entry)
    (destinationArray : ArrayAt heapLimit destination ys entry)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    let result := copyFunctions.applyState.copy source destination length heapLimit entry
      (copy_halts safe hstack)
    result.1 = () ∧
      ArrayAt heapLimit source xs result.2 ∧ ArrayAt heapLimit destination xs result.2 ∧
      ArrayFrame destination xs.length entry.mem result.2.mem ∧
      result.2.input = entry.input ∧ result.2.outputRev = entry.outputRev := by
  have lengthFit : xs.length < 2 ^ 32 := by
    rw [← count]
    exact length.isLt
  have encoded : length = BitVec.ofNat 32 xs.length := by
    rw [← count]
    exact (Word.ofNat_toNat_self length).symm
  have post := LocalCompiler.Function.applyState_spec (copy_halts safe hstack)
    compile_copy copyFunctions.function_lookup.copy copyCode_length_lt (by simpa using hstack)
    (copy_function_contract (program := copyFunctions.program) (depth := 0)
      (by decide : 0 < 32) sameLength lengthFit disjoint)
    ⟨by rw [encoded], sourceArray, destinationArray⟩
  refine ⟨rfl, ?_⟩
  simpa only [copyFunctions.applyState.copy,
    max_eq_right (by decide : 1 ≤ copyFunctions.registers)] using post.2

/-- The actual returned state contains the copied list at both pointers,
preserves memory outside the destination, and retains both I/O streams. -/
theorem copy_spec (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (count : length.toNat = xs.length)
    (sameLength : ys.length = xs.length)
    (sourceArray : ArrayAt heapLimit source xs entry)
    (destinationArray : ArrayAt heapLimit destination ys entry)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    let finish := copy source destination length heapLimit entry safe hstack
    ArrayAt heapLimit source xs finish ∧ ArrayAt heapLimit destination xs finish ∧
      ArrayFrame destination xs.length entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev :=
  (copy_applyState_spec safe hstack count sameLength sourceArray destinationArray disjoint).2

/-- The ordinary list observation of the actual copied destination equals
the source list. This reuses the existing representation-to-list theorem. -/
theorem copy_contents (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (count : length.toNat = xs.length)
    (sameLength : ys.length = xs.length)
    (sourceArray : ArrayAt heapLimit source xs entry)
    (destinationArray : ArrayAt heapLimit destination ys entry)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    arrayContents (copy source destination length heapLimit entry safe hstack).mem
      destination xs.length = xs :=
  (copy_spec safe hstack count sameLength sourceArray destinationArray disjoint).2.1.1.contents_eq

/-- The existing independent body bound gives a bound for the actual copy
call, including argument setup, return and halt. It is not used by `copy_halts`. -/
theorem runTotal_steps_le (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (count : length.toNat = xs.length)
    (sameLength : ys.length = xs.length)
    (sourceArray : ArrayAt heapLimit source xs entry)
    (destinationArray : ArrayAt heapLimit destination ys entry)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    (copyFunctions.runTotal.copy source destination length heapLimit entry
      (copy_halts safe hstack)).steps ≤ 19 * xs.length + 39 := by
  have lengthFit : xs.length < 2 ^ 32 := by
    rw [← count]
    exact length.isLt
  have encoded : length = BitVec.ofNat 32 xs.length := by
    rw [← count]
    exact (Word.ofNat_toNat_self length).symm
  obtain ⟨finish, execution, _⟩ := copy_function_runs
    (program := copyFunctions.program) (depth := 0) (by decide : 0 < 32)
    sameLength lengthFit disjoint entry sourceArray destinationArray
  rw [← encoded] at execution
  have bounded := LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (copy_halts safe hstack) compile_copy copyFunctions.function_lookup.copy
    copyCode_length_lt (by simpa using hstack) execution
    (copy_function_timeBound (by decide : 0 < 32) sameLength lengthFit disjoint)
    ⟨by rw [encoded], sourceArray, destinationArray⟩
  have callCount : LocalCompiler.Function.callSteps copyFunctions.registers
      copyFunctions.function.copy (19 * xs.length + 2) + 1 = 19 * xs.length + 39 := by
    rw [LocalCompiler.Function.callSteps_eq]
    change 19 * xs.length + 2 + 2 * 3 + 0 + 7 * 3 + 2 * 0 + 9 + 1 =
      19 * xs.length + 39
    omega
  simpa only [copyFunctions.runTotal.copy,
    max_eq_right (by decide : 1 ≤ copyFunctions.registers), callCount] using bounded

private theorem copy_stack_of_sum_stack
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32) :
    heapLimit + ABI.frameSize copyFunctions.registers < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.add_le_add_left (by decide) heapLimit) hstack

/-- Host-level sequencing of two actual compiled applications. Sum reads the
destination from copy's returned state, not the input state or a logical list. -/
def copyThenSum (source destination length : Word 32) (heapLimit : Nat)
    (entry : Source.State 32) (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32) : Nat :=
  let copyStack := copy_stack_of_sum_stack hstack
  let copied := copy source destination length heapLimit entry safe copyStack
  ArraySum.sum ⟨destination, length⟩ heapLimit copied (by
    obtain ⟨xs, ys, count, sameLength, sourceArray, destinationArray, disjoint⟩ := safe
    have post := copy_spec
      ⟨xs, ys, count, sameLength, sourceArray, destinationArray, disjoint⟩
      copyStack count sameLength sourceArray destinationArray disjoint
    refine ⟨xs, ⟨count, post.2.1⟩, ?_⟩
    change destination.toNat + xs.length < 2 ^ 32
    have within := post.2.1.2
    omega) hstack

/-- Ordinary function composition preserves the source list's modular sum.
No loop, RAM register or calling-convention proof is opened in this argument. -/
theorem copyThenSum_eq (safe : Safe source destination length heapLimit entry)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    {xs ys : List (Word 32)} (count : length.toNat = xs.length)
    (sameLength : ys.length = xs.length)
    (sourceArray : ArrayAt heapLimit source xs entry)
    (destinationArray : ArrayAt heapLimit destination ys entry)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    copyThenSum source destination length heapLimit entry safe hstack =
      (xs.map BitVec.toNat).sum % 2 ^ 32 := by
  have post := copy_spec safe (copy_stack_of_sum_stack hstack)
    count sameLength sourceArray destinationArray disjoint
  have fit : destination.toNat + xs.length < 2 ^ 32 := by
    have within := post.2.1.2
    omega
  dsimp only [copyThenSum]
  exact ArraySum.sum_eq fit hstack ⟨count, post.2.1⟩

-- These are explicit host-side preloaded arrays, not an implemented loader.
private def sampleState : Source.State 32 :=
  { Source.State.initial [] with
    mem := fun address => if address.toNat < 3 then BitVec.ofNat 32 (address.toNat + 1) else 0 }

private theorem sample_source : ArrayAt 6 (0 : Word 32) [1, 2, 3] sampleState := by
  refine ⟨⟨by decide, ?_⟩, by decide⟩
  intro i hi
  have indices : i = 0 ∨ i = 1 ∨ i = 2 := by
    change i < 3 at hi
    omega
  rcases indices with rfl | rfl | rfl <;> rfl

private theorem sample_destination : ArrayAt 6 (3 : Word 32) [0, 0, 0] sampleState := by
  refine ⟨⟨by decide, ?_⟩, by decide⟩
  intro i hi
  have indices : i = 0 ∨ i = 1 ∨ i = 2 := by
    change i < 3 at hi
    omega
  rcases indices with rfl | rfl | rfl <;> rfl

private theorem sample_safe : Safe 0 3 3 6 sampleState :=
  ⟨[1, 2, 3], [0, 0, 0], by decide, rfl, sample_source, sample_destination,
    Or.inl (by decide)⟩

-- The destination initially holds zeros. This returns 6 only after the
-- actual stores performed by copy have reached the subsequent sum call.
#eval copyThenSum 0 3 3 6 sampleState sample_safe (by decide)

end Ram.Examples.ArrayCopyFunction
