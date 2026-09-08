/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Basic
import Complexity.Computability.Ram.Source.Named.Declaration

/-!
# Callable merge on represented arrays

`mergeFunctions` gives the existing merge loop a function declaration, then
provides a typed three-array entry point through a real source call. Both
functions return `Unit`; their result is the destination's actual contents.
Correctness reuses the loop's budget-free contract, not another implementation
or a new loop invariant.

The two source references may alias. The preallocated destination must be
disjoint from each source and have exactly the combined length. Sortedness is
not required to describe the result as standard `List.merge`. The raw core
retains separate word-sized counts without requiring their sum to fit a word.
-/

namespace Ram.Source.Array.Merge

/-- Ordinary source merge followed by a typed array-reference calling interface.
The wrapper passes existing reference fields; it does not load or allocate arrays. -/
ram_def mergeFunctions := ram_functions% {
  fn mergeCore(left, right, destination, leftRemaining, rightRemaining) : Unit {
    while leftRemaining ||| rightRemaining {
      if leftRemaining {
        if rightRemaining {
          if load[left] <= load[right] {
            store[destination] := load[left];
            left := left + 1;
            destination := destination + 1;
            leftRemaining := leftRemaining - 1;
          } else {
            store[destination] := load[right];
            right := right + 1;
            destination := destination + 1;
            rightRemaining := rightRemaining - 1;
          }
        } else {
          store[destination] := load[left];
          left := left + 1;
          destination := destination + 1;
          leftRemaining := leftRemaining - 1;
        }
      } else {
        store[destination] := load[right];
        right := right + 1;
        destination := destination + 1;
        rightRemaining := rightRemaining - 1;
      }
    }
    return;
  }
  fn merge(left : array, right : array, destination : array) : Unit {
    call mergeCore(left.base, right.base, destination.base, left.length, right.length);
    return;
  }
}

/-- The declared core is exactly the existing verified loop. -/
theorem core_body : mergeFunctions.function.mergeCore.body = program := rfl

/-- Bind the five actual core arguments once for both correctness and separate
time proofs. The two counts need only be individually word-representable. -/
theorem core_pre {heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry : State w}
    (hleftFit : xs.length < 2 ^ w) (hrightFit : ys.length < 2 ^ w)
    (leftArray : ArrayAt heapLimit left xs entry)
    (rightArray : ArrayAt heapLimit right ys entry)
    (destinationArray : ArrayAt heapLimit destination scratch entry) :
    Pre heapLimit left right destination xs ys scratch
      (entry.enter (mergeFunctions.arguments.mergeCore left right destination
        (BitVec.ofNat w xs.length) (BitVec.ofNat w ys.length))) := by
  refine ⟨leftArray, rightArray, destinationArray, rfl, rfl, rfl, ?_, ?_⟩
  · exact Word.ofNat_toNat_of_lt hleftFit
  · exact Word.ofNat_toNat_of_lt hrightFit

/-- Invoke the existing merge loop without an I/O driver or a dummy return
word. The destination is disjoint from each source; the sources may alias.
Sortedness and word-representability of the combined length are not required. -/
theorem core_function_contract {w heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)}
    (hw : 0 < w) (hleftFit : xs.length < 2 ^ w) (hrightFit : ys.length < 2 ^ w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length) :
    FunctionContract functions heapLimit depth mergeFunctions.function.mergeCore
      (fun args entry =>
        args = mergeFunctions.arguments.mergeCore left right destination
          (BitVec.ofNat w xs.length) (BitVec.ofNat w ys.length) ∧
        ArrayAt heapLimit left xs entry ∧ ArrayAt heapLimit right ys entry ∧
        ArrayAt heapLimit destination scratch entry)
      (fun _ entry value finish => value = [] ∧
        ArrayAt heapLimit left xs finish ∧ ArrayAt heapLimit right ys finish ∧
        ArrayAt heapLimit destination (unsignedMerge xs ys) finish ∧
        ArrayFrame destination (xs.length + ys.length) entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  apply FunctionContract.of_body
    (R := Pre heapLimit left right destination xs ys scratch)
    (S := Post heapLimit left right destination xs ys)
  · intro entered pre
    obtain ⟨callee, execution, result⟩ :=
      total_contract (functions := functions) (depth := depth) hw hlen hdl hdr entered pre
    exact ⟨callee, execution, by simp [mergeFunctions.result_eq.mergeCore], result⟩
  · rintro args entry ⟨rfl, _, _, _⟩
    exact mergeFunctions.arguments_length.mergeCore left right destination
      (BitVec.ofNat w xs.length) (BitVec.ofNat w ys.length)
  · decide
  · rintro args entry ⟨rfl, leftArray, rightArray, destinationArray⟩
    exact core_pre hleftFit hrightFit leftArray rightArray destinationArray
  · intro args entry pre callee result
    exact ⟨rfl, result.left_array, result.right_array, result.destination_array,
      result.frame, result.input, result.output⟩

/-- Merge through three typed references using a real call to the verified core.
The references denote existing storage, and the returned unit carries no dummy
word. The merged destination and unchanged sources are ordinary list properties. -/
theorem function_contract {w heapLimit : Nat} {left right destination : ArrayRef w}
    {xs ys scratch : List (Word w)} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination.base (xs.length + ys.length) left.base xs.length)
    (hdr : ArraysDisjoint destination.base (xs.length + ys.length) right.base ys.length) :
    TypedFunctionContract mergeFunctions.program heapLimit 1 mergeFunctions.function.merge .unit
      (fun input : ArrayRef w × ArrayRef w × ArrayRef w =>
        mergeFunctions.arguments.merge input.1 input.2.1 input.2.2)
      (fun input entry => input = (left, right, destination) ∧
        left.Rep heapLimit xs entry ∧ right.Rep heapLimit ys entry ∧
        destination.Rep heapLimit scratch entry)
      (fun _ entry _ finish =>
        left.Rep heapLimit xs finish ∧ right.Rep heapLimit ys finish ∧
        destination.Rep heapLimit (unsignedMerge xs ys) finish ∧
        ArrayFrame destination.base (xs.length + ys.length) entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  ram_total_vc input entry ⟨rfl, leftArray, rightArray, destinationArray⟩
    [mergeFunctions.body_eq.merge, mergeFunctions.result_eq.merge]
  have core := core_function_contract (functions := mergeFunctions.program)
    (heapLimit := heapLimit) (depth := 0)
    hw leftArray.length_lt rightArray.length_lt hlen hdl hdr
  ram_total_apply core [leftArray.length_eq, rightArray.length_eq]
  · exact ⟨leftArray.2, rightArray.2, destinationArray.2⟩
  · rintro value finish rfl leftDone rightDone destinationDone frame input output _
    refine ⟨⟨leftArray.1, leftDone⟩, ⟨rightArray.1, rightDone⟩,
      ⟨?_, destinationDone⟩, frame, input, output⟩
    simpa only [length_unsignedMerge, ← hlen] using destinationArray.1

end Ram.Source.Array.Merge
