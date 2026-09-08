/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Function
import Complexity.Computability.Ram.Array.Merge.Function
import Complexity.Computability.Ram.Array.MergeSort.Bounds
import Complexity.Computability.Ram.Array.MergeSort.Ordering
import Complexity.Computability.Ram.Array.MergeSort.Stages
import Complexity.Computability.Ram.Array.TwoBuffer
import Complexity.Computability.Ram.Source.Function.Linking

/-!
# Recursive merge sort with typed array arguments

The source declaration recursively sorts two borrowed slices, calls the verified
merge function into preallocated scratch storage, and copies the result back.
All calls are part of one compiled program. The function returns genuine `Unit`;
the sorted contents are observed in its actual shared heap.

Correctness follows ordinary induction on the represented list's length. Its
call-depth capacity allows the nested merge-core call, but contains no proposed
running-time budget. The two arrays must already exist and be disjoint; no
allocation or host-side list loading is implicit.
-/

namespace Ram.Source.Array.MergeSort.Function

/-- Sort an existing array using an equally sized, disjoint scratch reference.
Slice descriptors are ordinary source bindings, not host-side recursive calls. -/
ram_def sortFunctions := ram_functions% {
  include Merge.mergeFunctions as Merge;
  include copyFunctions as Copy;
  fn sort(xs : array, scratch : array) : Unit {
    if 1 < xs.length {
      let middle := xs.length / 2;
      let left : array := subslice(xs, 0, middle);
      let right : array := subslice(xs, middle, xs.length - middle);
      call sort(left, subslice(scratch, 0, middle));
      call sort(right, subslice(scratch, middle, xs.length - middle));
      call Merge.merge(left, right, scratch);
      call Copy.copy(scratch.base, xs.base, xs.length);
    }
    return;
  }
}

/-- Sort the represented source through the declaration's actual recursive
calls. The induction ranges over every pair of array references and every
initial scratch contents, so both borrowed children use the same theorem.
The depth is a safety capacity, not a running-time budget. -/
theorem function_contract {w heapLimit : Nat} {array scratch : ArrayRef w}
    {xs workspace : List (Word w)} (hw : 2 ≤ w)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length) :
    TypedFunctionContract sortFunctions.program heapLimit (Nat.clog 2 xs.length + 1)
      sortFunctions.function.sort .unit
      (fun input : ArrayRef w × ArrayRef w =>
        sortFunctions.arguments.sort input.1 input.2)
      (fun input entry => input = (array, scratch) ∧
        array.Rep heapLimit xs entry ∧ scratch.Rep heapLimit workspace entry)
      (fun _ entry _ finish =>
        array.Rep heapLimit (sorted xs) finish ∧
        (∃ now, scratch.Rep heapLimit now finish) ∧
        TwoBufferFrame array.base xs.length scratch.base xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  have positive : 0 < w := by omega
  have two : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hw))
  induction xs using (measure (fun xs : List (Word w) => xs.length)).wf.induction
      generalizing array scratch workspace with
  | h xs ih =>
    by_cases small : xs.length ≤ 1
    · ram_total_vc input entry ⟨rfl, sourceArray, scratchArray⟩
        [sortFunctions.body_eq.sort, sortFunctions.result_eq.sort,
          BitVec.toNat_one positive, sourceArray.1, show ¬1 < xs.length by omega]
      exact ⟨by simpa only [sorted_eq_self_of_length_le_one small] using sourceArray,
        ⟨workspace, scratchArray⟩, TwoBufferFrame.refl _ _ _ _ _⟩
    · have large : 2 ≤ xs.length := by omega
      ram_total_vc input entry ⟨rfl, sourceArray, scratchArray⟩
        [sortFunctions.body_eq.sort, sortFunctions.result_eq.sort,
          BitVec.toNat_one positive, sourceArray.1,
          show 1 < xs.length by omega, Nat.ne_of_gt positive]
      let k : Word w := array.length / 2
      have half : k.toNat = xs.length / 2 := by
        simp only [k, BitVec.toNat_udiv, sourceArray.1, two]
      have contained : k.toNat ≤ xs.length := by rw [half]; exact Nat.div_le_self _ _
      have takeLength : (xs.take k.toNat).length = k.toNat :=
        List.length_take_of_le contained
      have frontLength : (sorted (xs.take k.toNat)).length = k.toNat := by
        rw [length_sorted, takeLength]
      have leftShorter : (xs.take k.toNat).length < xs.length := by
        rw [takeLength, half]
        omega
      have rightShorter : (xs.drop k.toNat).length < xs.length := by
        rw [List.length_drop, half]
        omega
      have leftDepth : Nat.clog 2 (xs.take k.toNat).length + 2 ≤
          Nat.clog 2 xs.length + 1 := by
        have bound := Bounds.depth_left large
        simp only [Bounds.depth] at bound
        rw [takeLength, half]
        omega
      have rightDepth : Nat.clog 2 (xs.drop k.toNat).length + 2 ≤
          Nat.clog 2 xs.length + 1 := by
        have bound := Bounds.depth_right large
        simp only [Bounds.depth] at bound
        rw [List.length_drop, half]
        omega
      obtain ⟨⟨leftSource, leftScratch, leftLength, leftDisjoint⟩, _⟩ :=
        Stages.split_arrays sourceArray scratchArray hlen disjoint k contained
      have leftCorrect := ih (xs.take k.toNat) leftShorter leftLength leftDisjoint
      ram_total_apply (leftCorrect.wp_call_restored
        (arg := (array.subslice 0 k, scratch.subslice 0 k))) [ArrayRef.subslice]
      · simpa [ArrayRef.subslice, k] using And.intro leftSource leftScratch
      · have bound : Nat.clog 2 (xs.take k.toNat).length < Nat.clog 2 xs.length := by omega
        simpa [k] using bound
      · rintro _ afterLeft leftSorted _ _ leftFrame leftInput leftOutput
        obtain ⟨sourceAfterLeft, ⟨leftWorkspace, scratchAfterLeft⟩, frameAfterLeft⟩ :=
          Stages.after_left sourceArray scratchArray hlen disjoint k contained
            (by simpa [ArrayRef.subslice, k] using leftSorted)
            (by simpa [ArrayRef.subslice, k] using leftFrame)
        have leftWholeLength : (sorted (xs.take k.toNat) ++ xs.drop k.toNat).length =
            xs.length := by
          rw [List.length_append, frontLength, List.length_drop]
          omega
        have leftWorkspaceLength : leftWorkspace.length = xs.length :=
          scratchAfterLeft.1.symm.trans (scratchArray.1.trans hlen)
        have rightViews := (Stages.split_arrays sourceAfterLeft scratchAfterLeft
          (leftWorkspaceLength.trans leftWholeLength.symm)
          (by simpa only [leftWholeLength] using disjoint) k
          (by simpa only [leftWholeLength] using contained)).2
        simp only [List.drop_left' frontLength] at rightViews
        obtain ⟨rightSource, rightScratch, rightLength, rightDisjoint⟩ := rightViews
        have rightCorrect := ih (xs.drop k.toNat) rightShorter rightLength rightDisjoint
        ram_total_apply (rightCorrect.wp_call_restored
          (arg := (array.subslice k (array.length - k),
            scratch.subslice k (array.length - k))))
          [ArrayRef.subslice]
        · simpa [ArrayRef.subslice, k] using And.intro rightSource rightScratch
        · have bound : Nat.clog 2 (xs.drop k.toNat).length < Nat.clog 2 xs.length := by omega
          simpa [k] using bound
        · rintro _ afterRight rightSorted _ _ rightFrame rightInput rightOutput
          obtain ⟨sourceAfterRight, ⟨rightWorkspace, scratchAfterRight⟩, frameAfterRight⟩ :=
            Stages.after_right k contained sourceAfterLeft scratchAfterLeft
              leftWorkspaceLength disjoint
              (by simpa [ArrayRef.subslice, k] using rightSorted)
              (by simpa [ArrayRef.subslice, k] using rightFrame)
          have mergeLength : (sorted (xs.take k.toNat)).length +
              (sorted (xs.drop k.toNat)).length = xs.length := by
            rw [frontLength, length_sorted, List.length_drop]
            omega
          have rightWorkspaceLength : rightWorkspace.length = xs.length :=
            scratchAfterRight.1.symm.trans (scratchArray.1.trans hlen)
          obtain ⟨mergeLeft, mergeRight, mergeLeftDisjoint, mergeRightDisjoint⟩ :=
            Stages.merge_arrays sourceAfterRight scratchAfterRight
              (rightWorkspaceLength.trans mergeLength.symm)
              (by simpa only [mergeLength] using disjoint) k frontLength.symm
          have mergeCorrect := (Merge.function_contract
            (heapLimit := heapLimit) positive
            (rightWorkspaceLength.trans mergeLength.symm) mergeLeftDisjoint mergeRightDisjoint).renameCalls
              sortFunctions.embeds.Merge
          ram_total_apply (mergeCorrect.wp_call_restored
            (arg := (array.subslice 0 k, array.subslice k (array.length - k), scratch)))
            [ArrayRef.subslice, merge_sorted_split, mergeLength]
          · simpa [ArrayRef.subslice] using And.intro mergeLeft (And.intro mergeRight scratchAfterRight)
          · have bound := Bounds.depth_left large
            simp only [Bounds.depth] at bound
            omega
          · rintro _ afterMerge _ _ scratchMerged mergeFrame mergeInput mergeOutput
            have sourceBeforeCopy := sourceAfterRight.2.frame mergeFrame
              (by simpa only [List.length_append, mergeLength] using disjoint.symm)
            have copyCorrect := (copy_function_typed_contract_of_ref
              (program := copyFunctions.program) (heapLimit := heapLimit) (depth := 0)
              (source := scratch) (destination := array)
              (xs := sorted xs) (ys := sorted (xs.take k.toNat) ++ sorted (xs.drop k.toNat))
              positive (by simpa only [List.length_append, length_sorted] using mergeLength)
              (by simpa only [length_sorted] using disjoint.symm)).renameCalls
                sortFunctions.embeds.Copy
            ram_total_apply (copyCorrect.wp_call_restored (arg := (scratch, array)))
              [ArrayRef.subslice, sourceArray.length_eq, scratchMerged.length_eq, length_sorted]
            · exact ⟨scratchMerged, sourceAfterRight.1, sourceBeforeCopy⟩
            · rintro _ finish scratchDone sourceDone copyFrame copyInput copyOutput
              refine ⟨sourceDone, ⟨sorted xs, scratchDone⟩,
                frameAfterLeft.trans (frameAfterRight.trans
                  ((TwoBufferFrame.of_right mergeFrame).trans
                    (TwoBufferFrame.of_left copyFrame))),
                copyInput.trans (mergeInput.trans (rightInput.trans leftInput)),
                copyOutput.trans (mergeOutput.trans (rightOutput.trans leftOutput))⟩

end Ram.Source.Array.MergeSort.Function
