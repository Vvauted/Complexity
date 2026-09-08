/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contents
import Complexity.Computability.Ram.Array.MergeSort.Ordering
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Array.TwoBuffer

/-!
# Heap representations between recursive sorting calls

The two input references describe an existing source and an equally sized,
disjoint scratch allocation. Splitting borrows ordinary `take`/`drop` views;
it performs no allocation or copying. After a recursive call, the shared
two-buffer rules reassemble the transformed source and retain its enclosing
frame. Scratch contents are refreshed as a mathematical witness, not assumed
unchanged.

These lemmas mention neither registers nor return fields. They are heap facts
for actual call continuations, independent of termination and instruction counts.
The split is any contained word-sized offset, including empty endpoint views.
-/

namespace Ram.Source.Array.MergeSort.Stages

/-- The source and scratch views passed to the two recursive calls. Each pair
has equal extents and remains disjoint; the right length is the actual word
subtraction used by the source program. -/
theorem split_arrays {heapLimit : Nat} {array scratch : ArrayRef w}
    {xs workspace : List (Word w)} {s : State w}
    (sourceArray : array.Rep heapLimit xs s)
    (scratchArray : scratch.Rep heapLimit workspace s)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length)
    (k : Word w) (hk : k.toNat ≤ xs.length) :
    ((array.subslice 0 k).Rep heapLimit (xs.take k.toNat) s ∧
      (scratch.subslice 0 k).Rep heapLimit (workspace.take k.toNat) s ∧
      (workspace.take k.toNat).length = (xs.take k.toNat).length ∧
      ArraysDisjoint (array.subslice 0 k).base (xs.take k.toNat).length
        (scratch.subslice 0 k).base (xs.take k.toNat).length) ∧
    ((array.subslice k (array.length - k)).Rep heapLimit (xs.drop k.toNat) s ∧
      (scratch.subslice k (array.length - k)).Rep heapLimit (workspace.drop k.toNat) s ∧
      (workspace.drop k.toNat).length = (xs.drop k.toNat).length ∧
      ArraysDisjoint (array.subslice k (array.length - k)).base (xs.drop k.toNat).length
        (scratch.subslice k (array.length - k)).base (xs.drop k.toNat).length) := by
  have hkw : k.toNat ≤ workspace.length := by omega
  have rightLength : (array.length - k).toNat = xs.length - k.toNat := by
    change (BinOp.eval .sub array.length k).toNat = _
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [sourceArray.1]; exact hk), sourceArray.1]
  have wholeDisjoint : ArraysDisjoint array.base xs.length scratch.base workspace.length := by
    simpa only [hlen] using disjoint
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa using sourceArray.subslice 0 k (by simpa [sourceArray.1] using hk)
  · simpa using scratchArray.subslice 0 k (by simpa [scratchArray.1] using hkw)
  · simp only [List.length_take, hlen]
  · have splitDisjoint := ArraysDisjoint.slices sourceArray.2.1 scratchArray.2.1
      (firstOffset := 0) (firstLen := k.toNat) (secondOffset := 0) (secondLen := k.toNat)
      (by omega) (by omega) wholeDisjoint
    simpa [ArrayRef.subslice, arrayAddr, List.length_take_of_le hk] using splitDisjoint
  · have view := sourceArray.subslice k (array.length - k)
      (by rw [sourceArray.1, rightLength]; omega)
    simpa only [rightLength, ← List.length_drop, List.take_length] using view
  · have view := scratchArray.subslice k (array.length - k)
      (by rw [scratchArray.1, rightLength, hlen]; omega)
    simpa only [rightLength, ← hlen, ← List.length_drop, List.take_length] using view
  · simp only [List.length_drop, hlen]
  · have splitDisjoint := ArraysDisjoint.slices sourceArray.2.1 scratchArray.2.1
      (firstOffset := k.toNat) (firstLen := (xs.drop k.toNat).length)
      (secondOffset := k.toNat) (secondLen := (xs.drop k.toNat).length)
      (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega) wholeDisjoint
    simpa [ArrayRef.subslice, arrayAddr] using splitDisjoint

/-- A completed recursive prefix call replaces only that source half and its
scratch view. Its postcondition reassembles the whole source and supplies a
whole-allocation frame; the scratch reference still has some actual contents. -/
theorem after_left {heapLimit : Nat} {array scratch : ArrayRef w}
    {xs workspace : List (Word w)} {entry finish : State w}
    (sourceArray : array.Rep heapLimit xs entry)
    (scratchArray : scratch.Rep heapLimit workspace entry)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length)
    (k : Word w) (hk : k.toNat ≤ xs.length)
    (updated : (array.subslice 0 k).Rep heapLimit (sorted (xs.take k.toNat)) finish)
    (frame : TwoBufferFrame (array.subslice 0 k).base (xs.take k.toNat).length
      (scratch.subslice 0 k).base (xs.take k.toNat).length entry.mem finish.mem) :
    array.Rep heapLimit (sorted (xs.take k.toNat) ++ xs.drop k.toNat) finish ∧
      (∃ now, scratch.Rep heapLimit now finish) ∧
      TwoBufferFrame array.base xs.length scratch.base xs.length entry.mem finish.mem := by
  have takeLength : (xs.take k.toNat).length = k.toNat := List.length_take_of_le hk
  have wholeLength : (sorted (xs.take k.toNat) ++ xs.drop k.toNat).length = xs.length := by
    rw [List.length_append, length_sorted, takeLength, List.length_drop]
    omega
  have wholeDisjoint : ArraysDisjoint array.base xs.length scratch.base workspace.length := by
    simpa only [hlen] using disjoint
  have sourceDone : ArrayAt heapLimit array.base
      (sorted (xs.take k.toNat) ++ xs.drop k.toNat) finish :=
    sourceArray.2.reassemble_prefix_of_frame_two (scratchOffset := 0) (scratchLen := k.toNat)
      scratchArray.2.1 wholeDisjoint hk (by omega)
      (by rw [length_sorted, takeLength])
      (by simpa [ArrayRef.subslice] using updated.2)
      (by simpa [ArrayRef.subslice, arrayAddr, takeLength] using frame)
  refine ⟨⟨sourceArray.1.trans wholeLength.symm, sourceDone⟩, ?_, ?_⟩
  · obtain ⟨now, sameLength, represented⟩ := scratchArray.2.exists_contents finish
    exact ⟨now, scratchArray.1.trans sameLength.symm, represented⟩
  · have sliceFrame : TwoBufferFrame (arrayAddr array.base 0) k.toNat
        (arrayAddr scratch.base 0) k.toNat entry.mem finish.mem := by
      simpa [ArrayRef.subslice, arrayAddr, takeLength] using frame
    have outer := TwoBufferFrame.within sourceArray.2.1 scratchArray.2.1
      (by omega : 0 + k.toNat ≤ xs.length)
      (by omega : 0 + k.toNat ≤ workspace.length) sliceFrame
    simpa only [hlen] using outer

/-- A completed recursive suffix call preserves the already sorted prefix.
Reassembly and the enclosing frame use the current source representation,
without recovering any callee locals or depending on its returned value. -/
theorem after_right {heapLimit : Nat} {array scratch : ArrayRef w}
    {xs workspace : List (Word w)} {entry finish : State w}
    (k : Word w) (hk : k.toNat ≤ xs.length)
    (sourceArray : array.Rep heapLimit (sorted (xs.take k.toNat) ++ xs.drop k.toNat) entry)
    (scratchArray : scratch.Rep heapLimit workspace entry)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length)
    (updated : (array.subslice k (array.length - k)).Rep heapLimit
      (sorted (xs.drop k.toNat)) finish)
    (frame : TwoBufferFrame (array.subslice k (array.length - k)).base (xs.drop k.toNat).length
      (scratch.subslice k (array.length - k)).base (xs.drop k.toNat).length
      entry.mem finish.mem) :
    array.Rep heapLimit (sorted (xs.take k.toNat) ++ sorted (xs.drop k.toNat)) finish ∧
      (∃ now, scratch.Rep heapLimit now finish) ∧
      TwoBufferFrame array.base xs.length scratch.base xs.length entry.mem finish.mem := by
  have takeLength : (xs.take k.toNat).length = k.toNat := List.length_take_of_le hk
  have wholeLength : (sorted (xs.take k.toNat) ++ xs.drop k.toNat).length = xs.length := by
    rw [List.length_append, length_sorted, takeLength, List.length_drop]
    omega
  have sortedLength : (sorted (xs.take k.toNat) ++ sorted (xs.drop k.toNat)).length =
      xs.length := by
    simpa only [List.length_append, length_sorted] using wholeLength
  have wholeDisjoint : ArraysDisjoint array.base
      (sorted (xs.take k.toNat) ++ xs.drop k.toNat).length scratch.base workspace.length := by
    simpa only [wholeLength, hlen] using disjoint
  have sliceFrame : TwoBufferFrame (arrayAddr array.base k.toNat) (xs.drop k.toNat).length
      (arrayAddr scratch.base k.toNat) (xs.drop k.toNat).length entry.mem finish.mem := by
    simpa [ArrayRef.subslice, arrayAddr] using frame
  have sourceDone : ArrayAt heapLimit array.base
      (sorted (xs.take k.toNat) ++ sorted (xs.drop k.toNat)) finish := by
    have restored := sourceArray.2.reassemble_suffix_of_frame_two
      (suffix := sorted (xs.drop k.toNat))
      (split := k.toNat) (scratchOffset := k.toNat) (scratchLen := (xs.drop k.toNat).length)
      scratchArray.2.1 wholeDisjoint (by omega) (by rw [List.length_drop]; omega)
      (by simp only [length_sorted, List.length_drop, wholeLength])
      (by simpa [ArrayRef.subslice, arrayAddr] using updated.2)
      (by simpa only [wholeLength, List.length_drop] using sliceFrame)
    simpa only [List.take_left' ((length_sorted (xs.take k.toNat)).trans takeLength)]
      using restored
  refine ⟨⟨sourceArray.1.trans (wholeLength.trans sortedLength.symm), sourceDone⟩, ?_, ?_⟩
  · obtain ⟨now, sameLength, represented⟩ := scratchArray.2.exists_contents finish
    exact ⟨now, scratchArray.1.trans sameLength.symm, represented⟩
  · have outer := TwoBufferFrame.within sourceArray.2.1 scratchArray.2.1
      (by rw [wholeLength, List.length_drop]; omega)
      (by rw [List.length_drop]; omega) sliceFrame
    simpa only [wholeLength, hlen] using outer

/-- Adjacent represented halves supply the typed merge call's actual source
views and its two destination-disjointness obligations. Correctness and time
continuations can share these facts after both recursive calls have finished. -/
theorem merge_arrays {heapLimit : Nat} {array scratch : ArrayRef w}
    {front back workspace : List (Word w)} {s : State w}
    (sourceArray : array.Rep heapLimit (front ++ back) s)
    (scratchArray : scratch.Rep heapLimit workspace s)
    (hlen : workspace.length = front.length + back.length)
    (disjoint : ArraysDisjoint array.base (front.length + back.length)
      scratch.base (front.length + back.length))
    (k : Word w) (hk : k.toNat = front.length) :
    (array.subslice 0 k).Rep heapLimit front s ∧
      (array.subslice k (array.length - k)).Rep heapLimit back s ∧
      ArraysDisjoint scratch.base (front.length + back.length)
        (array.subslice 0 k).base front.length ∧
      ArraysDisjoint scratch.base (front.length + back.length)
        (array.subslice k (array.length - k)).base back.length := by
  have extent : workspace.length = (front ++ back).length := by
    simpa only [List.length_append] using hlen
  have wholeDisjoint : ArraysDisjoint array.base (front ++ back).length
      scratch.base (front ++ back).length := by
    simpa only [List.length_append] using disjoint
  obtain ⟨⟨leftArray, _, _, _⟩, ⟨rightArray, _, _, _⟩⟩ :=
    split_arrays sourceArray scratchArray extent wholeDisjoint k
      (by rw [hk, List.length_append]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hk, List.take_left] using leftArray
  · simpa only [hk, List.drop_left] using rightArray
  · have separated := ArraysDisjoint.slice_right sourceArray.2.1
      (offset := 0) (length := front.length) (by simp only [List.length_append]; omega)
      (by simpa only [List.length_append] using disjoint.symm)
    simpa [ArrayRef.subslice, arrayAddr] using separated
  · have separated := ArraysDisjoint.slice_right sourceArray.2.1
      (offset := k.toNat) (length := back.length)
      (by rw [hk, List.length_append])
      (by simpa only [List.length_append] using disjoint.symm)
    simpa [ArrayRef.subslice, arrayAddr] using separated

end Ram.Source.Array.MergeSort.Stages
