/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Time
import Complexity.Computability.Ram.Array.MergeSort.Function
import Complexity.Computability.Ram.Verification.Time.Typed
import Complexity.Tactic.Ram.Time

/-!
# Separate time bounds for typed recursive merge sort

The declaration's five assignments and four calls are charged by the same
compiler-derived time rules as their actual executions. Functional contracts
supply the intermediate heap assertions, independently of these bounds.
The induction applies at every sufficient call depth; it does not assume that
a conditional time bound is monotone in a safety capacity.

The balanced reserve covers both unequal children and the whole current toll,
including descriptor arithmetic, argument evaluation, frames and empty returns.
The outer invocation and halt are not included in the function's body bound.
-/

namespace Ram.Source.Array.MergeSort.Function

/-- A balanced supersolution for the actual typed function body. -/
def bodyBudget (n : Nat) : Nat := Recurrence.balancedBudget 4 227 n

/-- Nonrecursive work in a taken branch: guard and jump, five assignments,
two recursive call blocks, and the complete merge and copy invocations.
The call rules below derive these terms from the declared source. -/
def stepToll (n : Nat) : Nat :=
  4 + 1 + 18 + 82 + 84 + (34 * n + 121) + (19 * n + 38)

theorem stepToll_eq (n : Nat) : stepToll n = 53 * n + 348 := by
  simp only [stepToll]
  omega

theorem bodyBudget_small {n : Nat} (hn : n ≤ 1) : bodyBudget n = 4 := by
  have cases : n = 0 ∨ n = 1 := by omega
  rcases cases with rfl | rfl <;> simp [bodyBudget]

/-- The real one-step toll is covered without requiring equal child sizes. -/
theorem bodyBudget_split_cover {n : Nat} (hn : 2 ≤ n) :
    bodyBudget (n / 2) + bodyBudget (n - n / 2) + stepToll n ≤ bodyBudget n := by
  rw [stepToll_eq]
  exact (Nat.add_le_add_left (by omega : 53 * n + 348 ≤ 227 * n) _).trans
    (Recurrence.balancedBudget_split_le 4 227 hn)

set_option maxHeartbeats 400000 in
/-- Every sufficient call-depth capacity admits the same independent body
bound. The induction hypothesis is used at the actual child depth; only the
separate functional contracts are lifted to that depth. -/
theorem function_timeBound_of_depth {w control heapLimit depth : Nat}
    {array scratch : ArrayRef w} {xs workspace : List (Word w)} (hw : 2 ≤ w)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length)
    (capacity : Nat.clog 2 xs.length + 1 ≤ depth) :
    FunctionTimeBound control sortFunctions.program heapLimit depth
      sortFunctions.function.sort
      (fun args entry => args = sortFunctions.arguments.sort array scratch ∧
        array.Rep heapLimit xs entry ∧ scratch.Rep heapLimit workspace entry)
      (fun _ _ => bodyBudget xs.length) := by
  have positive : 0 < w := by omega
  have two : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hw))
  induction xs using (measure (fun xs : List (Word w) => xs.length)).wf.induction
      generalizing array scratch workspace depth with
  | h xs ih =>
    by_cases small : xs.length ≤ 1
    · ram_time_vc args entry ⟨rfl, sourceArray, scratchArray⟩
        [sortFunctions.body_eq.sort]
      have guardZero : (entry.enter (sortFunctions.arguments.sort array scratch)).eval
          (.bin .ult (.const 1) (.var 1)) = 0 := by
        ram_simp [BitVec.toNat_one positive, sourceArray.1,
          show ¬1 < xs.length by omega]
      apply (TimeBound.ite (yesBound := fun _ => 0) (noBound := fun _ => 0)
        ?_ (TimeBound.skip _)).mono_budget
      · rintro state rfl
        ram_bound [guardZero, bodyBudget_small small]
      · rintro state ⟨rfl, nonzero⟩
        exact (nonzero guardZero).elim
    · have large : 2 ≤ xs.length := by omega
      have logPositive : 1 ≤ Nat.clog 2 xs.length := Nat.clog_pos (by decide) (by omega)
      obtain ⟨inner, rfl⟩ : ∃ inner, depth = inner + 2 := ⟨depth - 2, by omega⟩
      ram_time_vc args entry ⟨rfl, sourceArray, scratchArray⟩
        [sortFunctions.body_eq.sort]
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
      have leftDepth : Nat.clog 2 (xs.take k.toNat).length + 1 ≤ inner + 1 := by
        have bound := Bounds.depth_left large
        simp only [Bounds.depth] at bound
        rw [takeLength, half]
        omega
      have rightDepth : Nat.clog 2 (xs.drop k.toNat).length + 1 ≤ inner + 1 := by
        have bound := Bounds.depth_right large
        simp only [Bounds.depth] at bound
        rw [List.length_drop, half]
        omega
      have guardNonzero : (entry.enter (sortFunctions.arguments.sort array scratch)).eval
          (.bin .ult (.const 1) (.var 1)) ≠ 0 := by
        ram_simp [BitVec.toNat_one positive, sourceArray.1,
          show 1 < xs.length by omega, Nat.ne_of_gt positive]
      apply (TimeBound.ite
        (yesBound := fun _ => bodyBudget (xs.take k.toNat).length +
          bodyBudget (xs.drop k.toNat).length + 53 * xs.length + 343)
        (noBound := fun _ => 0) ?_ (TimeBound.skip _)).mono_budget
      · rintro state rfl
        have cover := bodyBudget_split_cover large
        rw [stepToll_eq] at cover
        ram_bound [guardNonzero, takeLength, List.length_drop, half,
          List.length_take_of_le (Nat.div_le_self xs.length 2)]
      · apply TimeBound.consequence
          (P := fun state => state = entry.enter (sortFunctions.arguments.sort array scratch))
          (bound := fun _ => bodyBudget (xs.take k.toNat).length +
            bodyBudget (xs.drop k.toNat).length + 53 * xs.length + 343)
          ?_ (fun _ pre => pre.1) (fun _ _ => Nat.le_refl _)
        ram_time_vc []
        obtain ⟨⟨leftSource, leftScratch, leftLength, leftDisjoint⟩, _⟩ :=
          Stages.split_arrays sourceArray scratchArray hlen disjoint k contained
        have leftTime := ih (xs.take k.toNat) leftShorter leftLength leftDisjoint leftDepth
        have leftCorrect := (function_contract (heapLimit := heapLimit)
          hw leftLength leftDisjoint).mono_depth leftDepth
        ram_time_apply leftCorrect leftTime on
          (array.subslice 0 k, scratch.subslice 0 k) [ArrayRef.subslice, k]
        · exact ⟨rfl, leftSource, leftScratch⟩
        · exact ⟨rfl, leftSource, leftScratch⟩
        · ram_bound [sortFunctions.result_eq.sort, List.length_take, List.length_drop,
            min_eq_left contained]
        · rintro _ afterLeft ⟨leftSorted, _, leftFrame, _, _⟩
          ram_time_vc [sortFunctions.result_eq.sort, List.length_take, List.length_drop,
            min_eq_left contained]
          obtain ⟨sourceAfterLeft, ⟨leftWorkspace, scratchAfterLeft⟩, _⟩ :=
            Stages.after_left sourceArray scratchArray hlen disjoint k contained
              leftSorted leftFrame
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
          have rightTime := ih (xs.drop k.toNat) rightShorter rightLength rightDisjoint rightDepth
          have rightCorrect :=
            (function_contract (heapLimit := heapLimit)
              hw rightLength rightDisjoint).mono_depth rightDepth
          ram_time_apply rightCorrect rightTime on
            (array.subslice k (array.length - k), scratch.subslice k (array.length - k))
            [ArrayRef.subslice, k]
          · exact ⟨rfl, rightSource, rightScratch⟩
          · exact ⟨rfl, rightSource, rightScratch⟩
          · ram_bound [sortFunctions.result_eq.sort, List.length_take, List.length_drop,
              min_eq_left contained]
          · rintro _ afterRight ⟨rightSorted, _, rightFrame, _, _⟩
            ram_time_vc [sortFunctions.result_eq.sort, List.length_take, List.length_drop,
              min_eq_left contained]
            obtain ⟨sourceAfterRight, ⟨rightWorkspace, scratchAfterRight⟩, _⟩ :=
              Stages.after_right k contained sourceAfterLeft scratchAfterLeft
                leftWorkspaceLength disjoint rightSorted rightFrame
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
            have mergeCorrectSource := (Merge.function_contract
              (heapLimit := heapLimit) positive
              (rightWorkspaceLength.trans mergeLength.symm) mergeLeftDisjoint mergeRightDisjoint).mono_depth
                (show 1 ≤ inner + 1 by omega)
            have mergeTime := (Merge.function_timeBound
              (control := control) (heapLimit := heapLimit) (depth := inner) positive
              (rightWorkspaceLength.trans mergeLength.symm) mergeLeftDisjoint mergeRightDisjoint).renameCalls
                sortFunctions.embeds.Merge
                  ((mergeCorrectSource.raw
                    (array.subslice 0 k, array.subslice k (array.length - k), scratch)).consequence
                    (by rintro values state ⟨rfl, leftRep, rightRep, scratchRep⟩
                        exact ⟨rfl, rfl, leftRep, rightRep, scratchRep⟩)
                    (by intro values state fields finish _ post; exact post))
            have mergeCorrect := mergeCorrectSource.renameCalls sortFunctions.embeds.Merge
            ram_time_apply mergeCorrect mergeTime on
              (array.subslice 0 k, array.subslice k (array.length - k), scratch)
              [ArrayRef.subslice, k]
            · exact ⟨rfl, mergeLeft, mergeRight, scratchAfterRight⟩
            · exact ⟨rfl, mergeLeft, mergeRight, scratchAfterRight⟩
            · ram_bound [Func.renameCalls_locals, Func.renameCalls_results,
                Merge.mergeFunctions.result_eq.merge,
                sortFunctions.result_eq.sort, List.length_take, List.length_drop,
                min_eq_left contained, mergeLength]
            · rintro _ afterMerge ⟨_, _, scratchMerged, mergeFrame, _, _⟩
              ram_time_vc [Merge.mergeFunctions.result_eq.merge, mergeLength]
              have sourceBeforeCopy := sourceAfterRight.2.frame mergeFrame
                (by simpa only [List.length_append, mergeLength] using disjoint.symm)
              rw [merge_sorted_split] at scratchMerged
              have copyLength : (sorted (xs.take k.toNat) ++
                  sorted (xs.drop k.toNat)).length = (sorted xs).length := by
                simpa only [List.length_append, length_sorted] using mergeLength
              have copyFit : (sorted xs).length < 2 ^ w := by
                simpa only [length_sorted] using sourceArray.length_lt
              have copyDisjoint : ArraysDisjoint scratch.base (sorted xs).length
                  array.base (sorted xs).length := by
                simpa only [length_sorted] using disjoint.symm
              have copyCorrect := copy_function_contract
                (program := copyFunctions.program) (heapLimit := heapLimit) (depth := inner + 1)
                positive copyLength copyFit copyDisjoint
              have copyTime := (copy_function_timeBound
                (program := copyFunctions.program) (control := control)
                (heapLimit := heapLimit) (depth := inner + 1)
                positive copyLength copyFit copyDisjoint).renameCalls
                  sortFunctions.embeds.Copy copyCorrect
              ram_time_call copyTime
                [ArrayRef.subslice, sourceArray.length_eq, length_sorted,
                  Func.renameCalls_locals, Func.renameCalls_results,
                  copyFunctions.result_eq.copy, Merge.mergeFunctions.result_eq.merge,
                  sortFunctions.result_eq.sort, List.length_take, List.length_drop,
                  min_eq_left contained, mergeLength]
              exact ⟨scratchMerged.2, sourceBeforeCopy⟩

/-- The canonical budget-free correctness depth suffices for the same body bound. -/
theorem function_timeBound {w control heapLimit : Nat}
    {array scratch : ArrayRef w} {xs workspace : List (Word w)} (hw : 2 ≤ w)
    (hlen : workspace.length = xs.length)
    (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length) :
    FunctionTimeBound control sortFunctions.program heapLimit (Nat.clog 2 xs.length + 1)
      sortFunctions.function.sort
      (fun args entry => args = sortFunctions.arguments.sort array scratch ∧
        array.Rep heapLimit xs entry ∧ scratch.Rep heapLimit workspace entry)
      (fun _ _ => bodyBudget xs.length) :=
  function_timeBound_of_depth hw hlen disjoint (Nat.le_refl _)

/-- The actual typed function's concrete reserve has mathlib's usual `n log n` bound. -/
theorem bodyBudget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => (bodyBudget n : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) :=
  Recurrence.balancedBudget_isBigO 4 227

end Ram.Source.Array.MergeSort.Function
