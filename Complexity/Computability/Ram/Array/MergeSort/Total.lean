/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.Basic
import Complexity.Computability.Ram.Array.MergeSort.Bounds
import Complexity.Tactic.Ram.Total

/-!
# Functional correctness of the existing recursive merge-sort function

The recursion argument is the ordinary list, ordered by length. The proof
uses callable total specifications for both smaller halves and the existing
array/frame interfaces for their mathematical results. Initialization and
merge/copy-back use independently proved total contracts, down to the actual
copy and merge iterations. No fuel, continuation reserve or instruction
arithmetic is needed.

This is the same fixed function and the same `Pre`/`Post` as the measured
interface. The logarithmic call-depth obligations still justify its stack
usage; a separate time proof can later be combined with this total result.
-/

namespace Ram.Source.Array.MergeSort

/-- The source-level guard follows the ordinary list's nontrivial-length test. -/
theorem condition_ne_zero_iff {heapLimit : Nat}
    {base scratch : Word w} {xs : List (Word w)} {entry : State w}
    (hw : 0 < w) (hp : Pre heapLimit base scratch xs entry) :
    entry.eval condition ≠ 0 ↔ 1 < xs.length := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  change BinOp.eval .ult (1 : Word w) (entry.regs 2) ≠ 0 ↔ _
  rw [BinOp.eval_ult_ne_zero_iff hw, hone, hp.length_reg]

variable {w heapLimit selfFn : Nat} {functions : Program}

/-- Functional recursion preserves the sorted-array, scratch, memory-frame
and I/O postconditions, independently of any proposed running-time bound. -/
theorem recursive_total (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    ∀ xs, (recursionSpec heapLimit selfFn w).toTotal.Correct functions heapLimit xs := by
  apply Recursion.TotalSpec.verify_wellFounded _
    (measure (fun xs : List (Word w) => xs.length)).wf
  intro xs ih entry hp
  change Pre heapLimit (entry.regs 0) (entry.regs 1) xs entry at hp
  change Verification.TotalWP functions heapLimit (Nat.clog 2 xs.length)
    (.ite condition
      (.seq setup (.seq (.call 4 selfFn leftArgs)
        (.seq (.call 4 selfFn rightArgs) Combine.program))) .skip)
    (fun finish => True ∧ Post heapLimit (entry.regs 0) (entry.regs 1) xs entry finish) entry
  rw [Verification.TotalWP.ite_iff]
  refine ⟨by simp [condition, Expr.ReadsBelow], ?_⟩
  by_cases hsmall : xs.length ≤ 1
  · have hz : entry.eval condition = 0 := by
      by_contra hnonzero
      have := (condition_ne_zero_iff (by omega) hp).mp hnonzero
      omega
    rw [if_pos hz, Verification.TotalWP.skip_iff]
    exact ⟨trivial, small_post hp hsmall⟩
  · have hlarge : 2 ≤ xs.length := by omega
    have hnonzero : entry.eval condition ≠ 0 :=
      (condition_ne_zero_iff (by omega) hp).mpr (by omega)
    have hleftLength : (xs.take (xs.length / 2)).length = xs.length / 2 :=
      List.length_take_of_le (Nat.div_le_self _ _)
    have hrightLength : (xs.drop (xs.length / 2)).length =
        xs.length - xs.length / 2 := List.length_drop ..
    have leftCorrect := ih (xs.take (xs.length / 2)) (by
      change (xs.take (xs.length / 2)).length < xs.length
      rw [hleftLength]
      omega)
    have rightCorrect := ih (xs.drop (xs.length / 2)) (by
      change (xs.drop (xs.length / 2)).length < xs.length
      rw [hrightLength]
      omega)
    have hleftDepth : Nat.clog 2 (xs.take (xs.length / 2)).length + 1 ≤
        Nat.clog 2 xs.length := by
      simpa only [hleftLength, Bounds.depth] using Bounds.depth_left hlarge
    have hrightDepth : Nat.clog 2 (xs.drop (xs.length / 2)).length + 1 ≤
        Nat.clog 2 xs.length := by
      simpa only [hrightLength, Bounds.depth] using Bounds.depth_right hlarge
    rw [if_neg hnonzero]
    ram_total_apply (initialize_total_contract (functions := functions)
      (heapLimit := heapLimit) (depth := Nat.clog 2 xs.length) entry)
    apply leftCorrect.wp_call lookup rfl (by change 3 ≤ 9; decide)
    · simp [leftArgs, Expr.ReadsBelow]
    · exact left_pre (selfFn := selfFn) hw hp
    · exact hleftDepth
    · intro leftCallee leftPost
      have leftStage := after_left (selfFn := selfFn) hw hp leftPost
      simp only [Verification.TotalWP.seq_iff]
      apply rightCorrect.wp_call lookup rfl (by change 3 ≤ 9; decide)
      · simp [rightArgs, Expr.ReadsBelow]
      · exact right_pre (selfFn := selfFn) hp leftStage
      · exact hrightDepth
      · intro rightCallee rightPost
        have rightStage := after_right (selfFn := selfFn) hp leftStage rightPost
        obtain ⟨workspace, combinePre⟩ := combine_pre hp rightStage
        ram_total_apply (Combine.total_contract (functions := functions)
          (heapLimit := heapLimit) (depth := Nat.clog 2 xs.length)
          (by omega : 0 < w))
        · exact combinePre
        · intro finish finishPost
          simpa only [true_and] using after_combine hp rightStage finishPost

end Ram.Source.Array.MergeSort
