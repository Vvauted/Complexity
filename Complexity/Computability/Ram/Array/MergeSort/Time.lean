/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.Total
import Complexity.Computability.Ram.Verification.Time.Capacity
import Complexity.Computability.Ram.Verification.Time.Composition

/-!
# Time analysis of the existing recursive merge sort

The functional proof supplies the intermediate array assertions at each call.
This independent induction adds the actual setup, call, merge/copy and guard
counts using `TimeBound`. There is no unused fuel to subtract or thread.
The recurrence and final budget are unchanged from the original contract.
-/

namespace Ram.Source.Array.MergeSort

variable {w control heapLimit selfFn : Nat} {functions : Program}

/-- The existing body budget bounds every completed execution. Recursive
functional contracts supply states and termination, not cost hypotheses;
the time induction supplies the two child bounds independently. -/
theorem recursive_timeBound (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    ∀ xs, TimeBound control functions heapLimit (Nat.clog 2 xs.length)
      (function selfFn).body ((recursionSpec heapLimit selfFn w).pre xs)
      (fun _ => budget xs.length) := by
  intro xs
  induction xs using (measure (fun xs : List (Word w) => xs.length)).wf.induction with
  | h xs ih =>
    intro entry hp steps finish execution
    change Pre heapLimit (entry.regs 0) (entry.regs 1) xs entry at hp
    let n := xs.length
    let left := xs.take (n / 2)
    let right := xs.drop (n / 2)
    have hleft : left.length = n / 2 := List.length_take_of_le (Nat.div_le_self _ _)
    have hright : right.length = n - n / 2 := List.length_drop ..
    by_cases hsmall : n ≤ 1
    · have impossible : TimeBound control functions heapLimit (Nat.clog 2 n)
          (.seq setup (.seq (.call 4 selfFn leftArgs)
            (.seq (.call 4 selfFn rightArgs) Combine.program)))
          (fun s => s = entry ∧ s.eval condition ≠ 0) (fun _ => 0) := by
        rintro s ⟨rfl, nonzero⟩
        have large := (condition_ne_zero_iff (by omega) hp).mp nonzero
        omega
      have cost := TimeBound.ite impossible (TimeBound.skip
        (fun s => s = entry ∧ s.eval condition = 0))
      have hz : entry.eval condition = 0 := by
        by_contra hn
        have large := (condition_ne_zero_iff (by omega) hp).mp hn
        omega
      have bounded := cost entry rfl steps finish execution
      change steps ≤ 4 + (if entry.eval condition = 0 then 0 else 0 + 1) at bounded
      rw [if_pos hz] at bounded
      change steps ≤ budget n
      have budgetSmall : budget n = 4 := Bounds.budget_small hsmall
      rw [budgetSmall]
      exact bounded
    · have hlarge : 2 ≤ n := by omega
      have hleftLt : left.length < xs.length := by change left.length < n; omega
      have hrightLt : right.length < xs.length := by change right.length < n; omega
      have leftTime := ih left hleftLt
      have rightTime := ih right hrightLt
      have leftTotal := recursive_total (heapLimit := heapLimit) hw lookup left
      have rightTotal := recursive_total (heapLimit := heapLimit) hw lookup right
      have leftDepth : Nat.clog 2 left.length + 1 ≤ Nat.clog 2 n := by
        simpa only [hleft, Bounds.depth] using Bounds.depth_left hlarge
      have rightDepth : Nat.clog 2 right.length + 1 ≤ Nat.clog 2 n := by
        simpa only [hright, Bounds.depth] using Bounds.depth_right hlarge
      let afterLeft := Stage heapLimit (entry.regs 0) (entry.regs 1) xs
        (sorted left) right entry
      let afterRight := Stage heapLimit (entry.regs 0) (entry.regs 1) xs
        (sorted left) (sorted right) entry
      have leftCall : TotalContract functions heapLimit (Nat.clog 2 left.length + 1)
          (.call 4 selfFn leftArgs) (fun s => s = initialized entry) afterLeft := by
        rintro s rfl
        apply leftTotal.wp_call lookup rfl (by change 3 ≤ 9; decide)
        · simp [leftArgs, Expr.ReadsBelow]
        · exact left_pre (selfFn := selfFn) hw hp
        · exact Nat.le_refl _
        · intro callee post
          exact after_left (selfFn := selfFn) hw hp post
      have rightCall : TotalContract functions heapLimit (Nat.clog 2 right.length + 1)
          (.call 4 selfFn rightArgs) afterLeft afterRight := by
        intro caller stage
        apply rightTotal.wp_call lookup rfl (by change 3 ≤ 9; decide)
        · simp [rightArgs, Expr.ReadsBelow]
        · exact right_pre (selfFn := selfFn) hp stage
        · exact Nat.le_refl _
        · intro callee post
          exact after_right (selfFn := selfFn) hp stage post
      have leftCost : TimeBound control functions heapLimit (Nat.clog 2 n)
          (.call 4 selfFn leftArgs) (fun s => s = initialized entry)
          (fun _ => budget left.length + 81) := by
        have original := TimeBound.call (dst := 4) lookup
          (fun s (same : s = initialized entry) => by
            subst s
            exact left_pre (selfFn := selfFn) hw hp) leftTime
        have enlarged := original.change_capacity
          (heapLimit' := heapLimit) (depth' := Nat.clog 2 n) leftCall
        apply enlarged.mono_budget
        intro s same
        exact Nat.le_of_eq (left_call_steps control (budget left.length))
      have rightCost : TimeBound control functions heapLimit (Nat.clog 2 n)
          (.call 4 selfFn rightArgs) afterLeft
          (fun _ => budget right.length + 87) := by
        have original := TimeBound.call (dst := 4) lookup
          (fun s (stage : afterLeft s) => right_pre (selfFn := selfFn) hp stage) rightTime
        have enlarged := original.change_capacity
          (heapLimit' := heapLimit) (depth' := Nat.clog 2 n) rightCall
        apply enlarged.mono_budget
        intro s stage
        exact Nat.le_of_eq (right_call_steps control (budget right.length))
      have combineCost : TimeBound control functions heapLimit (Nat.clog 2 n)
          Combine.program afterRight (fun _ => 53 * n + 26) := by
        intro caller stage count target run
        obtain ⟨workspace, pre⟩ := combine_pre hp stage
        have bounded := (Combine.timeBound (control := control) (functions := functions)
          (heapLimit := heapLimit) (depth := Nat.clog 2 n) (by omega : 0 < w))
          caller pre count target run
        have hsum : (sorted left).length + (sorted right).length = n := by
          rw [length_sorted, length_sorted, hleft, hright]
          omega
        simpa only [hsum] using bounded
      have rightRest : TimeBound control functions heapLimit (Nat.clog 2 n)
          (.seq (.call 4 selfFn rightArgs) Combine.program) afterLeft
          (fun _ => budget right.length + 87 + (53 * n + 26)) :=
        TimeBound.seq (rightCall.mono_depth rightDepth) rightCost combineCost
          (fun _ _ _ _ => Nat.le_refl _)
      have leftRest : TimeBound control functions heapLimit (Nat.clog 2 n)
          (.seq (.call 4 selfFn leftArgs)
            (.seq (.call 4 selfFn rightArgs) Combine.program))
          (fun s => s = initialized entry)
          (fun _ => budget left.length + 81 + (budget right.length + 87 + (53 * n + 26))) :=
        TimeBound.seq (leftCall.mono_depth leftDepth) leftCost rightRest
          (fun _ _ _ _ => Nat.le_refl _)
      have setupContract := initialize_contract (control := control) (functions := functions)
        (heapLimit := heapLimit) (depth := Nat.clog 2 n) entry
      have setupTotal := initialize_total_contract (functions := functions)
        (heapLimit := heapLimit) (depth := Nat.clog 2 n) entry
      have bodyCost := TimeBound.seq setupTotal setupContract.timeBound leftRest
        (bound := fun _ => 10 + (budget left.length + 81 +
          (budget right.length + 87 + (53 * n + 26))))
        (fun _ _ _ _ => Nat.le_refl _)
      have yes := bodyCost.consequence
        (P' := fun s => s = entry ∧ s.eval condition ≠ 0)
        (fun _ hs => hs.1) (fun _ _ => Nat.le_refl _)
      have both := TimeBound.ite yes
        (TimeBound.skip (fun s => s = entry ∧ s.eval condition = 0))
      have bounded := both entry rfl steps finish execution
      have nonzero : entry.eval condition ≠ 0 :=
        (condition_ne_zero_iff (by omega) hp).mpr (by omega)
      change steps ≤ 4 + (if entry.eval condition = 0 then 0 else
        (10 + (budget left.length + 81 + (budget right.length + 87 + (53 * n + 26)))) + 1)
        at bounded
      rw [if_neg nonzero, hleft, hright] at bounded
      have cover := Bounds.budget_split_cover hlarge
      change steps ≤ budget n
      change budget (n / 2) + budget (n - n / 2) + (53 * n + 209) ≤ budget n at cover
      omega

end Ram.Source.Array.MergeSort
