/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity.Recurrence.Balanced

/-!
# Depth and budget reserves for recursive merge sort

The two branches have floor/ceiling half lengths. These arithmetic lemmas
supply the depth and budget in the function contract. The contract separately
justifies the actual instruction counts, including its two calls and copying;
this module does not assign costs to a host-side sorting function.
-/

namespace Ram.Source.Array.MergeSort.Bounds

/-- Maximum nested calls made by a body sorting `n` elements. -/
def depth (n : Nat) : Nat := Nat.clog 2 n

/-- Each nontrivial call pays its two children from a balanced supersolution. -/
def budget (n : Nat) : Nat := Ram.Recurrence.balancedBudget 4 158 n

@[simp] theorem depth_zero : depth 0 = 0 := by simp [depth]
@[simp] theorem depth_one : depth 1 = 0 := by simp [depth]
@[simp] theorem budget_zero : budget 0 = 4 := by simp [budget]
@[simp] theorem budget_one : budget 1 = 4 := by simp [budget]

/-- Both base cases take no recursive depth and reserve their final guard. -/
theorem budget_small {n : Nat} (hn : n ≤ 1) : budget n = 4 := by
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl <;> simp

theorem depth_left {n : Nat} (hn : 2 ≤ n) : depth (n / 2) + 1 ≤ depth n := by
  have hm : Nat.clog 2 (n / 2) ≤ Nat.clog 2 (n - n / 2) :=
    Nat.clog_mono_right 2 (by omega)
  exact (Nat.add_le_add_right hm 1).trans_eq (Ram.Recurrence.clog_ceil_half_add_one hn)

theorem depth_right {n : Nat} (hn : 2 ≤ n) : depth (n - n / 2) + 1 ≤ depth n :=
  Nat.le_of_eq (Ram.Recurrence.clog_ceil_half_add_one hn)

/-- Reserve both child budgets plus merge/copy and the fixed nonrecursive
overhead. The machine proof must establish that its overhead is at most this
quantity; no recurrence hypothesis is assumed for the runtime itself. -/
theorem budget_split_cover {n : Nat} (hn : 2 ≤ n) :
    budget (n / 2) + budget (n - n / 2) + (53 * n + 209) ≤ budget n := by
  exact (Nat.add_le_add_left (by omega : 53 * n + 209 ≤ 158 * n) _).trans
    (Ram.Recurrence.balancedBudget_split_le 4 158 hn)

/-- Direct mathlib `IsBigO` for the budget used in the recursive contract. -/
theorem budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => (budget n : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) :=
  Ram.Recurrence.balancedBudget_isBigO 4 158

/-- The initial three-argument call and final halt can be covered by a larger
base reserve. Their actual instruction lengths are proved in the program modules. -/
theorem block_budget_le (n : Nat) :
    budget n + 82 ≤ Ram.Recurrence.balancedBudget 86 158 n :=
  Ram.Recurrence.balancedBudget_add_const_le 4 158 82 n

/-- The actual main-block budget, including its initial call and halt, has
the same direct mathlib asymptotic bound as the recursive body reserve. -/
theorem block_budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => ((budget n + 82 : Nat) : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) := by
  refine (Asymptotics.IsBigO.of_norm_le (g := fun n =>
    (Ram.Recurrence.balancedBudget 86 158 n : ℝ)) ?_).trans
      (Ram.Recurrence.balancedBudget_isBigO 86 158)
  intro n
  simpa only [Real.norm_natCast] using (Nat.cast_le.mpr (block_budget_le n) :
    ((budget n + 82 : Nat) : ℝ) ≤ (Ram.Recurrence.balancedBudget 86 158 n : ℝ))

end Ram.Source.Array.MergeSort.Bounds
