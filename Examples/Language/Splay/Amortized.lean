/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Trace
import Complexity.Analysis.Amortized

/-!
# Summing measured splay-access bounds

This module combines rotation certificates with an externally justified bound
`steps ≤ K * (rotations + 1)`. The latter premise must be supplied by a theorem
about the actual implementation's execution, not by pricing this mathematical
tree relation. The generic potential-sum theorem then accounts for all accesses.

Initial potential is charged explicitly; final potential can be retained or
discarded using its nonnegativity. No theorem here claims logarithmic worst-case
time for an individual access. The additive terms cover empty trees and empty
sequences without a positivity restriction on the node count or sequence length.
-/

namespace Complexity.Language.Examples.Splay

open Finset

variable {α : Type*} {trees focus : Nat → Tree α} {rotations steps : Nat → Nat} {m K : Nat}

private theorem rank_eq_initial_of_traces
    (traces : ∀ i, i < m → SplayTrace (focus i) (trees i) (trees (i + 1)) (rotations i))
    {i : Nat} (hi : i ≤ m) : rank (trees i) = rank (trees 0) := by
  have hsize : ∀ j, j ≤ m → (trees j).numLeaves = (trees 0).numLeaves := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      exact (traces j (Nat.lt_of_succ_le hj)).numLeaves_eq.trans
        (ih (Nat.le_trans (Nat.le_succ j) hj))
  exact congrArg (fun size : Nat => Real.logb 2 (size : ℝ)) (hsize i hi)

/-- Sum supplied implementation costs and retain the final scaled potential. -/
theorem sum_steps_add_potential_le
    (traces : ∀ i, i < m → SplayTrace (focus i) (trees i) (trees (i + 1)) (rotations i))
    (costs : ∀ i, i < m → steps i ≤ K * (rotations i + 1)) :
    ((∑ i ∈ range m, steps i : Nat) : ℝ) + (K : ℝ) * potential (trees m) ≤
      (K : ℝ) * ((m : ℝ) *
        (3 * Real.logb 2 (((trees 0).numNodes + 1 : Nat) : ℝ) + 2) + potential (trees 0)) := by
  have localBound : ∀ i, i < m → (steps i : ℝ) + (K : ℝ) * potential (trees (i + 1)) ≤
      (K : ℝ) * (3 * rank (trees 0) + 2) + (K : ℝ) * potential (trees i) := by
    intro i hi
    have htrace := mul_le_mul_of_nonneg_left (traces i hi).rotations_add_potential_le
      (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    have hcost : (steps i : ℝ) ≤ (K : ℝ) * ((rotations i : ℝ) + 1) := by
      exact_mod_cast costs i hi
    rw [rank_eq_initial_of_traces traces (Nat.le_of_lt hi)] at htrace
    nlinarith
  have hsum := Finset.sum_range_add_potential_le (n := m)
    (cost := fun i => (steps i : ℝ))
    (charge := fun _ => (K : ℝ) * (3 * rank (trees 0) + 2))
    (potential := fun i => (K : ℝ) * potential (trees i)) localBound
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  calc
    ((∑ i ∈ range m, steps i : Nat) : ℝ) + (K : ℝ) * potential (trees m) =
        (∑ i ∈ range m, (steps i : ℝ)) + (K : ℝ) * potential (trees m) := by
      simp only [Nat.cast_sum]
    _ ≤ (m : ℝ) * ((K : ℝ) * (3 * rank (trees 0) + 2)) +
        (K : ℝ) * potential (trees 0) := hsum
    _ = (K : ℝ) * ((m : ℝ) *
        (3 * Real.logb 2 (((trees 0).numNodes + 1 : Nat) : ℝ) + 2) + potential (trees 0)) := by
      rw [rank_eq_log_numNodes]
      ring

/-- Discard nonnegative final credit while retaining the actual initial potential. -/
theorem sum_steps_le
    (traces : ∀ i, i < m → SplayTrace (focus i) (trees i) (trees (i + 1)) (rotations i))
    (costs : ∀ i, i < m → steps i ≤ K * (rotations i + 1)) :
    ((∑ i ∈ range m, steps i : Nat) : ℝ) ≤
      (K : ℝ) * ((m : ℝ) *
        (3 * Real.logb 2 (((trees 0).numNodes + 1 : Nat) : ℝ) + 2) + potential (trees 0)) := by
  have h := sum_steps_add_potential_le traces costs
  have hfinal := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) (potential_nonneg (trees m))
  linarith

/-- A bound uniform over all initial shapes, including their initial credit. -/
theorem sum_steps_le_log
    (traces : ∀ i, i < m → SplayTrace (focus i) (trees i) (trees (i + 1)) (rotations i))
    (costs : ∀ i, i < m → steps i ≤ K * (rotations i + 1)) :
    ((∑ i ∈ range m, steps i : Nat) : ℝ) ≤
      (K : ℝ) * ((m : ℝ) *
        (3 * Real.logb 2 (((trees 0).numNodes + 1 : Nat) : ℝ) + 2) +
          ((trees 0).numNodes : ℝ) * Real.logb 2 (((trees 0).numNodes + 1 : Nat) : ℝ)) := by
  apply (sum_steps_le traces costs).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (potential_le_numNodes_mul_log (trees 0)))
    (Nat.cast_nonneg K)

end Complexity.Language.Examples.Splay
