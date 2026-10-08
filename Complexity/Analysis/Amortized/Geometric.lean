/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# Online geometric capacity growth

A reusable buffer retains its current capacity when a request fits. Otherwise
its new capacity is the larger of the current request and twice its previous
capacity. This policy reads no future requests. Starting at zero, all fresh
reservations together use at most twice the final capacity, which is at most
twice the largest request so far.

These are arithmetic bounds on the specified capacity transitions, not costs
assigned to arbitrary programs. A concrete loader must establish that it uses
`next` and reserves exactly `allocated` fresh words. Initialization, overwriting,
driver work and old reservations remain the loader's actual operations. A first
empty allocation reserves zero words; its nonzero instruction overhead is not
discarded by this word count.
-/

namespace Complexity.GeometricCapacity

/-- Retain sufficient capacity; on a miss, grow using only the current request. -/
def next (capacity request : Nat) : Nat :=
  if request ≤ capacity then capacity else max request (2 * capacity)

/-- Fresh words reserved by this policy. Reuse allocates nothing, while growth
retains the old region and allocates the complete new capacity. -/
def allocated (capacity request : Nat) : Nat :=
  if request ≤ capacity then 0 else max request (2 * capacity)

@[simp] theorem next_of_le {capacity request : Nat} (h : request ≤ capacity) :
    next capacity request = capacity := by simp [next, h]

theorem next_of_lt {capacity request : Nat} (h : capacity < request) :
    next capacity request = max request (2 * capacity) := by
  simp [next, Nat.not_le.mpr h]

@[simp] theorem allocated_of_le {capacity request : Nat} (h : request ≤ capacity) :
    allocated capacity request = 0 := by simp [allocated, h]

theorem allocated_of_lt {capacity request : Nat} (h : capacity < request) :
    allocated capacity request = max request (2 * capacity) := by
  simp [allocated, Nat.not_le.mpr h]

@[simp] theorem next_zero (request : Nat) : next 0 request = request := by
  simp only [next, Nat.mul_zero, Nat.max_zero]
  split <;> omega

@[simp] theorem allocated_zero (request : Nat) : allocated 0 request = request := by
  simp only [allocated, Nat.mul_zero, Nat.max_zero]
  split <;> omega

/-- Every current request fits in the selected capacity. -/
theorem next_ge_request (capacity request : Nat) : request ≤ next capacity request := by
  unfold next
  split <;> omega

/-- Capacity never shrinks; repeated smaller requests reuse the same reservation. -/
theorem next_ge_capacity (capacity request : Nat) : capacity ≤ next capacity request := by
  unfold next
  split <;> omega

/-- The accumulated-reservation invariant is preserved by one actual policy step. -/
theorem add_allocated_le_two_mul_next {amount capacity request : Nat}
    (previous : amount ≤ 2 * capacity) :
    amount + allocated capacity request ≤ 2 * next capacity request := by
  by_cases fits : request ≤ capacity
  · simp only [allocated_of_le fits, next_of_le fits, Nat.add_zero]
    exact previous
  · rw [allocated_of_lt (Nat.lt_of_not_ge fits), next_of_lt (Nat.lt_of_not_ge fits)]
    omega

/-- A bound on requests already observed is preserved, without consulting later inputs. -/
theorem next_le_two_mul {capacity request maximum : Nat}
    (previous : capacity ≤ 2 * maximum) (current : request ≤ maximum) :
    next capacity request ≤ 2 * maximum := by
  unfold next
  split <;> omega

/-- Total fresh reservations along a finite sequence of the specified transitions.
The old regions are not subtracted or assumed to be freed. -/
theorem sum_allocated_le_two_mul_capacity {capacity request : Nat → Nat} {n : Nat}
    (initial : capacity 0 = 0)
    (step : ∀ i, i < n → capacity (i + 1) = next (capacity i) (request i)) :
    (∑ i ∈ Finset.range n, allocated (capacity i) (request i)) ≤ 2 * capacity n := by
  revert step
  induction n with
  | zero => simp [initial]
  | succ n ih =>
      intro step
      have previous := ih (fun i hi => step i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      rw [Finset.sum_range_succ, step n (Nat.lt_succ_self n)]
      exact add_allocated_le_two_mul_next previous

/-- A finite trace whose requests are bounded has at most twice that capacity. -/
theorem capacity_le_two_mul {capacity request : Nat → Nat} {n maximum : Nat}
    (initial : capacity 0 = 0)
    (step : ∀ i, i < n → capacity (i + 1) = next (capacity i) (request i))
    (requests : ∀ i, i < n → request i ≤ maximum) :
    capacity n ≤ 2 * maximum := by
  revert step requests
  induction n with
  | zero => simp [initial]
  | succ n ih =>
      intro step requests
      have previous := ih
        (fun i hi => step i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        (fun i hi => requests i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      rw [step n (Nat.lt_succ_self n)]
      exact next_le_two_mul previous (requests n (Nat.lt_succ_self n))

/-- The maximum is taken only over the actual finite prefix, with empty maximum zero. -/
theorem capacity_le_two_mul_sup {capacity request : Nat → Nat} {n : Nat}
    (initial : capacity 0 = 0)
    (step : ∀ i, i < n → capacity (i + 1) = next (capacity i) (request i)) :
    capacity n ≤ 2 * (Finset.range n).sup request :=
  capacity_le_two_mul initial step (fun _ hi => Finset.le_sup (Finset.mem_range.mpr hi))

/-- Even retaining every replaced buffer, total fresh storage is linear in the
largest request seen so far. No future-size advice or reclamation is assumed. -/
theorem sum_allocated_le_four_mul_sup {capacity request : Nat → Nat} {n : Nat}
    (initial : capacity 0 = 0)
    (step : ∀ i, i < n → capacity (i + 1) = next (capacity i) (request i)) :
    (∑ i ∈ Finset.range n, allocated (capacity i) (request i)) ≤
      4 * (Finset.range n).sup request := by
  have reserved := sum_allocated_le_two_mul_capacity initial step
  have bounded := capacity_le_two_mul_sup initial step
  omega

end Complexity.GeometricCapacity
