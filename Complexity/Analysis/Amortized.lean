/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite sums of verified costs

The potential inequalities below are arithmetic tools for summing costs already
justified by execution or contracts. They do not themselves certify machine
execution or assign costs to source operations. Initial potential is part of the
budget; final potential can be kept for a later phase. Neither theorem requires
the potential to be monotone, and both include the empty sequence.

General summation and irregular traversal counting are already upstream:

* `Finset.sum_range_by_parts` in `Mathlib.Algebra.BigOperators.Module` is the
  usual summation-by-parts identity over a module, where subtraction is available.
* `List.length_flatten` and `List.length_flatMap` count list visits, including
  repeated visits, as the sum of the inner lengths.
* `Finset.card_sigma` in `Mathlib.Algebra.BigOperators.Group.Finset.Sigma` counts
  irregular finite index pairs as the sum of their fiber cardinalities. Counting
  pairs preserves visits at different outer indices; counting a union of visited
  values instead could discard duplicates.

These existing results need no additional sum definition or RAM-specific alias.
-/

namespace Finset

open Finset

/-- Sum local amortized bounds without natural subtraction. The final potential
remains available as credit for subsequent work. -/
theorem sum_range_add_potential_le
    {cost charge potential : Nat → Nat} {n : Nat}
    (step : ∀ i, i < n → cost i + potential (i + 1) ≤ charge i + potential i) :
    (∑ i ∈ range n, cost i) + potential n ≤
      (∑ i ∈ range n, charge i) + potential 0 := by
  have hsum : (∑ i ∈ range n, (cost i + potential (i + 1))) ≤
      ∑ i ∈ range n, (charge i + potential i) :=
    sum_le_sum fun i hi => step i (mem_range.mp hi)
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have telescope : (∑ i ∈ range n, potential (i + 1)) + potential 0 =
      (∑ i ∈ range n, potential i) + potential n :=
    (sum_range_succ' potential n).symm.trans (sum_range_succ potential n)
  omega

/-- A constant amortized charge gives a total cost bound, with initial credit
explicitly charged to the budget and nonnegative final credit discarded. -/
theorem sum_range_le_mul_add_of_potential
    {cost potential : Nat → Nat} {n charge : Nat}
    (step : ∀ i, i < n → cost i + potential (i + 1) ≤ charge + potential i) :
    (∑ i ∈ range n, cost i) ≤ n * charge + potential 0 := by
  have h := sum_range_add_potential_le (charge := fun _ => charge) step
  simp only [sum_const, card_range, Nat.nsmul_eq_mul] at h
  omega

end Finset
