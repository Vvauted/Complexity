/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Upper-bound comparison for finite-branch recurrences

Compare a recursive upper bound with a proposed supersolution. The children
may have different, rounded sizes. Neither the cost nor its supersolution
needs to be monotone. One ordered-semiring proof covers natural budgets and
the real-valued comparisons used by mathlib's Akra–Bazzi theorem.

This arithmetic comparison does not establish execution or termination of
a machine program. A program's recurrence must include its actual compiled
work, including the setup and return cost of every recursive call.
-/

namespace Ram.Recurrence

open scoped BigOperators

/-- A finite recursive upper bound is dominated by any supersolution that
covers all base cases. Nonnegative coefficients preserve child inequalities;
strictly smaller child sizes justify the strong induction. -/
theorem le_of_sum_rec_le {ι R : Type*} [Fintype ι]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {T bound toll : Nat → R} {a : ι → R} {r : ι → Nat → Nat} {n₀ : Nat}
    (ha : ∀ i, 0 ≤ a i)
    (base : ∀ n, n < n₀ → T n ≤ bound n)
    (smaller : ∀ i n, n₀ ≤ n → r i n < n)
    (step : ∀ n, n₀ ≤ n → T n ≤ (∑ i, a i * T (r i n)) + toll n)
    (reserve : ∀ n, n₀ ≤ n → (∑ i, a i * bound (r i n)) + toll n ≤ bound n) :
    ∀ n, T n ≤ bound n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rcases lt_or_ge n n₀ with hn | hn
      · exact base n hn
      · apply (step n hn).trans
        apply le_trans _ (reserve n hn)
        exact add_le_add (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (ih _ (smaller i n hn)) (ha i)) le_rfl

end Ram.Recurrence
