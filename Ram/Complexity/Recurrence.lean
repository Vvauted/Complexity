/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring
import Ram.Loop.Logarithmic

/-!
# Arithmetic bounds for verified recursive budgets

These comparison lemmas help discharge the budget obligations of recursive
function contracts. The recurrence must already account for the actual work:
for example, `Recursion.Spec.callBudget` includes generated argument setup,
save/restore blocks and jumps. A toll below is an upper bound to prove for that
work, not a new instruction price or a runtime annotation.

The results are arithmetic facts about natural-valued functions. They do not
establish termination, functional correctness, word/stack fit, or a machine
certificate on their own. In particular, the factor `branches` in a recurrence
is an assumption about the total recursive work, not evidence that a program
has that many equal-sized calls.

Finite sums, ceiling logarithms and the concluding asymptotic relation are
mathlib's `Finset.sum`, `Nat.clog` and `Asymptotics.IsBigO`.
-/

namespace Ram.Recurrence

open scoped BigOperators

/-- Accumulate a possibly nonmonotone toll. The summand `toll k` pays for the
transition from size `k + 1` to size `k`, including its actual call overhead. -/
theorem le_sum_of_succ_le {T toll : Nat → Nat} {initial : Nat}
    (zero : T 0 ≤ initial) (step : ∀ n, T (n + 1) ≤ T n + toll n) (n : Nat) :
    T n ≤ initial + ∑ i ∈ Finset.range n, toll i := by
  induction n with
  | zero => simpa using zero
  | succ n ih =>
      rw [Finset.sum_range_succ, ← Nat.add_assoc]
      exact (step n).trans (Nat.add_le_add_right ih _)

/-- Constant incremental work gives an all-input affine bound. -/
theorem le_affine_of_succ_le {T : Nat → Nat} {initial toll : Nat}
    (zero : T 0 ≤ initial) (step : ∀ n, T (n + 1) ≤ T n + toll) (n : Nat) :
    T n ≤ initial + toll * n := by
  simpa [Nat.mul_comm] using le_sum_of_succ_le zero step n

/-- Compare a dividing recurrence with a proposed supersolution. No
monotonicity of either function or of the variable toll is required. -/
theorem le_of_div_le {T bound toll : Nat → Nat} {divisor branches : Nat}
    (divides : 1 < divisor) (zero : T 0 ≤ bound 0)
    (step : ∀ n, 0 < n → T n ≤ branches * T (n / divisor) + toll n)
    (reserve : ∀ n, 0 < n → branches * bound (n / divisor) + toll n ≤ bound n) :
    ∀ n, T n ≤ bound n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n = 0
      · simpa only [hn] using zero
      · have positive : 0 < n := Nat.pos_of_ne_zero hn
        exact (step n positive).trans
          ((Nat.add_le_add_right
            (Nat.mul_le_mul_left branches (ih _ (Nat.div_lt_self positive divides))) _).trans
              (reserve n positive))

/-- Complete-tree upper bound at a given recursion height. It is a closed
arithmetic expression, not another evaluator or a proof of a call tree. -/
def geometricBudget (branches initial toll height : Nat) : Nat :=
  branches ^ height * initial + toll * ∑ i ∈ Finset.range height, branches ^ i

@[simp] theorem geometricBudget_zero (branches initial toll : Nat) :
    geometricBudget branches initial toll 0 = initial := by
  simp [geometricBudget]

/-- Reserve the recursive sub-budgets and the current node's toll exactly. -/
theorem geometricBudget_succ (branches initial toll height : Nat) :
    geometricBudget branches initial toll (height + 1) =
      branches * geometricBudget branches initial toll height + toll := by
  unfold geometricBudget
  rw [Finset.sum_range_succ']
  simp only [Nat.pow_succ, Nat.pow_zero, ← Finset.sum_mul]
  ring

/-- The zero case costs `initial`; every positive size divides by `divisor`.
Each division consumes exactly one shifted ceiling-logarithm level. -/
theorem le_geometric_of_div_le {T : Nat → Nat} {divisor branches initial toll : Nat}
    (divides : 1 < divisor) (zero : T 0 ≤ initial)
    (step : ∀ n, 0 < n → T n ≤ branches * T (n / divisor) + toll) (n : Nat) :
    T n ≤ geometricBudget branches initial toll (Nat.clog divisor (n + 1)) := by
  apply le_of_div_le divides (by simpa using zero) step
  intro m hm
  rw [← Source.Contract.clog_div_succ_add_one divides hm, geometricBudget_succ]

/-- In a single-branch recurrence the geometric sum is just the number of
positive levels. This includes size zero and does not round away base work. -/
theorem le_clog_of_div_le {T : Nat → Nat} {divisor initial toll : Nat}
    (divides : 1 < divisor) (zero : T 0 ≤ initial)
    (step : ∀ n, 0 < n → T n ≤ T (n / divisor) + toll) (n : Nat) :
    T n ≤ initial + toll * Nat.clog divisor (n + 1) := by
  have hstep : ∀ m, 0 < m → T m ≤ 1 * T (m / divisor) + toll := by
    simpa only [Nat.one_mul] using step
  simpa [geometricBudget] using le_geometric_of_div_le divides zero hstep n

/-- The same recurrence yields mathlib's logarithmic `IsBigO` statement.
The all-input theorem above retains the possibly nonzero cost at size zero;
the asymptotic proof uses positivity of the logarithm for sizes at least one. -/
theorem isBigO_clog_of_div_le {T : Nat → Nat} {divisor initial toll : Nat}
    (divides : 1 < divisor) (zero : T 0 ≤ initial)
    (step : ∀ n, 0 < n → T n ≤ T (n / divisor) + toll) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (Nat.clog divisor (n + 1) : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((initial + toll : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hlog : 1 ≤ Nat.clog divisor (n + 1) :=
    Nat.clog_pos divides (by omega)
  have hnat : T n ≤ (initial + toll) * Nat.clog divisor (n + 1) := by
    calc
      T n ≤ initial + toll * Nat.clog divisor (n + 1) :=
        le_clog_of_div_le divides zero step n
      _ ≤ initial * Nat.clog divisor (n + 1) + toll * Nat.clog divisor (n + 1) :=
        Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left initial hlog) _
      _ = (initial + toll) * Nat.clog divisor (n + 1) := (Nat.add_mul _ _ _).symm
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (T n : ℝ) ≤ (((initial + toll) * Nat.clog divisor (n + 1) : Nat) : ℝ))

end Ram.Recurrence
