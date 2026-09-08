/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Recurrence.Finite
import Mathlib.Computability.AkraBazzi.AkraBazzi

/-!
# Recursive upper bounds through mathlib's Akra–Bazzi theorem

The supplied `AkraBazziRecurrence` describes an exact real-valued comparison
function. The cost being analyzed only needs a recursive upper inequality.
A single constant covers all base cases; positivity of the comparison
function and nonnegativity of the toll come from the upstream structure.

Only an upper asymptotic bound is transferred, not a matching lower bound or
`IsTheta`. These arithmetic results do not replace a program's termination,
correctness, or measured-execution certificate. The upstream regularity
condition `GrowsPolynomially` is retained unchanged.
-/

namespace AkraBazziRecurrence

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {M : Nat → ℝ} {g : ℝ → ℝ} {a b : ι → ℝ} {r : ι → Nat → Nat}
variable (R : AkraBazziRecurrence M g a b r)

/-- Scale an exact Akra–Bazzi comparison function to cover the base costs of
a recursive upper inequality. The same constant works for every size. -/
theorem le_mul_of_rec_le {T : Nat → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (base : ∀ n, n < R.n₀ → T n ≤ C * M n)
    (step : ∀ n, R.n₀ ≤ n → T n ≤ (∑ i, a i * T (r i n)) + g n) :
    ∀ n, T n ≤ C * M n := by
  apply Recurrence.le_of_sum_rec_le
    (a := a) (r := r) (toll := fun n => g n) (n₀ := R.n₀)
    (fun i => (R.a_pos i).le) base R.r_lt_n step
  intro n hn
  have htoll : g n ≤ C * g n := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hC (R.g_nonneg n (Nat.cast_nonneg n))
  calc
    (∑ i, a i * (C * M (r i n))) + g n
        ≤ (∑ i, a i * (C * M (r i n))) + C * g n := add_le_add le_rfl htoll
    _ = C * M n := by
      rw [R.h_rec n hn, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm _ _ _

/-- A natural-valued recursive cost upper bound inherits the official
Akra–Bazzi asymptotic upper bound of its exact comparison function. -/
theorem isBigO_of_nat_upper {T : Nat → Nat} {C : ℝ} (hC : 1 ≤ C)
    (base : ∀ n, n < R.n₀ → (T n : ℝ) ≤ C * M n)
    (step : ∀ n, R.n₀ ≤ n →
      (T n : ℝ) ≤ (∑ i, a i * (T (r i n) : ℝ)) + g n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ)) (asympBound g a b) := by
  have hbound := R.le_mul_of_rec_le hC base step
  have hO : Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ)) M := by
    apply Asymptotics.IsBigO.of_bound C
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Real.norm_natCast, Real.norm_of_nonneg (R.T_nonneg n)] using hbound n
  exact hO.trans R.isBigO_asympBound

end AkraBazziRecurrence
