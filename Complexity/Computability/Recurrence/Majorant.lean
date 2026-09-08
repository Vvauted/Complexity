/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Recurrence.AkraBazzi
import Mathlib.Data.Nat.Init

/-!
# Exact comparison recurrences for recursive upper bounds

`majorant` uses the standard natural-number strong recursor to solve the
comparison recurrence. Its base values are `max 1 (T n)`, so every base case
is positive and covers the corresponding natural cost, without a separate
uniform-base estimate from the caller.

The function is an arithmetic comparison object, not another program or a
definition of machine costs. `isBigO_of_sum_rec_le` requires the original
recursive cost inequality and all of mathlib's Akra–Bazzi hypotheses. It
concludes only an upper bound, not `IsTheta` or program correctness.
-/

namespace Recurrence

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The exact finite-branch comparison recurrence, with positive base values
covering every cost below the given threshold. -/
noncomputable def majorant (T : Nat → Nat) (a : ι → ℝ) (r : ι → Nat → Nat)
    (g : ℝ → ℝ) (n₀ : Nat) (smaller : ∀ i n, n₀ ≤ n → r i n < n) (n : Nat) : ℝ :=
  Nat.strongRecOn' n fun n recur =>
    if hn : n < n₀ then max 1 (T n : ℝ)
    else (∑ i, a i * recur (r i n) (smaller i n (Nat.le_of_not_gt hn))) + g n

variable {T : Nat → Nat} {a b : ι → ℝ} {r : ι → Nat → Nat}
variable {g : ℝ → ℝ} {n₀ : Nat}

/-- Unfold the standard recursor once, without unfolding recursive children. -/
theorem majorant_eq (smaller : ∀ i n, n₀ ≤ n → r i n < n) (n : Nat) :
    majorant T a r g n₀ smaller n =
      if n < n₀ then max 1 (T n : ℝ)
      else (∑ i, a i * majorant T a r g n₀ smaller (r i n)) + g n := by
  rw [majorant, Nat.strongRecOn'_beta]
  rfl

/-- Every base value covers its particular input cost. -/
theorem majorant_of_lt (smaller : ∀ i n, n₀ ≤ n → r i n < n)
    {n : Nat} (hn : n < n₀) :
    majorant T a r g n₀ smaller n = max 1 (T n : ℝ) := by
  rw [majorant_eq, if_pos hn]

/-- Above the threshold, the comparison function satisfies the exact
recurrence required by the upstream theorem. -/
theorem majorant_of_le (smaller : ∀ i n, n₀ ≤ n → r i n < n)
    {n : Nat} (hn : n₀ ≤ n) :
    majorant T a r g n₀ smaller n =
      (∑ i, a i * majorant T a r g n₀ smaller (r i n)) + g n := by
  rw [majorant_eq, if_neg (Nat.not_lt_of_ge hn)]

/-- Base positivity is provided by construction, including zero input cost. -/
theorem majorant_pos_base (smaller : ∀ i n, n₀ ≤ n → r i n < n)
    {n : Nat} (hn : n < n₀) : 0 < majorant T a r g n₀ smaller n := by
  rw [majorant_of_lt smaller hn]
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The original upper recurrence is dominated on every input, not only
eventually. This reuses the finite-branch supersolution comparison. -/
theorem le_majorant (smaller : ∀ i n, n₀ ≤ n → r i n < n)
    (ha : ∀ i, 0 ≤ a i)
    (step : ∀ n, n₀ ≤ n →
      (T n : ℝ) ≤ (∑ i, a i * (T (r i n) : ℝ)) + g n) :
    ∀ n, (T n : ℝ) ≤ majorant T a r g n₀ smaller n := by
  exact le_of_sum_rec_le (a := a) (r := r) (toll := fun n => g n) (n₀ := n₀) ha
    (fun n hn => by
      rw [majorant_of_lt smaller hn]
      exact le_max_right _ _) smaller step
    (fun n hn => (majorant_of_le smaller (n := n) hn).symm.le)

/-- Package the constructed exact recurrence in the official structure.
All coefficient, rounding and regularity assumptions are unchanged. -/
def majorant_akraBazzi [Nonempty ι]
    (smaller : ∀ i n, n₀ ≤ n → r i n < n) (hn₀ : 0 < n₀)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hb₁ : ∀ i, b i < 1)
    (hg : ∀ x ≥ 0, 0 ≤ g x) (hgrowth : AkraBazziRecurrence.GrowsPolynomially g)
    (hround : ∀ i, Asymptotics.IsLittleO Filter.atTop
      (fun n : Nat => (r i n : ℝ) - b i * n)
      (fun n : Nat => (n : ℝ) / (Real.log n) ^ 2)) :
    AkraBazziRecurrence (majorant T a r g n₀ smaller) g a b r where
  n₀ := n₀
  n₀_gt_zero := hn₀
  a_pos := ha
  b_pos := hb
  b_lt_one := hb₁
  g_nonneg := hg
  g_grows_poly := hgrowth
  h_rec n hn := majorant_of_le smaller (n := n) hn
  T_gt_zero' n hn := majorant_pos_base smaller (n := n) hn
  r_lt_n := smaller
  dist_r_b := hround

/-- Apply the official Akra–Bazzi upper bound to a natural cost satisfying
only an upper recurrence. No exact control function or base bound is required
from the caller: both are supplied by `majorant`. -/
theorem isBigO_of_sum_rec_le [Nonempty ι]
    (smaller : ∀ i n, n₀ ≤ n → r i n < n) (hn₀ : 0 < n₀)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hb₁ : ∀ i, b i < 1)
    (hg : ∀ x ≥ 0, 0 ≤ g x) (hgrowth : AkraBazziRecurrence.GrowsPolynomially g)
    (hround : ∀ i, Asymptotics.IsLittleO Filter.atTop
      (fun n : Nat => (r i n : ℝ) - b i * n)
      (fun n : Nat => (n : ℝ) / (Real.log n) ^ 2))
    (step : ∀ n, n₀ ≤ n →
      (T n : ℝ) ≤ (∑ i, a i * (T (r i n) : ℝ)) + g n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (AkraBazziRecurrence.asympBound g a b) := by
  let R := majorant_akraBazzi (T := T) smaller hn₀ ha hb hb₁ hg hgrowth hround
  apply R.isBigO_of_nat_upper (C := 1) le_rfl ?_ step
  intro n hn
  simpa only [one_mul] using le_majorant smaller (fun i => (ha i).le) step n

end Recurrence
