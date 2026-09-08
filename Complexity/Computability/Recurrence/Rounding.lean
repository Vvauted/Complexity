/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded subproblem sizes for Akra–Bazzi

These lemmas supply the rounding-error and strictly-smaller-subproblem hypotheses
used by mathlib's `AkraBazziRecurrence`. The error estimates reuse mathlib's
floor/ceiling bounds and logarithmic asymptotics; no alternative recurrence or
growth notion is introduced.
-/

open Filter Asymptotics

namespace Recurrence

/-- An eventually bounded error meets the rounding-error condition in the
official Akra–Bazzi theorem. -/
theorem isLittleO_div_log_sq_of_bounded {error : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ‖error n‖ ≤ C) :
    error =o[atTop] (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  have herror : error =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound C
    simpa only [norm_one, mul_one] using hbound
  have hlog : (fun n : ℕ => (Real.log n) ^ 2) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnonzero : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
    exact pow_ne_zero _ (ne_of_gt (Real.log_pos hn'))
  apply (isLittleO_mul_iff_isLittleO_div hnonzero).mp
  simpa only [mul_one] using hlog.mul_isBigO herror

/-- Rounding a nonnegative real fraction of the input size down has admissible
Akra–Bazzi error. -/
theorem floor_mul_dist {b : ℝ} (hb : 0 ≤ b) :
    (fun n : ℕ => (⌊b * n⌋₊ : ℝ) - b * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  apply isLittleO_div_log_sq_of_bounded (C := 1)
  apply Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs] using
    Nat.abs_floor_sub_le (mul_nonneg hb (Nat.cast_nonneg n))

/-- Rounding a nonnegative real fraction of the input size up has admissible
Akra–Bazzi error. This alone does not assert that the branch shrinks. -/
theorem ceil_mul_dist {b : ℝ} (hb : 0 ≤ b) :
    (fun n : ℕ => (⌈b * n⌉₊ : ℝ) - b * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  apply isLittleO_div_log_sq_of_bounded (C := 1)
  apply Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs] using
    Nat.abs_ceil_sub_le (mul_nonneg hb (Nat.cast_nonneg n))

/-- A floor-rounded proper fraction strictly shrinks at every positive input
size, so a recurrence may use cutoff `1`. -/
theorem floor_mul_lt {b : ℝ} (hb : 0 ≤ b) (hb₁ : b < 1)
    {n : ℕ} (hn : 0 < n) : ⌊b * n⌋₊ < n := by
  apply (Nat.floor_lt (mul_nonneg hb (Nat.cast_nonneg n))).mpr
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right hb₁ (by exact_mod_cast hn : (0 : ℝ) < n)

/-- Natural-number division has the rounding error of coefficient `1 / d`.
The error statement is valid even at `d = 0`; valid Akra–Bazzi coefficients
require `1 < d`, as recorded by `div_split_conditions`. -/
theorem div_dist (d : ℕ) :
    (fun n : ℕ => ((n / d : ℕ) : ℝ) - (d : ℝ)⁻¹ * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  have hfloor (n : ℕ) : ⌊(d : ℝ)⁻¹ * n⌋₊ = n / d := by
    simpa only [mul_comm (d : ℝ)⁻¹, ← div_eq_mul_inv] using
      (Nat.floor_div_eq_div (K := ℝ) n d)
  simpa only [hfloor] using floor_mul_dist (inv_nonneg.mpr (Nat.cast_nonneg d))

/-- The complementary branch `n - n / d` has coefficient `1 - 1 / d`.
Its error is the negative of the division branch's error. -/
theorem sub_div_dist (d : ℕ) :
    (fun n : ℕ => ((n - n / d : ℕ) : ℝ) - (1 - (d : ℝ)⁻¹) * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  apply (div_dist d).neg_left.congr_left
  intro n
  rw [Nat.cast_sub (Nat.div_le_self n d)]
  ring

/-- Both branches of the split `n / d`, `n - n / d` meet the coefficient,
shrinking, and rounding hypotheses for Akra–Bazzi, with explicit cutoff `d`.
Below that cutoff, the complementary branch need not shrink. -/
theorem div_split_conditions {d : ℕ} (hd : 1 < d) :
    (d : ℝ)⁻¹ ∈ Set.Ioo 0 1 ∧
    1 - (d : ℝ)⁻¹ ∈ Set.Ioo 0 1 ∧
    (∀ n : ℕ, d ≤ n → n / d < n ∧ n - n / d < n) ∧
    ((fun n : ℕ => ((n / d : ℕ) : ℝ) - (d : ℝ)⁻¹ * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2)) ∧
    ((fun n : ℕ => ((n - n / d : ℕ) : ℝ) - (1 - (d : ℝ)⁻¹) * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2)) := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := zero_lt_one.trans hd'
  have hinv₀ : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hd₀
  have hinv₁ : (d : ℝ)⁻¹ < 1 := (inv_lt_one₀ hd₀).mpr hd'
  refine ⟨⟨hinv₀, hinv₁⟩, ⟨sub_pos.mpr hinv₁, sub_lt_self _ hinv₀⟩,
    ?_, div_dist d, sub_div_dist d⟩
  intro n hn
  have hdpos : 0 < d := Nat.zero_lt_one.trans hd
  have hnpos : 0 < n := hdpos.trans_le hn
  exact ⟨Nat.div_lt_self hnpos hd, Nat.sub_lt hnpos (Nat.div_pos hn hdpos)⟩

end Recurrence
