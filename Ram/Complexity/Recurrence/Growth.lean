/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity.Recurrence.AkraBazzi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-!
# Standard growth bounds for the Akra–Bazzi comparison expression

A proposed exponent is identified by the upstream uniqueness theorem, not by
unfolding its inverse-function definition. Summability of the normalized toll
makes its partial sums bounded. A critical toll is instead bounded by the
upstream harmonic-number estimate and contributes one logarithmic factor.

The critical hypothesis concerns positive integer inputs only. The term at
zero in mathlib's sum is retained as a finite constant, including when the
exponent makes its denominator `0 ^ 0`. No assumption silently deletes it.

These are upper asymptotic bounds for the existing comparison expression and
recurrence. A program still needs its measured-execution and recurrence proof;
no runtime certificate or matching lower bound is supplied here.
-/

namespace AkraBazziRecurrence

open Filter Asymptotics
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {M : Nat → ℝ} {g : ℝ → ℝ} {a b : ι → ℝ} {r : ι → Nat → Nat}
variable (R : AkraBazziRecurrence M g a b r)

include R

/-- Identify the characteristic exponent by a checked coefficient equation. -/
theorem p_eq_of_sum_eq_one {q : ℝ} (hq : (∑ i, a i * (b i) ^ q) = 1) :
    p a b = q :=
  R.injective_sumCoeffsExp (R.sumCoeffsExp_p_eq_one.trans hq.symm)

/-- Rewrite the official comparison expression using an identified exponent.
The finite sum still starts at zero, exactly as in mathlib. -/
theorem asympBound_eq_of_sum_eq_one {q : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1) (n : Nat) :
    asympBound g a b n = (n : ℝ) ^ q *
      (1 + ∑ k ∈ Finset.range n, g k / (k : ℝ) ^ (q + 1)) := by
  rw [asympBound_def', R.p_eq_of_sum_eq_one hq]

/-- A summable normalized toll contributes only a bounded multiplicative
factor to the characteristic power. Summability includes the finite zero term. -/
theorem asympBound_isBigO_rpow_of_summable {q : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1)
    (hsum : Summable (fun n : Nat => g n / (n : ℝ) ^ (q + 1))) :
    asympBound g a b =O[atTop] (fun n : Nat => (n : ℝ) ^ q) := by
  have hfactor :
      (fun n : Nat => 1 + ∑ k ∈ Finset.range n, g k / (k : ℝ) ^ (q + 1))
        =O[atTop] (fun _ : Nat => (1 : ℝ)) :=
    (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).isBigO_one ℝ
  have heq : asympBound g a b = fun n : Nat => (n : ℝ) ^ q *
      (1 + ∑ k ∈ Finset.range n, g k / (k : ℝ) ^ (q + 1)) :=
    funext (R.asympBound_eq_of_sum_eq_one hq)
  rw [heq]
  simpa only [Pi.mul_apply, mul_one] using
    (isBigO_refl (fun n : Nat => (n : ℝ) ^ q) atTop).mul hfactor

/-- The exact comparison recurrence inherits the power upper bound. This
also applies to an upstream recurrence packaged from `majorant`. -/
theorem isBigO_rpow_of_summable {q : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1)
    (hsum : Summable (fun n : Nat => g n / (n : ℝ) ^ (q + 1))) :
    M =O[atTop] (fun n : Nat => (n : ℝ) ^ q) :=
  R.isBigO_asympBound.trans (R.asympBound_isBigO_rpow_of_summable hq hsum)

/-- A toll whose power is strictly below the characteristic power has a
summable normalization. The standard eventual comparison test permits its
arbitrary finite value at zero; no new series comparison is proved here. -/
theorem normalized_toll_summable_of_lt {q exponent C : ℝ} (hlt : exponent < q)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ exponent) :
    Summable (fun n : Nat => g n / (n : ℝ) ^ (q + 1)) := by
  have hseries : Summable (fun n : Nat => (n : ℝ) ^ (exponent - (q + 1))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (hseries.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Real.norm_of_nonneg (div_nonneg (R.g_nonneg n (Nat.cast_nonneg n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
  calc
    _ ≤ (C * (n : ℝ) ^ exponent) / (n : ℝ) ^ (q + 1) :=
      div_le_div_of_nonneg_right (htoll n hn) (Real.rpow_nonneg hnReal.le _)
    _ = C * (n : ℝ) ^ (exponent - (q + 1)) := by
      rw [Real.rpow_sub hnReal exponent (q + 1), mul_div_assoc]

/-- A strictly subcritical power toll leaves the comparison expression
bounded by the characteristic power itself. -/
theorem asympBound_isBigO_rpow_of_toll_lt {q exponent C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1) (hlt : exponent < q)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ exponent) :
    asympBound g a b =O[atTop] (fun n : Nat => (n : ℝ) ^ q) :=
  R.asympBound_isBigO_rpow_of_summable hq (R.normalized_toll_summable_of_lt hlt htoll)

/-- Transfer the subcritical upper bound to the exact comparison recurrence. -/
theorem isBigO_rpow_of_toll_lt {q exponent C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1) (hlt : exponent < q)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ exponent) :
    M =O[atTop] (fun n : Nat => (n : ℝ) ^ q) :=
  R.isBigO_asympBound.trans (R.asympBound_isBigO_rpow_of_toll_lt hq hlt htoll)

/-- A critical toll bounded by `C * n^q` on positive integer inputs contributes
at most a logarithmic factor. No condition on its value at zero is added.
Nonnegativity of `C` follows from the toll hypothesis at one and the existing
Akra–Bazzi nonnegativity assumption. -/
theorem asympBound_isBigO_rpow_mul_one_add_log_of_le {q C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ q) :
    asympBound g a b =O[atTop]
      (fun n : Nat => (n : ℝ) ^ q * (1 + Real.log (n : ℝ))) := by
  have hC : 0 ≤ C := calc
    0 ≤ g 1 := R.g_nonneg 1 zero_le_one
    _ ≤ C := by simpa only [Nat.cast_one, Real.one_rpow, mul_one] using htoll 1 Nat.one_pos
  let d := fun n : Nat => g n / (n : ℝ) ^ (q + 1)
  have dNonneg (n : Nat) : 0 ≤ d n :=
    div_nonneg (R.g_nonneg n (Nat.cast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have dBound (n : Nat) (hn : 0 < n) : d n ≤ C * (n : ℝ)⁻¹ := by
    have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hp : (n : ℝ) ^ q ≠ 0 := (Real.rpow_pos_of_pos hnReal q).ne'
    calc
      d n ≤ (C * (n : ℝ) ^ q) / (n : ℝ) ^ (q + 1) :=
        div_le_div_of_nonneg_right (htoll n hn) (Real.rpow_nonneg hnReal.le _)
      _ = C * (n : ℝ)⁻¹ := by
        rw [Real.rpow_add_one hnReal.ne' q]
        field_simp
  have partialBound (n : Nat) :
      (∑ k ∈ Finset.range n, d k) ≤ C * (harmonic n : ℝ) + d 0 := by
    calc
      (∑ k ∈ Finset.range n, d k) ≤ (∑ k ∈ Finset.range n, d k) + d n :=
        le_add_of_nonneg_right (dNonneg n)
      _ = ∑ k ∈ Finset.range (n + 1), d k := (Finset.sum_range_succ d n).symm
      _ = (∑ k ∈ Finset.range n, d (k + 1)) + d 0 := Finset.sum_range_succ' d n
      _ ≤ (∑ k ∈ Finset.range n, C * ((k + 1 : Nat) : ℝ)⁻¹) + d 0 := by
        have bound := Finset.sum_le_sum
          (s := Finset.range n) (fun k _ => dBound (k + 1) (Nat.succ_pos k))
        linarith
      _ = C * (harmonic n : ℝ) + d 0 := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
  apply IsBigO.of_bound (1 + |d 0| + C)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have hpower : 0 ≤ (n : ℝ) ^ q := Real.rpow_nonneg (Nat.cast_nonneg n) q
  have innerNonneg : 0 ≤ 1 + ∑ k ∈ Finset.range n, d k :=
    add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => dNonneg k))
  have innerBound : 1 + ∑ k ∈ Finset.range n, d k ≤
      (1 + |d 0| + C) * (1 + Real.log (n : ℝ)) := by
    have hharm := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hC
    have habs := le_abs_self (d 0)
    have habslog := mul_nonneg (abs_nonneg (d 0)) hlog
    have hpartial := partialBound n
    nlinarith
  rw [R.asympBound_eq_of_sum_eq_one hq]
  change ‖(n : ℝ) ^ q * (1 + ∑ k ∈ Finset.range n, d k)‖ ≤
    (1 + |d 0| + C) * ‖(n : ℝ) ^ q * (1 + Real.log (n : ℝ))‖
  rw [Real.norm_of_nonneg (mul_nonneg hpower innerNonneg),
    Real.norm_of_nonneg (mul_nonneg hpower (by linarith))]
  calc
    _ ≤ (n : ℝ) ^ q * ((1 + |d 0| + C) * (1 + Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left innerBound hpower
    _ = _ := by ring

/-- Transfer the critical upper bound to the exact comparison recurrence. -/
theorem isBigO_rpow_mul_one_add_log_of_le {q C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ q) :
    M =O[atTop] (fun n : Nat => (n : ℝ) ^ q * (1 + Real.log (n : ℝ))) :=
  R.isBigO_asympBound.trans (R.asympBound_isBigO_rpow_mul_one_add_log_of_le hq htoll)

end AkraBazziRecurrence
