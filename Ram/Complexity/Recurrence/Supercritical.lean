/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity.Recurrence.Growth
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Supercritical power tolls

The finite power-sum estimate combines mathlib's ordinary finite-sum bound
with its sum/integral comparison and exact real-power integral. Negative
exponents are integrated only from one; the value of `0 ^ exponent` is never
used to claim monotonicity through zero.

The resulting Akra–Bazzi upper bound retains the normalized toll's finite
zero term. All recurrence and regularity assumptions stay in the existing
upstream structure, and no machine cost or growth relation is redefined.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Ram.Recurrence

/-- A finite positive-integer power sum, for every natural endpoint. This
is the elementary comparison needed when the normalized toll exponent is
greater than `-1`; it includes fractional negative exponents. -/
theorem sum_Icc_nat_rpow_le {exponent : ℝ} (hexponent : -1 < exponent) (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ exponent) ≤
      (1 + 1 / (exponent + 1)) * (n : ℝ) ^ (exponent + 1) := by
  have hpos : 0 < exponent + 1 := by linarith
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow hpos.ne']
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpNonneg : 0 ≤ (n : ℝ) ^ (exponent + 1) := Real.rpow_nonneg hnReal.le _
  have hpOne : 1 ≤ (n : ℝ) ^ (exponent + 1) :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hnOne) hpos.le
  have hInv : 0 ≤ 1 / (exponent + 1) := one_div_nonneg.mpr hpos.le
  by_cases hnonneg : 0 ≤ exponent
  · calc
      (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ exponent) ≤
          ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) ^ exponent :=
        Finset.sum_le_sum fun k hk => Real.rpow_le_rpow (Nat.cast_nonneg k)
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2) hnonneg
      _ = (n : ℝ) * (n : ℝ) ^ exponent := by simp [Nat.card_Icc, nsmul_eq_mul]
      _ = (n : ℝ) ^ (exponent + 1) := by rw [Real.rpow_add_one hnReal.ne']; ring
      _ ≤ (1 + 1 / (exponent + 1)) * (n : ℝ) ^ (exponent + 1) := by
        nlinarith [mul_nonneg hInv hpNonneg]
  · have anti : AntitoneOn (fun x : ℝ => x ^ exponent) (Set.Icc (1 : ℝ) (n : ℝ)) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (le_of_not_ge hnonneg)).mono
        (fun _ hx => lt_of_lt_of_le zero_lt_one hx.1)
    have integralBound := AntitoneOn.sum_le_integral_Ico
      (f := fun x : ℝ => x ^ exponent) hnOne
      (by simpa only [Nat.cast_one] using anti)
    simp only [Nat.cast_one] at integralBound
    calc
      (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ exponent) =
          (∑ k ∈ Finset.Ico 1 n, ((k + 1 : Nat) : ℝ) ^ exponent) + 1 := by
        rw [← Finset.sum_erase_add _ _ (Finset.left_mem_Icc.mpr hnOne),
          Finset.Icc_erase_left]
        simp only [Nat.cast_one, Real.one_rpow]
        rw [Finset.sum_Ico_add' (fun k : Nat => (k : ℝ) ^ exponent) 1 n 1]
        rfl
      _ ≤ (∫ x in (1 : ℝ)..(n : ℝ), x ^ exponent) + 1 := by linarith
      _ = ((n : ℝ) ^ (exponent + 1) - 1) / (exponent + 1) + 1 := by
        rw [integral_rpow (Or.inl hexponent), Real.one_rpow]
      _ ≤ (1 + 1 / (exponent + 1)) * (n : ℝ) ^ (exponent + 1) := by
        simp only [div_eq_mul_inv, one_mul] at hInv ⊢
        nlinarith

end Ram.Recurrence

namespace AkraBazziRecurrence

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {M : Nat → ℝ} {g : ℝ → ℝ} {a b : ι → ℝ} {r : ι → Nat → Nat}
variable (R : AkraBazziRecurrence M g a b r)

include R

/-- A power toll strictly above the characteristic power bounds the official
comparison expression by that larger power. Only positive integer tolls are
constrained; the normalization's zero term remains a finite constant. -/
theorem asympBound_isBigO_rpow_of_toll_gt {q exponent C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1) (hgt : q < exponent)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ exponent) :
    asympBound g a b =O[atTop] (fun n : Nat => (n : ℝ) ^ exponent) := by
  have hC : 0 ≤ C := calc
    0 ≤ g 1 := R.g_nonneg 1 zero_le_one
    _ ≤ C := by simpa only [Nat.cast_one, Real.one_rpow, mul_one] using htoll 1 Nat.one_pos
  let d := fun n : Nat => g n / (n : ℝ) ^ (q + 1)
  have dNonneg (n : Nat) : 0 ≤ d n :=
    div_nonneg (R.g_nonneg n (Nat.cast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have dBound (n : Nat) (hn : 0 < n) : d n ≤ C * (n : ℝ) ^ (exponent - (q + 1)) := by
    have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    calc
      d n ≤ (C * (n : ℝ) ^ exponent) / (n : ℝ) ^ (q + 1) :=
        div_le_div_of_nonneg_right (htoll n hn) (Real.rpow_nonneg hnReal.le _)
      _ = C * (n : ℝ) ^ (exponent - (q + 1)) := by
        rw [Real.rpow_sub hnReal exponent (q + 1), mul_div_assoc]
  have partialBound (n : Nat) : (∑ k ∈ Finset.range n, d k) ≤
      C * (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ (exponent - (q + 1))) + d 0 := by
    calc
      (∑ k ∈ Finset.range n, d k) ≤ (∑ k ∈ Finset.range n, d k) + d n :=
        le_add_of_nonneg_right (dNonneg n)
      _ = ∑ k ∈ Finset.range (n + 1), d k := (Finset.sum_range_succ d n).symm
      _ = (∑ k ∈ Finset.range n, d (k + 1)) + d 0 := Finset.sum_range_succ' d n
      _ ≤ (∑ k ∈ Finset.range n, C * ((k + 1 : Nat) : ℝ) ^ (exponent - (q + 1))) + d 0 := by
        have bound := Finset.sum_le_sum
          (s := Finset.range n) (fun k _ => dBound (k + 1) (Nat.succ_pos k))
        linarith
      _ = C * (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ (exponent - (q + 1))) + d 0 := by
        rw [← Finset.mul_sum, Finset.range_eq_Ico,
          Finset.sum_Ico_add' (fun k : Nat => (k : ℝ) ^ (exponent - (q + 1))) 0 n 1]
        simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]
  have hfactor : (fun n : Nat => 1 + ∑ k ∈ Finset.range n, d k)
      =O[atTop] (fun n : Nat => (n : ℝ) ^ (exponent - q)) := by
    apply IsBigO.of_bound (1 + |d 0| + C * (1 + 1 / (exponent - q)))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpower : 0 ≤ (n : ℝ) ^ (exponent - q) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hpOne : 1 ≤ (n : ℝ) ^ (exponent - q) :=
      Real.one_le_rpow (Nat.one_le_cast.mpr hn) (sub_nonneg.mpr hgt.le)
    have powers := Ram.Recurrence.sum_Icc_nat_rpow_le
      (exponent := exponent - (q + 1)) (by linarith) n
    have exponentEq : exponent - (q + 1) + 1 = exponent - q := by ring
    rw [exponentEq] at powers
    have scaled := mul_le_mul_of_nonneg_left powers hC
    have innerNonneg : 0 ≤ 1 + ∑ k ∈ Finset.range n, d k :=
      add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => dNonneg k))
    have baseBound : 1 + |d 0| ≤ (1 + |d 0|) * (n : ℝ) ^ (exponent - q) := by
      nlinarith [mul_nonneg (abs_nonneg (d 0)) (sub_nonneg.mpr hpOne)]
    rw [Real.norm_of_nonneg innerNonneg, Real.norm_of_nonneg hpower]
    have hpartial := partialBound n
    have habs := le_abs_self (d 0)
    nlinarith
  have heq : asympBound g a b =
      fun n : Nat => (n : ℝ) ^ q * (1 + ∑ k ∈ Finset.range n, d k) :=
    funext (R.asympBound_eq_of_sum_eq_one hq)
  rw [heq]
  simpa only [Pi.mul_apply] using
    IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow q (exponent - q) exponent
      (isBigO_refl (fun n : Nat => (n : ℝ) ^ q) atTop) hfactor (by linarith)

/-- Transfer the supercritical power upper bound to the exact comparison
recurrence, including a recurrence packaged by the existing majorant API. -/
theorem isBigO_rpow_of_toll_gt {q exponent C : ℝ}
    (hq : (∑ i, a i * (b i) ^ q) = 1) (hgt : q < exponent)
    (htoll : ∀ n : Nat, 0 < n → g n ≤ C * (n : ℝ) ^ exponent) :
    M =O[atTop] (fun n : Nat => (n : ℝ) ^ exponent) :=
  R.isBigO_asympBound.trans (R.asympBound_isBigO_rpow_of_toll_gt hq hgt htoll)

end AkraBazziRecurrence
