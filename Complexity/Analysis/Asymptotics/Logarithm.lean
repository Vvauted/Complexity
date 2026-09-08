/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic logarithmic bounds on natural-valued functions

`Asymptotics.isBigO_log2_of_le_clog` turns an all-input affine bound in the shifted
ceiling logarithm into mathlib's asymptotic bound in the binary floor logarithm.
This theorem analyzes a numerical function; it assumes no machine or execution relation.
-/

namespace Asymptotics

/-- An all-input affine ceiling-log budget gives the standard floor-log
asymptotic bound. Setup and termination costs may be included in `b`; no
condition on their value or on the small-input costs is dropped from `bound`.
This is arithmetic analysis of a proved budget, not an execution theorem. -/
theorem isBigO_log2_of_le_clog {T : Nat → Nat} {a b : Nat}
    (bound : ∀ n, T n ≤ a * Nat.clog 2 (n + 1) + b) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (Nat.log2 n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((2 * a + b : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnonzero : n ≠ 0 := by omega
  have hlog : 1 ≤ Nat.log2 n := (Nat.le_log2 hnonzero).mpr (by simpa using hn)
  have ha : a ≤ a * Nat.log2 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hlog
  have hb : b ≤ b * Nat.log2 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hlog
  have hnat : T n ≤ (2 * a + b) * Nat.log2 n := by
    have h := bound n
    rw [Nat.clog_two_succ_eq_log2 hnonzero, Nat.mul_add, Nat.mul_one] at h
    simp only [Nat.add_mul, Nat.two_mul]
    omega
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr hnat : (T n : ℝ) ≤ (((2 * a + b) * Nat.log2 n : Nat) : ℝ))

end Asymptotics
