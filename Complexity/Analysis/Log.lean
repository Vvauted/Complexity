/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Binary logarithms of disjoint sizes

The logarithms of two positive sizes whose sum fits in a containing size leave
two units of slack. This elementary consequence of `(a - b)² ≥ 0` is useful for
potential arguments; the logarithms are mathematical quantities, not executable
operations with an assigned cost.
-/

namespace Real

/-- The binary logarithms of two positive summands leave two units of slack. -/
theorem logb_add_logb_add_two_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logb 2 a + logb 2 b + 2 ≤ 2 * logb 2 (a + b) := by
  have hprod : (2 * a) * (2 * b) ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have h := logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (2 * a) * (2 * b)) hprod
  rw [logb_mul (by positivity : (2 : ℝ) * a ≠ 0)
      (by positivity : (2 : ℝ) * b ≠ 0),
    logb_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne',
    logb_mul (by norm_num : (2 : ℝ) ≠ 0) hb.ne',
    logb_pow, logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  norm_num at h
  linarith

/-- Two positive sizes contained in a third satisfy the binary-logarithm bound. -/
theorem logb_add_logb_add_two_le_of_add_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ c) :
    logb 2 a + logb 2 b + 2 ≤ 2 * logb 2 c := by
  exact (logb_add_logb_add_two_le ha hb).trans
    (mul_le_mul_of_nonneg_left
      (logb_le_logb_of_le (by norm_num) (add_pos ha hb) hab) (by norm_num))

end Real
