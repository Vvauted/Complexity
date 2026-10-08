/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.BigOperators

/-!
# Finite-support expectations of natural-valued functions

These facts concern mathlib probability mass functions only; they do not
depend on a language, machine model or program resource interface.
-/

namespace PMF

open scoped ENNReal

variable {α : Type*}

/-- A convenient author-side finiteness fact, not an assumption that every PMF
has finite expectation. No implementation or input law is changed. -/
theorem tsum_mul_natCast_lt_top_of_finite_support (law : PMF α)
    (finite : law.support.Finite) (cost : α → Nat) :
    (∑' x, law x * (cost x : ℝ≥0∞)) < ⊤ := by
  classical
  rw [tsum_eq_sum (s := finite.toFinset) (fun x outside => by
    have absent : x ∉ law.support := by simpa using outside
    rw [(law.apply_eq_zero_iff x).mpr absent, zero_mul])]
  exact ENNReal.sum_lt_top.mpr (fun x _ =>
    ENNReal.mul_lt_top (law.apply_lt_top x) (ENNReal.natCast_lt_top _))

end PMF
