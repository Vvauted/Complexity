/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform bounds for input-dependent finite cost sums

The index set may depend on the input and need not have bounded cardinality.
The coefficient is chosen once, outside both the input and summand quantifiers;
one common eventual condition must then bound every currently selected summand.
Individual per-index `IsBigO` hypotheses do not supply this uniformity. For a
fixed index set, use mathlib's `Asymptotics.IsBigO.sum` directly instead.

Both cost and majorant are natural-valued, so the real casts in mathlib's
`IsBigO` have no sign or cancellation issue. The input type and filter are
arbitrary. These are eventual arithmetic bounds, not all-input bounds or
machine execution certificates: the summands must separately account for the
verified work being analyzed.

For a variable-length range, take `indices x := Finset.range (length x)` in
`isBigO_sum_card_mul_of_uniform` and simplify with `Finset.card_range`. To
replace the cardinality or common growth by asymptotically larger bounds, use
mathlib's `Asymptotics.IsBigO.mul` and `Asymptotics.IsBigO.trans` on the result.
No new sum or asymptotic relation is introduced here.
-/

namespace Asymptotics

open Filter Finset

/-- A uniform eventual bound on every selected term controls the sum over an
input-dependent finite set. The common majorant may itself vary with the index. -/
theorem isBigO_sum_of_uniform
    {α ι : Type*} {l : Filter α} {indices : α → Finset ι}
    {cost majorant : α → ι → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ i ∈ indices x,
      (cost x i : ℝ) ≤ C * (majorant x i : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => ((∑ i ∈ indices x, cost x i : Nat) : ℝ))
      (fun x => ((∑ i ∈ indices x, majorant x i : Nat) : ℝ)) := by
  obtain ⟨C, hC⟩ := uniform
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with x hx
  simp only [Real.norm_natCast]
  simpa only [Nat.cast_sum, Finset.mul_sum] using
    (Finset.sum_le_sum hx)

/-- Uniformly charging each visited index against the same growth function
gives a total bound by the number of visits times that growth. Empty index sets
and a zero growth value are allowed; no positivity hypothesis is needed. -/
theorem isBigO_sum_card_mul_of_uniform
    {α ι : Type*} {l : Filter α} {indices : α → Finset ι}
    {cost : α → ι → Nat} {growth : α → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ i ∈ indices x,
      (cost x i : ℝ) ≤ C * (growth x : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => ((∑ i ∈ indices x, cost x i : Nat) : ℝ))
      (fun x => (((indices x).card * growth x : Nat) : ℝ)) := by
  simpa only [Finset.sum_const, Nat.nsmul_eq_mul] using
    (isBigO_sum_of_uniform (majorant := fun x _ => growth x) uniform)

end Asymptotics
