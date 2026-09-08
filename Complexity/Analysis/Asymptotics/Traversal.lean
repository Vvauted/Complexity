/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform asymptotic bounds for lists of visits

The input-dependent list records occurrences, so repeated visits are counted repeatedly.
A single eventual coefficient bounds every selected occurrence; pointwise bounds with
unrelated coefficients would not suffice. The results use ordinary list sums and mathlib's
`Asymptotics.IsBigO`, without introducing an execution model.

## Main results

- `Asymptotics.isBigO_list_sum_of_uniform`: sum a common per-occurrence comparison.
- `Asymptotics.isBigO_list_sum_length_mul_of_uniform`: bound by length times common growth.
-/

namespace Asymptotics

open Filter

/-- A uniform bound on every visit controls the sum, including repeated visits
and inputs with an empty visit list. The same eventual condition covers all
currently selected occurrences. -/
theorem isBigO_list_sum_of_uniform
    {α ι : Type*} {l : Filter α} {visits : α → List ι}
    {cost majorant : α → ι → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ a ∈ visits x,
      (cost x a : ℝ) ≤ C * (majorant x a : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => (((visits x).map (cost x)).sum : ℝ))
      (fun x => (((visits x).map (majorant x)).sum : ℝ)) := by
  obtain ⟨C, hC⟩ := uniform
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with x hx
  simp only [Real.norm_natCast]
  simpa only [Nat.cast_list_sum, List.map_map,
    Function.comp_def, List.sum_map_mul_left] using List.sum_le_sum hx

/-- A common per-visit growth bound multiplies the length of the visit list,
not the number of distinct values. No decidable equality on visits is needed. -/
theorem isBigO_list_sum_length_mul_of_uniform
    {α ι : Type*} {l : Filter α} {visits : α → List ι}
    {cost : α → ι → Nat} {growth : α → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ a ∈ visits x,
      (cost x a : ℝ) ≤ C * (growth x : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => (((visits x).map (cost x)).sum : ℝ))
      (fun x => (((visits x).length * growth x : Nat) : ℝ)) := by
  simpa only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul] using
    (isBigO_list_sum_of_uniform (majorant := fun x _ => growth x) uniform)

end Asymptotics
