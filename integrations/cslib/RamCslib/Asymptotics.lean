import Ram.Complexity
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Mathlib asymptotic analysis of a proved RAM time bound

`Asymptotics.IsBigO` below is mathlib's API, not a CSLib definition. It is
connected to an actual uniform RAM execution certificate: the program, input
encoding, admissible word widths, size function, and functional postcondition
are unchanged. Total correctness holds on all admissible inputs, including
inputs below the asymptotic threshold. The constant and threshold are uniform
in both the input and the word width.
-/

namespace Ram

/-- Use mathlib to simplify a proved whole-program time bound asymptotically,
without dropping the program's total functional-correctness obligations. -/
theorem UniformTimeBound.bigO_of_isBigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound growth : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    UniformBigO code encode admissible size post growth := by
  obtain ⟨c, hc, hcost⟩ := hO.exists_pos
  obtain ⟨constant, hconstant⟩ := exists_nat_gt c
  have hpositive : 0 < constant := by
    exact_mod_cast hc.trans hconstant
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp hcost.bound
  apply h.bigO (constant := constant) (threshold := threshold) hpositive
  intro n hn
  have hreal : (bound n : ℝ) ≤ c * (growth n : ℝ) := by
    simpa using hthreshold n hn
  have hrounded : (bound n : ℝ) ≤ (constant : ℝ) * (growth n : ℝ) :=
    hreal.trans (mul_le_mul_of_nonneg_right hconstant.le (Nat.cast_nonneg _))
  exact_mod_cast hrounded

end Ram
