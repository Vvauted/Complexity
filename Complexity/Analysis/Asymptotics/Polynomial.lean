/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Polynomial upper bounds on natural-valued functions

`IsPolynomiallyBounded f` uses mathlib's `Asymptotics.IsBigO`: the real-valued
cast of `f` is eventually bounded by some shifted power. Arithmetic closure
uses mathlib's asymptotic lemmas. The shift by one accommodates constants and
allows the asymptotic bound to yield an all-input natural-valued majorant.

`IsPolynomiallyBounded.exists_pos` extracts the concrete majorant needed by
machine proofs, including the finite prefix omitted by `IsBigO`. Constants do
not depend on an input, word width, or execution. A machine complexity claim
additionally supplies total correctness and an execution bound; closure of
growth functions alone does not compose RAM programs.
-/

namespace Asymptotics

/-- The executable prefix maximum of a natural-valued function. This supplies
a monotone resource bound without choosing witnesses from a proposition. -/
def monotoneHull (f : Nat → Nat) (n : Nat) : Nat :=
  (Finset.range (n + 1)).sup f

@[simp] theorem monotoneHull_zero (f : Nat → Nat) : monotoneHull f 0 = f 0 := by
  simp [monotoneHull]

@[simp] theorem monotoneHull_succ (f : Nat → Nat) (n : Nat) :
    monotoneHull f (n + 1) = max (monotoneHull f n) (f (n + 1)) := by
  unfold monotoneHull
  rw [Finset.range_add_one, Finset.sup_insert]
  exact Nat.max_comm _ _

/-- The prefix maximum majorizes the value at its upper endpoint. -/
theorem le_monotoneHull (f : Nat → Nat) (n : Nat) : f n ≤ monotoneHull f n := by
  exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- Enlarging the prefix cannot decrease its maximum. -/
theorem hull_monotone (f : Nat → Nat) {m n : Nat} (hmn : m ≤ n) :
    monotoneHull f m ≤ monotoneHull f n := by
  exact Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hmn 1))

/-- Any monotone majorant also bounds the prefix maximum. -/
theorem monotoneHull_le {f g : Nat → Nat} (hfg : ∀ n, f n ≤ g n)
    (hg : ∀ ⦃m n⦄, m ≤ n → g m ≤ g n) (n : Nat) :
    monotoneHull f n ≤ g n := by
  exact Finset.sup_le fun i hi =>
    (hfg i).trans (hg (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

/-- An already monotone bound does not change under the prefix maximum. -/
theorem monotoneHull_eq {f : Nat → Nat}
    (hf : ∀ ⦃m n⦄, m ≤ n → f m ≤ f n) (n : Nat) : monotoneHull f n = f n :=
  Nat.le_antisymm (monotoneHull_le (fun _ => Nat.le_refl _) hf n) (le_monotoneHull f n)

@[simp] theorem monotoneHull_const (c n : Nat) : monotoneHull (fun _ => c) n = c :=
  monotoneHull_eq (fun _ _ _ => Nat.le_refl _) n

@[simp] theorem monotoneHull_id (n : Nat) : monotoneHull (fun k => k) n = n :=
  monotoneHull_eq (fun _ _ h => h) n

@[simp] theorem monotoneHull_add_const (c n : Nat) :
    monotoneHull (fun k => k + c) n = n + c :=
  monotoneHull_eq (fun _ _ h => Nat.add_le_add_right h c) n

@[simp] theorem monotoneHull_const_mul (c n : Nat) :
    monotoneHull (fun k => c * k) n = c * n :=
  monotoneHull_eq (fun _ _ h => Nat.mul_le_mul_left c h) n

/-- A natural-valued function grows no faster than some polynomial, expressed
directly using mathlib's asymptotic relation. -/
def IsPolynomiallyBounded (f : Nat → Nat) : Prop :=
  ∃ k : Nat, Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
    (fun n => (((n + 1) ^ k : Nat) : ℝ))

/-- Recover an all-input natural budget from an eventual bound, with the same
exponent. The prefix maximum covers the values below the asymptotic threshold. -/
theorem isBigO_shifted_pow_iff {f : Nat → Nat} {k : Nat} :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
      (fun n => (((n + 1) ^ k : Nat) : ℝ)) ↔
    ∃ c : Nat, ∀ n, f n ≤ c * (n + 1) ^ k := by
  constructor
  · intro hO
    obtain ⟨c, _, hbound⟩ := hO.exists_pos
    obtain ⟨coefficient, hcoefficient⟩ := exists_nat_gt c
    obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp hbound.bound
    refine ⟨max coefficient (monotoneHull f threshold), ?_⟩
    intro n
    by_cases hn : threshold ≤ n
    · have hreal : (f n : ℝ) ≤ c * (((n + 1) ^ k : Nat) : ℝ) := by
        simpa only [Real.norm_natCast] using hthreshold n hn
      have hrounded : (f n : ℝ) ≤
          (coefficient : ℝ) * (((n + 1) ^ k : Nat) : ℝ) :=
        hreal.trans (mul_le_mul_of_nonneg_right hcoefficient.le (Nat.cast_nonneg _))
      have hnat : f n ≤ coefficient * (n + 1) ^ k := by exact_mod_cast hrounded
      exact hnat.trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
    · have hn' : n ≤ threshold := Nat.le_of_lt (Nat.lt_of_not_ge hn)
      have hprefix : f n ≤ max coefficient (monotoneHull f threshold) :=
        (le_monotoneHull f n).trans
          ((hull_monotone f hn').trans (Nat.le_max_right _ _))
      have hpow : 1 ≤ (n + 1) ^ k := Nat.one_le_pow k (n + 1) (Nat.zero_lt_succ n)
      have hmul := Nat.mul_le_mul_left (max coefficient (monotoneHull f threshold)) hpow
      exact hprefix.trans (by simpa only [Nat.mul_one] using hmul)
  · rintro ⟨c, hf⟩
    apply Asymptotics.IsBigO.of_bound (c : ℝ)
    apply Filter.Eventually.of_forall
    intro n
    have hreal : (f n : ℝ) ≤ (c : ℝ) * (((n + 1) ^ k : Nat) : ℝ) := by
      exact_mod_cast hf n
    simpa only [Real.norm_natCast] using hreal

/-- Polynomial boundedness unfolds to mathlib's `IsBigO` without a conversion. -/
theorem isPolynomiallyBounded_iff_exists_isBigO {f : Nat → Nat} :
    IsPolynomiallyBounded f ↔ ∃ k : Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
        (fun n => (((n + 1) ^ k : Nat) : ℝ)) := Iff.rfl

namespace IsPolynomiallyBounded

variable {f g : Nat → Nat}

/-- Expose the underlying mathlib asymptotic certificate. -/
theorem exists_isBigO (hf : IsPolynomiallyBounded f) :
    ∃ k : Nat, Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
      (fun n => (((n + 1) ^ k : Nat) : ℝ)) := hf

/-- Extract a concrete polynomial budget valid even below an asymptotic threshold. -/
theorem exists_bound (hf : IsPolynomiallyBounded f) :
    ∃ c k : Nat, ∀ n, f n ≤ c * (n + 1) ^ k := by
  obtain ⟨k, hf⟩ := hf
  obtain ⟨c, hc⟩ := isBigO_shifted_pow_iff.mp hf
  exact ⟨c, k, hc⟩

/-- A concrete all-input bound supplies a mathlib polynomial growth certificate. -/
theorem of_bound {c k : Nat} (hf : ∀ n, f n ≤ c * (n + 1) ^ k) :
    IsPolynomiallyBounded f :=
  ⟨k, isBigO_shifted_pow_iff.mpr ⟨c, hf⟩⟩

/-- Reuse any mathlib asymptotic comparison with a polynomially bounded function. -/
theorem of_isBigO (hg : IsPolynomiallyBounded g)
    (hfg : Asymptotics.IsBigO Filter.atTop
      (fun n => (f n : ℝ)) (fun n => (g n : ℝ))) : IsPolynomiallyBounded f := by
  obtain ⟨k, hg⟩ := hg
  exact ⟨k, hfg.trans hg⟩

/-- A monomial in the shifted size is itself polynomially bounded. -/
theorem monomial (c k : Nat) :
    IsPolynomiallyBounded (fun n => c * (n + 1) ^ k) := by
  refine ⟨k, ?_⟩
  simpa only [Nat.cast_mul] using Asymptotics.isBigO_const_mul_self (c : ℝ)
    (fun n : Nat => (((n + 1) ^ k : Nat) : ℝ)) Filter.atTop

/-- Every fixed constant, including zero, is polynomially bounded. -/
theorem const (c : Nat) : IsPolynomiallyBounded (fun _ => c) := by
  refine ⟨0, ?_⟩
  simpa only [Nat.pow_zero, Nat.cast_one] using
    Asymptotics.isBigO_const_const (c : ℝ) (one_ne_zero : (1 : ℝ) ≠ 0) Filter.atTop

/-- The identity size function is polynomially bounded. -/
theorem id : IsPolynomiallyBounded (fun n => n) := by
  refine ⟨1, Asymptotics.isBigO_of_le Filter.atTop ?_⟩
  intro n
  simpa only [Real.norm_natCast, Nat.pow_one] using
    (Nat.cast_le.mpr (Nat.le_succ n) : (n : ℝ) ≤ ((n + 1 : Nat) : ℝ))

/-- A pointwise smaller function inherits a polynomial upper bound. -/
theorem mono (hf : IsPolynomiallyBounded f) (hgf : ∀ n, g n ≤ f n) :
    IsPolynomiallyBounded g := by
  apply hf.of_isBigO (Asymptotics.isBigO_of_le Filter.atTop ?_)
  intro n
  simpa only [Real.norm_natCast] using
    (Nat.cast_le.mpr (hgf n) : (g n : ℝ) ≤ (f n : ℝ))

/-- Polynomial bounds are closed under addition. -/
theorem add (hf : IsPolynomiallyBounded f) (hg : IsPolynomiallyBounded g) :
    IsPolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨k, hf⟩ := hf
  obtain ⟨l, hg⟩ := hg
  have liftDegree {a b : Nat} (hab : a ≤ b) :
      ∀ n : Nat, ‖(((n + 1) ^ a : Nat) : ℝ)‖ ≤ ‖(((n + 1) ^ b : Nat) : ℝ)‖ := by
    intro n
    simpa only [Real.norm_natCast] using
      (Nat.cast_le.mpr (Nat.pow_le_pow_right (Nat.zero_lt_succ n) hab) :
        (((n + 1) ^ a : Nat) : ℝ) ≤ (((n + 1) ^ b : Nat) : ℝ))
  refine ⟨max k l, ?_⟩
  simpa only [Nat.cast_add] using
    (hf.trans_le (liftDegree (Nat.le_max_left k l))).add
      (hg.trans_le (liftDegree (Nat.le_max_right k l)))

/-- Polynomial bounds are closed under multiplication. -/
theorem mul (hf : IsPolynomiallyBounded f) (hg : IsPolynomiallyBounded g) :
    IsPolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨k, hf⟩ := hf
  obtain ⟨l, hg⟩ := hg
  refine ⟨k + l, ?_⟩
  simpa only [Nat.pow_add, Nat.cast_mul] using hf.mul hg

/-- Taking a fixed natural power preserves a polynomial upper bound. -/
theorem pow (hf : IsPolynomiallyBounded f) (exponent : Nat) :
    IsPolynomiallyBounded (fun n => f n ^ exponent) := by
  obtain ⟨k, hf⟩ := hf
  refine ⟨k * exponent, ?_⟩
  simpa only [Nat.pow_mul, Nat.cast_pow] using hf.pow exponent

/-- Taking a pointwise maximum preserves polynomial boundedness. -/
theorem max (hf : IsPolynomiallyBounded f) (hg : IsPolynomiallyBounded g) :
    IsPolynomiallyBounded (fun n => max (f n) (g n)) := by
  apply (hf.add hg).mono
  intro n
  exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/-- Size-bound substitution preserves polynomial boundedness. Neither input
function needs to be monotone: the polynomial majorants supply monotonicity. -/
theorem comp (hf : IsPolynomiallyBounded f) (hg : IsPolynomiallyBounded g) :
    IsPolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨c, k, hf⟩ := hf.exists_bound
  exact ((const c).mul ((hg.add (const 1)).pow k)).mono (fun n => hf (g n))

/-- A polynomial bound can always be chosen with a positive coefficient. -/
theorem exists_pos (hf : IsPolynomiallyBounded f) :
    ∃ c k : Nat, 0 < c ∧ ∀ n, f n ≤ c * (n + 1) ^ k := by
  obtain ⟨c, k, hf⟩ := hf.exists_bound
  exact ⟨c + 1, k, Nat.zero_lt_succ c,
    fun n => Nat.le_trans (hf n) (Nat.mul_le_mul_right _ (Nat.le_succ c))⟩

/-- Shifted monomials are monotone in the input size. -/
theorem monomial_mono (c k : Nat) {m n : Nat} (hmn : m ≤ n) :
    c * (m + 1) ^ k ≤ c * (n + 1) ^ k :=
  Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) k)

/-- The executable monotone hull retains the original polynomial majorant. -/
theorem monotoneHull (hf : IsPolynomiallyBounded f) :
    IsPolynomiallyBounded (Asymptotics.monotoneHull f) := by
  obtain ⟨c, k, hf⟩ := hf.exists_bound
  exact of_bound (Asymptotics.monotoneHull_le hf (fun _ _ hmn => monomial_mono c k hmn))

/-- Choose the coefficient and exponent explicitly, with a positive
coefficient and monotonicity available for size-bound substitution. -/
theorem exists_monotone_monomial (hf : IsPolynomiallyBounded f) :
    ∃ c k : Nat, 0 < c ∧ (∀ n, f n ≤ c * (n + 1) ^ k) ∧
      (∀ ⦃m n⦄, m ≤ n → c * (m + 1) ^ k ≤ c * (n + 1) ^ k) := by
  obtain ⟨c, k, hc, hf⟩ := hf.exists_pos
  exact ⟨c, k, hc, hf, fun _ _ hmn => monomial_mono c k hmn⟩

/-- Every polynomially bounded function admits a positive-coefficient,
monotone polynomial majorant, even if the function itself is nonmonotone. -/
theorem exists_monotone_majorant (hf : IsPolynomiallyBounded f) :
    ∃ p : Nat → Nat, IsPolynomiallyBounded p ∧
      (∀ n, f n ≤ p n) ∧ (∀ ⦃m n⦄, m ≤ n → p m ≤ p n) ∧
      (∀ n, 0 < p n) := by
  obtain ⟨c, k, hc, hf⟩ := hf.exists_pos
  exact ⟨fun n => c * (n + 1) ^ k, monomial c k, hf,
    fun _ _ hmn => monomial_mono c k hmn,
    fun n => Nat.mul_pos hc (Nat.pow_pos (Nat.zero_lt_succ n))⟩

/-- A fixed finite sum of polynomially bounded functions is polynomially
bounded. The individual coefficients and degrees may differ. -/
theorem list_sum {α : Type} (indices : List α) (term : α → Nat → Nat)
    (hterm : ∀ i ∈ indices, IsPolynomiallyBounded (term i)) :
    IsPolynomiallyBounded (fun n => (indices.map (fun i => term i n)).sum) := by
  induction indices with
  | nil => simpa using const 0
  | cons i indices ih =>
    have hi := hterm i (by simp)
    have hs := ih (fun j hj => hterm j (by simp [hj]))
    simpa using hi.add hs

/-- Sum a list of values with one uniform upper bound. This helper also covers
input-dependent lists, so the number of summands need not be a constant. -/
theorem sum_map_le_length_mul {α : Type} (indices : List α) (term : α → Nat)
    (bound : Nat) (hterm : ∀ i ∈ indices, term i ≤ bound) :
    (indices.map term).sum ≤ indices.length * bound := by
  simpa using List.sum_le_sum hterm

/-- A polynomial number of uniformly polynomially bounded summands has a
polynomial sum. Uniformity in the index is essential; separate polynomial
bounds for each index alone would not imply this theorem. -/
theorem sum_range {length bound : Nat → Nat} (term : Nat → Nat → Nat)
    (hlength : IsPolynomiallyBounded length) (hbound : IsPolynomiallyBounded bound)
    (hterm : ∀ n i, i < length n → term i n ≤ bound n) :
    IsPolynomiallyBounded
      (fun n => ((List.range (length n)).map (fun i => term i n)).sum) := by
  apply (hlength.mul hbound).mono
  intro n
  simpa using sum_map_le_length_mul (List.range (length n)) (fun i => term i n)
    (bound n) (fun i hi => hterm n i (List.mem_range.mp hi))

end IsPolynomiallyBounded

end Asymptotics
