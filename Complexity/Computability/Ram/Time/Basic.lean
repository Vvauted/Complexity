/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Execution.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform runtime bounds for a fixed RAM program

The code is fixed outside the quantifiers over inputs and word widths. Both
exact upper bounds and asymptotic bounds require successful termination and the
postcondition, not merely an implication about an execution that might not
exist. Encoding, admissible widths, and the input-size function belong to the
problem specification; changing them changes the claim.

Asymptotic bounds use mathlib's `Asymptotics.IsBigO` on the legal input family,
filtered by increasing problem size. Its runtime witness is the number of real
machine transitions on each input, not a size-only envelope. Thus infinitely
many word widths or inputs of a small size need not have uniformly bounded
runtimes. Total correctness still covers all of them.
-/

namespace Ram

/-- Successful termination and the functional postcondition for every legal
input, including inputs below an asymptotic threshold. -/
def UniformCorrect {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (post : ∀ w, Input → State w → Prop) : Prop :=
  ∀ w input, admissible w input →
    ∃ steps finish, Exec code steps (State.initial (encode w input)) finish ∧
      finish.status = .halted ∧ post w input finish

/-- A total functional specification and time bound, uniform in the word width
and input, for one fixed instruction list. Input encoding costs inside the
program are counted; anything done by `encode` is part of the external problem
encoding and must be specified as such. -/
def UniformTimeBound {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (bound : Nat → Nat) : Prop :=
  ∀ w input, admissible w input →
    ∃ finish, TerminatesWithin code (bound (size input))
      (State.initial (encode w input)) finish ∧ post w input finish

/-- A legal input includes its word width. Both vary in the same asymptotic
domain, so one `IsBigO` constant must work uniformly for both. -/
abbrev LegalInput {Input : Type} (admissible : Nat → Input → Prop) :=
  { wi : Nat × Input // admissible wi.1 wi.2 }

/-- Eventual statements hold for every legal input of sufficiently large size,
not merely along one selected sequence of inputs or widths. -/
def inputSizeFilter {Input : Type} (admissible : Nat → Input → Prop)
    (size : Input → Nat) : Filter (LegalInput admissible) :=
  Filter.comap (fun i => size i.val.2) Filter.atTop

theorem eventually_inputSizeFilter {Input : Type}
    {admissible : Nat → Input → Prop} {size : Input → Nat}
    {P : LegalInput admissible → Prop} :
    (∀ᶠ i in inputSizeFilter admissible size, P i) ↔
      ∃ threshold, ∀ i, threshold ≤ size i.val.2 → P i := by
  rw [inputSizeFilter, Filter.eventually_comap, Filter.eventually_atTop]
  constructor
  · rintro ⟨threshold, h⟩
    exact ⟨threshold, fun i hi => h _ hi i rfl⟩
  · rintro ⟨threshold, h⟩
    refine ⟨threshold, ?_⟩
    intro n hn i hi
    apply h i
    simpa only [hi] using hn

/-- Uniform asymptotic complexity on an explicitly chosen legal-input filter.
The growth expression may depend on several input parameters. Correctness and
termination cover every legal input, independently of the asymptotic filter.
The big-O constant is shared by the whole family, including all word widths. -/
def UniformBigOAt {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (post : ∀ w, Input → State w → Prop) (l : Filter (LegalInput admissible))
    (growth : LegalInput admissible → Nat) : Prop :=
  ∃ runtime : LegalInput admissible → Nat,
    (∀ i, ∃ finish, Exec code (runtime i) (State.initial (encode i.val.1 i.val.2)) finish ∧
      finish.status = .halted ∧ post i.val.1 i.val.2 finish) ∧
    Asymptotics.IsBigO l (fun i => (runtime i : ℝ)) (fun i => (growth i : ℝ))

/-- Genuine mathlib big-O of an exact machine-runtime witness. The witness
terminates correctly on every legal input; only its asymptotic bound is
eventual. There is no requirement for a size-only bound at small sizes. -/
def UniformBigO {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (growth : Nat → Nat) : Prop :=
  UniformBigOAt code encode admissible post (inputSizeFilter admissible size)
    (fun i => growth (size i.val.2))

theorem UniformBigO.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {growth : Nat → Nat}
    (h : UniformBigO code encode admissible size post growth) :
    UniformCorrect code encode admissible post := by
  obtain ⟨runtime, hrun, _⟩ := h
  intro w input hi
  obtain ⟨finish, he, hh, hp⟩ := hrun ⟨(w, input), hi⟩
  exact ⟨runtime ⟨(w, input), hi⟩, finish, he, hh, hp⟩

/-- Any successful exact runtime obeys a proved termination budget for the
same initial machine state, by uniqueness of the terminal transition count. -/
theorem Exec.steps_le_of_terminatesWithin {code : Code} {steps budget : Nat}
    {s t u : State w} (he : Exec code steps s t) (hh : t.status = .halted)
    (hb : TerminatesWithin code budget s u) : steps ≤ budget := by
  obtain ⟨n, hn, hx, hhalt⟩ := hb
  have hsteps := (he.terminal_unique hx (step_of_halted hh) (step_of_halted hhalt)).1
  simpa only [hsteps] using hn

/-- Characterize the mathlib-based definition by a uniform eventual natural bound.
In particular, this equivalence introduces no uniform envelope for
the potentially infinite family of small-size inputs. -/
theorem uniformBigO_iff_eventual {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {growth : Nat → Nat} :
    UniformBigO code encode admissible size post growth ↔
      UniformCorrect code encode admissible post ∧
      ∃ constant threshold, 0 < constant ∧
        ∀ w input, admissible w input → threshold ≤ size input →
          ∃ finish, TerminatesWithin code (constant * growth (size input))
            (State.initial (encode w input)) finish ∧ post w input finish := by
  constructor
  · intro h
    have hcorrect := h.correct
    obtain ⟨runtime, hrun, hO⟩ := h
    obtain ⟨c, hc, hcost⟩ := hO.exists_pos
    obtain ⟨constant, hconstant⟩ := exists_nat_gt c
    have hpositive : 0 < constant := by exact_mod_cast hc.trans hconstant
    obtain ⟨threshold, hthreshold⟩ := eventually_inputSizeFilter.mp hcost.bound
    refine ⟨hcorrect, constant, threshold, hpositive, ?_⟩
    intro w input hi hs
    let i : LegalInput admissible := ⟨(w, input), hi⟩
    obtain ⟨finish, he, hh, hp⟩ := hrun i
    have hreal : (runtime i : ℝ) ≤ c * (growth (size input) : ℝ) := by
      simpa only [Real.norm_natCast] using hthreshold i hs
    have hrounded : (runtime i : ℝ) ≤ (constant : ℝ) * (growth (size input) : ℝ) :=
      hreal.trans (mul_le_mul_of_nonneg_right hconstant.le (Nat.cast_nonneg _))
    have hbound : runtime i ≤ constant * growth (size input) := by exact_mod_cast hrounded
    exact ⟨finish, ⟨runtime i, hbound, he, hh⟩, hp⟩
  · rintro ⟨hcorrect, constant, threshold, _, hbound⟩
    classical
    let runtime : LegalInput admissible → Nat := fun i =>
      (hcorrect i.val.1 i.val.2 i.property).choose
    have hrun : ∀ i : LegalInput admissible, ∃ finish,
        Exec code (runtime i) (State.initial (encode i.val.1 i.val.2)) finish ∧
          finish.status = .halted ∧ post i.val.1 i.val.2 finish :=
      fun i => (hcorrect i.val.1 i.val.2 i.property).choose_spec
    refine ⟨runtime, hrun, Asymptotics.IsBigO.of_bound (constant : ℝ) ?_⟩
    apply eventually_inputSizeFilter.mpr
    refine ⟨threshold, ?_⟩
    intro i hi
    obtain ⟨finish, he, hh, _⟩ := hrun i
    obtain ⟨boundedFinish, hb, _⟩ := hbound i.val.1 i.val.2 i.property hi
    have hn := he.steps_le_of_terminatesWithin hh hb
    have hr : (runtime i : ℝ) ≤ (constant : ℝ) * (growth (size i.val.2) : ℝ) := by
      exact_mod_cast hn
    simpa only [Real.norm_natCast] using hr

theorem UniformTimeBound.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {bound : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post bound) :
    UniformCorrect code encode admissible post := by
  intro w input hadmissible
  obtain ⟨finish, ⟨steps, _, he, hhalt⟩, hp⟩ := h w input hadmissible
  exact ⟨steps, finish, he, hhalt, hp⟩

theorem UniformTimeBound.mono {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {a b : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post a)
    (hab : ∀ n, a n ≤ b n) : UniformTimeBound code encode admissible size post b := by
  intro w input hadmissible
  obtain ⟨finish, he, hp⟩ := h w input hadmissible
  exact ⟨finish, he.mono (hab (size input)), hp⟩

/-- Transfer a proved concrete machine bound to an eventual asymptotic bound. -/
theorem UniformTimeBound.bigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound growth : Nat → Nat} {constant threshold : Nat}
    (h : UniformTimeBound code encode admissible size post bound)
    (hc : 0 < constant)
    (hbound : ∀ n, threshold ≤ n → bound n ≤ constant * growth n) :
    UniformBigO code encode admissible size post growth := by
  apply uniformBigO_iff_eventual.mpr
  refine ⟨h.correct, constant, threshold, hc, ?_⟩
  intro w input hadmissible hsize
  obtain ⟨finish, he, hp⟩ := h w input hadmissible
  exact ⟨finish, he.mono (hbound (size input) hsize), hp⟩

/-- Analyze a proved concrete bound with mathlib, then transfer that bound to
the actual runtime over the complete legal input family. -/
theorem UniformTimeBound.bigO_of_isBigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound growth : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    UniformBigO code encode admissible size post growth := by
  classical
  let runtime : LegalInput admissible → Nat := fun i =>
    (h.correct i.val.1 i.val.2 i.property).choose
  have hrun : ∀ i : LegalInput admissible, ∃ finish,
      Exec code (runtime i) (State.initial (encode i.val.1 i.val.2)) finish ∧
        finish.status = .halted ∧ post i.val.1 i.val.2 finish :=
    fun i => (h.correct i.val.1 i.val.2 i.property).choose_spec
  refine ⟨runtime, hrun, ?_⟩
  have hfirst : Asymptotics.IsBigO (inputSizeFilter admissible size)
      (fun i => (runtime i : ℝ)) (fun i => (bound (size i.val.2) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro i
    obtain ⟨finish, he, hh, _⟩ := hrun i
    obtain ⟨boundedFinish, hb, _⟩ := h i.val.1 i.val.2 i.property
    have hn := he.steps_le_of_terminatesWithin hh hb
    have hr : (runtime i : ℝ) ≤ (bound (size i.val.2) : ℝ) := by exact_mod_cast hn
    simpa only [Real.norm_natCast, one_mul] using hr
  exact hfirst.trans (hO.comp_tendsto Filter.tendsto_comap)

/-- A concrete affine machine bound yields linear asymptotic time, including
the fixed setup/termination overhead rather than silently dropping it. -/
theorem UniformTimeBound.linear {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {a b : Nat}
    (h : UniformTimeBound code encode admissible size post (fun n => a * n + b)) :
    UniformBigO code encode admissible size post (fun n => n) := by
  apply h.bigO (constant := a + b + 1) (threshold := 1) (Nat.zero_lt_succ _)
  intro n hn
  have hb : b ≤ b * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hn
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end Ram
