/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity

/-!
# Machine complexity with several size parameters

`UniformBigOAt` separates the chosen asymptotic regime from the growth
expression. For instance, take `inputSizeFilter admissible (fun x => n x + m x)`
and growth `fun i => m i.val.2 * Nat.log2 (n i.val.2)`. Unlike product `atTop`,
that regime retains families where only one of the two sizes grows.

The interface directly uses mathlib filters and `IsBigO`, and the same exact
machine-runtime witness proves correctness on every legal input. It does not
change the encoding or hide costs of converting representations. Like mathlib,
the asymptotic proposition alone permits a bottom filter; a published
asymptotic problem must additionally justify a nontrivial growth regime.

The existing scalar `UniformBigO` is a definitional specialization. These rules
therefore apply to both interfaces without an equivalence proof or conversion
of runtime witnesses.
-/

namespace Ram

variable {Input : Type} {code : Code}
variable {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
variable {post : ∀ w, Input → State w → Prop}
variable {l l' : Filter (LegalInput admissible)}
variable {bound growth growth' : LegalInput admissible → Nat}

/-- A scalar exhaustion describes a nontrivial asymptotic regime exactly when
legal inputs reach arbitrarily large values. This can be used for a joint
measure such as `n + m`, independently of the desired multivariate cost bound. -/
theorem inputSizeFilter_neBot_iff {size : Input → Nat} :
    (inputSizeFilter admissible size).NeBot ↔
      ∀ threshold, ∃ w input, admissible w input ∧ threshold ≤ size input := by
  constructor
  · intro hn threshold
    letI := hn
    have hlarge : ∀ᶠ i in inputSizeFilter admissible size, threshold ≤ size i.val.2 :=
      eventually_inputSizeFilter.mpr ⟨threshold, fun _ hi => hi⟩
    obtain ⟨i, hi⟩ := hlarge.exists
    exact ⟨i.val.1, i.val.2, i.property, hi⟩
  · intro hunbounded
    apply Filter.comap_neBot
    intro s hs
    obtain ⟨threshold, hthreshold⟩ := Filter.mem_atTop_sets.mp hs
    obtain ⟨w, input, ha, hi⟩ := hunbounded threshold
    exact ⟨⟨(w, input), ha⟩, hthreshold (size input) hi⟩

namespace UniformBigOAt

/-- The asymptotic regime does not restrict the all-input correctness claim. -/
theorem correct (h : UniformBigOAt code encode admissible post l growth) :
    UniformCorrect code encode admissible post := by
  obtain ⟨runtime, hrun, _⟩ := h
  intro w input hi
  obtain ⟨finish, he, hh, hp⟩ := hrun ⟨(w, input), hi⟩
  exact ⟨runtime ⟨(w, input), hi⟩, finish, he, hh, hp⟩

/-- Restrict the asymptotic regime, keeping the original all-input run proof. -/
theorem filter_mono (h : UniformBigOAt code encode admissible post l growth)
    (hle : l' ≤ l) : UniformBigOAt code encode admissible post l' growth := by
  obtain ⟨runtime, hrun, hO⟩ := h
  exact ⟨runtime, hrun, hO.mono hle⟩

/-- Change only the growth bound using a comparison on the same legal family. -/
theorem of_isBigO (h : UniformBigOAt code encode admissible post l growth)
    (hO : Asymptotics.IsBigO l (fun i => (growth i : ℝ))
      (fun i => (growth' i : ℝ))) :
    UniformBigOAt code encode admissible post l growth' := by
  obtain ⟨runtime, hrun, hbound⟩ := h
  exact ⟨runtime, hrun, hbound.trans hO⟩

/-- A bound depending on the full legal input yields asymptotic machine
complexity once its mathematical growth is proved. No scalar size envelope is
required, and every bound is justified by successful machine execution. -/
theorem of_terminatesWithin
    (h : ∀ i : LegalInput admissible, ∃ finish,
      TerminatesWithin code (bound i) (State.initial (encode i.val.1 i.val.2)) finish ∧
        post i.val.1 i.val.2 finish)
    (hO : Asymptotics.IsBigO l (fun i => (bound i : ℝ))
      (fun i => (growth i : ℝ))) :
    UniformBigOAt code encode admissible post l growth := by
  classical
  let finish := fun i => (h i).choose
  let runtime := fun i => (h i).choose_spec.1.choose
  have hrun : ∀ i : LegalInput admissible,
      runtime i ≤ bound i ∧
      Exec code (runtime i) (State.initial (encode i.val.1 i.val.2)) (finish i) ∧
      (finish i).status = .halted :=
    fun i => (h i).choose_spec.1.choose_spec
  refine ⟨runtime, fun i => ⟨finish i, (hrun i).2.1, (hrun i).2.2,
    (h i).choose_spec.2⟩, ?_⟩
  have hfirst : Asymptotics.IsBigO l (fun i => (runtime i : ℝ))
      (fun i => (bound i : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro i
    simpa only [Real.norm_natCast, one_mul] using
      (Nat.cast_le.mpr (hrun i).1 : (runtime i : ℝ) ≤ (bound i : ℝ))
  exact hfirst.trans hO

end UniformBigOAt

/-- The full-family filter formulation is equivalent to a uniform eventual
natural budget, together with total correctness on all legal inputs. -/
theorem uniformBigOAt_iff_eventual :
    UniformBigOAt code encode admissible post l growth ↔
      UniformCorrect code encode admissible post ∧
      ∃ constant : Nat, 0 < constant ∧
        ∀ᶠ i in l, ∃ finish,
          TerminatesWithin code (constant * growth i)
            (State.initial (encode i.val.1 i.val.2)) finish ∧ post i.val.1 i.val.2 finish := by
  constructor
  · intro h
    have hcorrect := h.correct
    obtain ⟨runtime, hrun, hO⟩ := h
    obtain ⟨c, hc, hcost⟩ := hO.exists_pos
    obtain ⟨constant, hconstant⟩ := exists_nat_gt c
    have hpositive : 0 < constant := by exact_mod_cast hc.trans hconstant
    refine ⟨hcorrect, constant, hpositive, ?_⟩
    filter_upwards [hcost.bound] with i hi
    obtain ⟨finish, he, hh, hp⟩ := hrun i
    have hreal : (runtime i : ℝ) ≤ c * (growth i : ℝ) := by
      simpa only [Real.norm_natCast] using hi
    have hrounded : (runtime i : ℝ) ≤ (constant : ℝ) * (growth i : ℝ) :=
      hreal.trans (mul_le_mul_of_nonneg_right hconstant.le (Nat.cast_nonneg _))
    have hbound : runtime i ≤ constant * growth i := by exact_mod_cast hrounded
    exact ⟨finish, ⟨runtime i, hbound, he, hh⟩, hp⟩
  · rintro ⟨hcorrect, constant, _, hbound⟩
    classical
    let runtime : LegalInput admissible → Nat := fun i =>
      (hcorrect i.val.1 i.val.2 i.property).choose
    have hrun : ∀ i : LegalInput admissible, ∃ finish,
        Exec code (runtime i) (State.initial (encode i.val.1 i.val.2)) finish ∧
          finish.status = .halted ∧ post i.val.1 i.val.2 finish :=
      fun i => (hcorrect i.val.1 i.val.2 i.property).choose_spec
    refine ⟨runtime, hrun, Asymptotics.IsBigO.of_bound (constant : ℝ) ?_⟩
    filter_upwards [hbound] with i hi
    obtain ⟨finish, he, hh, _⟩ := hrun i
    obtain ⟨boundedFinish, hb, _⟩ := hi
    have hn := he.steps_le_of_terminatesWithin hh hb
    have hr : (runtime i : ℝ) ≤ (constant : ℝ) * (growth i : ℝ) := by
      exact_mod_cast hn
    simpa only [Real.norm_natCast] using hr

/-- Existing scalar concrete budgets can be analyzed in a multivariate regime.
Only the comparison function and filter change, not the machine bound. -/
theorem UniformTimeBound.bigOAt_of_isBigO {size : Input → Nat} {budget : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post budget)
    (hO : Asymptotics.IsBigO l (fun i => (budget (size i.val.2) : ℝ))
      (fun i => (growth i : ℝ))) :
    UniformBigOAt code encode admissible post l growth :=
  UniformBigOAt.of_terminatesWithin (fun i => h i.val.1 i.val.2 i.property) hO

end Ram
