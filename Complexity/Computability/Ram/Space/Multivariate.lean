/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Space.Basic
import Complexity.Computability.Ram.Time.Multivariate

/-!
# Multivariate physical-word space bounds

The legal-input filter and growth expression may use different combinations of
input parameters. Correct termination remains required on every legal input;
only the cumulative physical-word bound is eventual. Space may legitimately be
zero when the machine never loads or stores a heap word.
-/

namespace Ram

variable {Input : Type} {code : Code}
variable {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
variable {post : ∀ w, Input → State w → Prop}
variable {l l' : Filter (LegalInput admissible)}
variable {bound growth growth' : LegalInput admissible → Nat}

namespace UniformSpaceBigOAt

/-- Restrict only the asymptotic regime, retaining every legal run. -/
theorem filter_mono (h : UniformSpaceBigOAt code encode admissible post l growth)
    (hle : l' ≤ l) : UniformSpaceBigOAt code encode admissible post l' growth := by
  obtain ⟨steps, runs, hO⟩ := h
  exact ⟨steps, runs, hO.mono hle⟩

/-- Weaken the requested space growth without changing the actual trace. -/
theorem of_isBigO (h : UniformSpaceBigOAt code encode admissible post l growth)
    (hO : Asymptotics.IsBigO l (fun i => (growth i : ℝ))
      (fun i => (growth' i : ℝ))) :
    UniformSpaceBigOAt code encode admissible post l growth' := by
  obtain ⟨steps, runs, hbound⟩ := h
  exact ⟨steps, runs, hbound.trans hO⟩

/-- Analyze a full-input physical-word budget on a chosen legal regime. -/
theorem of_spaceBound
    (h : ∀ i : LegalInput admissible, ∃ steps finish,
      SpaceBound code steps (State.initial (encode i.val.1 i.val.2)) finish ∅
        (bound i) ∧ post i.val.1 i.val.2 finish)
    (hO : Asymptotics.IsBigO l (fun i => (bound i : ℝ))
      (fun i => (growth i : ℝ))) :
    UniformSpaceBigOAt code encode admissible post l growth := by
  classical
  let steps : LegalInput admissible → Nat := fun i => (h i).choose
  have runs : ∀ i : LegalInput admissible, ∃ finish,
      Exec code (steps i) (State.initial (encode i.val.1 i.val.2)) finish ∧
      finish.status = .halted ∧ post i.val.1 i.val.2 finish := by
    intro i
    obtain ⟨finish, observed, answer⟩ := (h i).choose_spec
    exact ⟨finish, observed.run, observed.halted, answer⟩
  refine ⟨steps, runs, ?_⟩
  have hfirst : Asymptotics.IsBigO l
      (fun i => (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ))
      (fun i => (bound i : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro i
    obtain ⟨finish, observed, answer⟩ := (h i).choose_spec
    have hb : (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ) ≤
        (bound i : ℝ) := by exact_mod_cast observed.space
    simpa only [Real.norm_natCast, one_mul] using hb
  exact hfirst.trans hO

end UniformSpaceBigOAt

/-- All-input correctness plus an eventual space budget describes precisely
the full-family big-O claim; terminal determinism relates the witnesses. -/
theorem uniformSpaceBigOAt_iff_eventual :
    UniformSpaceBigOAt code encode admissible post l growth ↔
      UniformCorrect code encode admissible post ∧
      ∃ constant : Nat, 0 < constant ∧
        ∀ᶠ i in l, ∃ steps finish,
          SpaceBound code steps (State.initial (encode i.val.1 i.val.2)) finish ∅
            (constant * growth i) ∧ post i.val.1 i.val.2 finish := by
  constructor
  · intro h
    have hcorrect := h.correct
    obtain ⟨steps, runs, hO⟩ := h
    obtain ⟨c, hc, hcost⟩ := hO.exists_pos
    obtain ⟨constant, hconstant⟩ := exists_nat_gt c
    have hpositive : 0 < constant := by exact_mod_cast hc.trans hconstant
    refine ⟨hcorrect, constant, hpositive, ?_⟩
    filter_upwards [hcost.bound] with i hi
    obtain ⟨finish, run, halted, answer⟩ := runs i
    have hreal : (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ) ≤
        c * (growth i : ℝ) := by
      simpa only [Real.norm_natCast] using hi
    have hrounded : (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ) ≤
        (constant : ℝ) * (growth i : ℝ) :=
      hreal.trans (mul_le_mul_of_nonneg_right hconstant.le (Nat.cast_nonneg _))
    have hbound : spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ ≤ constant * growth i := by
      exact_mod_cast hrounded
    exact ⟨steps i, finish, ⟨run, halted, hbound⟩, answer⟩
  · rintro ⟨hcorrect, constant, _, hbound⟩
    classical
    let steps : LegalInput admissible → Nat := fun i =>
      (hcorrect i.val.1 i.val.2 i.property).choose
    have runs : ∀ i : LegalInput admissible, ∃ finish,
        Exec code (steps i) (State.initial (encode i.val.1 i.val.2)) finish ∧
        finish.status = .halted ∧ post i.val.1 i.val.2 finish :=
      fun i => (hcorrect i.val.1 i.val.2 i.property).choose_spec
    refine ⟨steps, runs, Asymptotics.IsBigO.of_bound (constant : ℝ) ?_⟩
    filter_upwards [hbound] with i hi
    obtain ⟨finish, run, halted, _⟩ := runs i
    obtain ⟨boundedSteps, boundedFinish, observed, _⟩ := hi
    have same := run.terminal_unique observed.run
      (step_of_halted halted) (step_of_halted observed.halted)
    have hs : steps i = boundedSteps := same.1
    have hspace : spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ ≤ constant * growth i := by
      rw [hs]
      exact observed.space
    have hr : (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ) ≤
        (constant : ℝ) * (growth i : ℝ) := by exact_mod_cast hspace
    simpa only [Real.norm_natCast] using hr

end Ram
