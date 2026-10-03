/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Execution.Space
import Complexity.Computability.Ram.Time.Basic

/-!
# Uniform physical-word space bounds for RAM programs

The fixed code runs on the same legal inputs and word widths as the time API.
`State.initial` places encoded input in the separate input stream and initializes
RAM memory to zero, so the initial resident-heap seed here is empty. Every bound
uses the actual halted machine execution and its cumulative distinct heap-word
footprint; it is not an allocation, maximum-address or peak-live-object bound.
-/

namespace Ram

/-- A concrete physical-word bound, termination and answer for one fixed code.
The space observation and postcondition refer to the same halted execution. -/
def UniformSpaceBound {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (bound : Nat → Nat) : Prop :=
  ∀ w input, admissible w input →
    ∃ steps finish, SpaceBound code steps (State.initial (encode w input)) finish ∅
      (bound (size input)) ∧ post w input finish

/-- Big-O of the physical words in actual halted runs on a chosen legal-input
filter. The transition count is a witness identifying the same execution, not
a time bound or a second computation. -/
def UniformSpaceBigOAt {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (post : ∀ w, Input → State w → Prop) (l : Filter (LegalInput admissible))
    (growth : LegalInput admissible → Nat) : Prop :=
  ∃ steps : LegalInput admissible → Nat,
    (∀ i, ∃ finish,
      Exec code (steps i) (State.initial (encode i.val.1 i.val.2)) finish ∧
      finish.status = .halted ∧ post i.val.1 i.val.2 finish) ∧
    Asymptotics.IsBigO l
      (fun i => (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ))
      (fun i => (growth i : ℝ))

/-- Scalar big-O uses the pre-existing legal-size filter and requires correct
termination even below its eventual asymptotic threshold. -/
def UniformSpaceBigO {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (growth : Nat → Nat) : Prop :=
  UniformSpaceBigOAt code encode admissible post (inputSizeFilter admissible size)
    (fun i => growth (size i.val.2))

theorem UniformSpaceBound.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {bound : Nat → Nat}
    (h : UniformSpaceBound code encode admissible size post bound) :
    UniformCorrect code encode admissible post := by
  intro w input legal
  obtain ⟨steps, finish, observed, answer⟩ := h w input legal
  exact ⟨steps, finish, observed.run, observed.halted, answer⟩

theorem UniformSpaceBigOAt.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {post : ∀ w, Input → State w → Prop}
    {l : Filter (LegalInput admissible)} {growth : LegalInput admissible → Nat}
    (h : UniformSpaceBigOAt code encode admissible post l growth) :
    UniformCorrect code encode admissible post := by
  obtain ⟨steps, runs, _⟩ := h
  intro w input legal
  obtain ⟨finish, run, halted, answer⟩ := runs ⟨(w, input), legal⟩
  exact ⟨steps ⟨(w, input), legal⟩, finish, run, halted, answer⟩

theorem UniformSpaceBigO.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {growth : Nat → Nat}
    (h : UniformSpaceBigO code encode admissible size post growth) :
    UniformCorrect code encode admissible post :=
  UniformSpaceBigOAt.correct h

theorem UniformSpaceBound.mono {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {a b : Nat → Nat}
    (h : UniformSpaceBound code encode admissible size post a)
    (hab : ∀ n, a n ≤ b n) :
    UniformSpaceBound code encode admissible size post b := by
  intro w input legal
  obtain ⟨steps, finish, observed, answer⟩ := h w input legal
  exact ⟨steps, finish, observed.mono (hab (size input)), answer⟩

/-- A time certificate and a space certificate cannot silently choose distinct
terminal runs: deterministic termination identifies their exact transition
count and final state. The result uses the space witness for both observations. -/
theorem UniformSpaceBound.with_time {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {timeBound spaceBound : Nat → Nat}
    (time : UniformTimeBound code encode admissible size post timeBound)
    (space : UniformSpaceBound code encode admissible size post spaceBound)
    {w : Nat} {input : Input} (legal : admissible w input) :
    ∃ steps finish,
      Exec code steps (State.initial (encode w input)) finish ∧
      finish.status = .halted ∧ post w input finish ∧
      steps ≤ timeBound (size input) ∧
      spaceWords code steps (State.initial (encode w input)) ∅ ≤
        spaceBound (size input) := by
  obtain ⟨steps, finish, observed, answer⟩ := space w input legal
  obtain ⟨timeFinish, timeRun, _⟩ := time w input legal
  exact ⟨steps, finish, observed.run, observed.halted, answer,
    observed.run.steps_le_of_terminatesWithin observed.halted timeRun, observed.space⟩

/-- Transfer a proved concrete space bound to a full legal-input asymptotic
regime without selecting an unrelated successful run. -/
theorem UniformSpaceBound.bigOAt_of_isBigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound : Nat → Nat} {l : Filter (LegalInput admissible)}
    {growth : LegalInput admissible → Nat}
    (h : UniformSpaceBound code encode admissible size post bound)
    (hO : Asymptotics.IsBigO l
      (fun i => (bound (size i.val.2) : ℝ)) (fun i => (growth i : ℝ))) :
    UniformSpaceBigOAt code encode admissible post l growth := by
  classical
  let witness : (i : LegalInput admissible) →
      ∃ steps finish, SpaceBound code steps
        (State.initial (encode i.val.1 i.val.2)) finish ∅
        (bound (size i.val.2)) ∧ post i.val.1 i.val.2 finish :=
    fun i => h i.val.1 i.val.2 i.property
  let steps : LegalInput admissible → Nat := fun i => (witness i).choose
  have runs : ∀ i : LegalInput admissible, ∃ finish,
      Exec code (steps i) (State.initial (encode i.val.1 i.val.2)) finish ∧
      finish.status = .halted ∧ post i.val.1 i.val.2 finish := by
    intro i
    obtain ⟨finish, observed, answer⟩ := (witness i).choose_spec
    exact ⟨finish, observed.run, observed.halted, answer⟩
  refine ⟨steps, runs, ?_⟩
  have hfirst : Asymptotics.IsBigO l
      (fun i => (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ))
      (fun i => (bound (size i.val.2) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro i
    obtain ⟨finish, observed, answer⟩ := (witness i).choose_spec
    have hb : (spaceWords code (steps i)
        (State.initial (encode i.val.1 i.val.2)) ∅ : ℝ) ≤
        (bound (size i.val.2) : ℝ) := by exact_mod_cast observed.space
    simpa only [Real.norm_natCast, one_mul] using hb
  exact hfirst.trans hO

theorem UniformSpaceBound.bigO_of_isBigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound growth : Nat → Nat}
    (h : UniformSpaceBound code encode admissible size post bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    UniformSpaceBigO code encode admissible size post growth :=
  h.bigOAt_of_isBigO (hO.comp_tendsto Filter.tendsto_comap)

end Ram
