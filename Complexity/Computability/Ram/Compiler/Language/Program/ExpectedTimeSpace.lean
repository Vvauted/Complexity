/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ParsedTimeSpace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Average resources under an author-fixed input distribution

This is average-case analysis of the existing deterministic program, not a
probabilistic language or a random-seed input convention. The task fixes a family
of raw-input PMFs and its admissible parameters; neither is chosen by the solver.
Task-specific distribution definitions must describe the original random fields
and justify the intended parameter coverage. Random data generation is outside
the preloaded-input invocation, just as loading deterministic inputs is outside it.

Time is an ENNReal-weighted sum of the steps of actual compiled executions.
Absent successful execution (including fault or divergence) costs infinity, not
zero. Every positive-mass input has a worst-case physical-space certificate for
that same execution. Independent `Correct`/`CorrectParsed` obligations continue
to cover every legal mathematical input, not merely almost all sampled inputs.

Widths are quantified as functions of the raw input. The canonical function
`fun x => timeWidth overhead x (timeTarget parameter)` is always admitted, even
when the distribution has unbounded support; no impossible common-width premise
can discharge the contract. The law and target do not depend on this function.

Internal random sampling, its cost, and a randomized compiler bridge are not
provided by this file. In particular a supplied seed is not an internal oracle.
-/

namespace Complexity.Program

open scoped ENNReal

universe u v w z r
variable {α : Type u} {β : Type v} {ι : Type w} {ο : Type z} {κ : Type r}
variable [Input α] [Output β] [RamInput α]

/-- Steps of the unique successful compiled invocation, or infinity if none
exists. Call-depth certificates do not choose different execution costs. -/
noncomputable def actualSteps (program : Complexity.Program α β) (x : α)
    (wordWidth : Nat) : ℝ≥0∞ := by
  classical
  exact if completed : ∃ depth, Nonempty (program.Execution x wordWidth depth) then
    ((Classical.choice completed.choose_spec).result.steps : ℝ≥0∞)
  else ⊤

theorem actualSteps_eq {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) :
    program.actualSteps x w = (execution.result.steps : ℝ≥0∞) := by
  classical
  unfold actualSteps
  split
  · rename_i completed
    have same :=
      (Classical.choice completed.choose_spec : program.Execution x w completed.choose).result_eq
        execution
    exact congrArg (fun result => (result.steps : ℝ≥0∞)) same
  · rename_i absent
    exact False.elim (absent ⟨depth, ⟨execution⟩⟩)

theorem actualSteps_eq_top_of_no_execution {program : Complexity.Program α β}
    {x : α} {w : Nat}
    (absent : ¬∃ depth, Nonempty (program.Execution x w depth)) :
    program.actualSteps x w = ⊤ := by
  classical
  simp only [actualSteps, dif_neg absent]

/-- The ordinary nonnegative discrete expectation; zero-mass points contribute
zero even when their execution cost is infinite. -/
noncomputable def expectedSteps (program : Complexity.Program α β) (law : PMF α)
    (wordWidths : α → Nat) : ℝ≥0∞ :=
  ∑' x, law x * program.actualSteps x (wordWidths x)

/-- Author-fixed input-average time and samplewise worst-case physical space.
The two envelopes are uniform before parameters, inputs, and width functions.
All raw inputs in the law's support must belong to the stated legal domain. -/
def ExpectedTimeSpaceOOn (program : Complexity.Program α β)
    (parameterValid : κ → Prop) (law : κ → PMF α) (valid : α → Prop)
    (timeTarget : κ → Nat) (spaceTarget : α → Nat) : Prop :=
  (∀ parameter, parameterValid parameter →
    ∀ x ∈ (law parameter).support, valid x) ∧
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
    ∀ parameter, parameterValid parameter → ∀ wordWidths : α → Nat,
      (∀ x ∈ (law parameter).support,
        timeWidth overhead x (timeTarget parameter) ≤ wordWidths x) →
      program.expectedSteps (law parameter) wordWidths ≤
          (timeBound (timeTarget parameter) : ℝ≥0∞) ∧
        ∀ x ∈ (law parameter).support,
          ∃ depth, ∃ execution : program.Execution x (wordWidths x) depth,
            execution.spaceWords ≤ spaceBound (spaceTarget x)

/-- A deterministic joint certificate is reusable when its pointwise time
target is constant on every distribution fiber. No algorithm proof is repeated. -/
theorem TimeSpaceOOn.to_expected {program : Complexity.Program α β}
    {valid : α → Prop} {pointTime spaceTarget : α → Nat}
    (bounds : program.TimeSpaceOOn valid pointTime spaceTarget)
    (parameterValid : κ → Prop) (law : κ → PMF α) (timeTarget : κ → Nat)
    (supported : ∀ parameter, parameterValid parameter →
      ∀ x ∈ (law parameter).support, valid x)
    (fiber : ∀ parameter, parameterValid parameter →
      ∀ x ∈ (law parameter).support, pointTime x = timeTarget parameter) :
    program.ExpectedTimeSpaceOOn parameterValid law valid timeTarget spaceTarget := by
  classical
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨supported, overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro parameter legal wordWidths admitted
  have executed : ∀ x ∈ (law parameter).support,
      ∃ depth, ∃ execution : program.Execution x (wordWidths x) depth,
        execution.result.steps ≤ timeBound (timeTarget parameter) ∧
          execution.spaceWords ≤ spaceBound (spaceTarget x) := by
    intro x member
    have fits : timeWidth overhead x (pointTime x) ≤ wordWidths x := by
      rw [fiber parameter legal x member]
      exact admitted x member
    obtain ⟨depth, execution, timed, spaced⟩ :=
      runs x (supported parameter legal x member) (wordWidths x) fits
    exact ⟨depth, execution, by simpa only [fiber parameter legal x member] using timed, spaced⟩
  constructor
  · calc
      program.expectedSteps (law parameter) wordWidths
          ≤ ∑' x, law parameter x * (timeBound (timeTarget parameter) : ℝ≥0∞) := by
            apply ENNReal.tsum_le_tsum
            intro x
            by_cases member : x ∈ (law parameter).support
            · obtain ⟨depth, execution, timed, _⟩ := executed x member
              rw [actualSteps_eq execution]
              exact mul_le_mul_left' (Nat.cast_le.mpr timed) (law parameter x)
            · have zeroMass := ((law parameter).apply_eq_zero_iff x).mpr member
              simp only [zeroMass, zero_mul, le_refl]
      _ = (timeBound (timeTarget parameter) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · intro x member
    obtain ⟨depth, execution, _, spaced⟩ := executed x member
    exact ⟨depth, execution, spaced⟩

/-- The minimum admitted width function always provides successful executions
on the whole PMF support. This also gives almost-sure termination for its law. -/
theorem ExpectedTimeSpaceOOn.runs {program : Complexity.Program α β}
    {parameterValid : κ → Prop} {law : κ → PMF α} {valid : α → Prop}
    {timeTarget : κ → Nat} {spaceTarget : α → Nat}
    (bounds : program.ExpectedTimeSpaceOOn parameterValid law valid timeTarget spaceTarget) :
    ∃ overhead, ∀ parameter, parameterValid parameter →
      ∀ x ∈ (law parameter).support,
        ∃ depth, Nonempty (program.Execution x
          (timeWidth overhead x (timeTarget parameter)) depth) := by
  obtain ⟨_, overhead, _, _, _, _, runs⟩ := bounds
  refine ⟨overhead, ?_⟩
  intro parameter legal x member
  obtain ⟨_, space⟩ := runs parameter legal
    (fun raw => timeWidth overhead raw (timeTarget parameter)) (fun _ _ => le_rfl)
  obtain ⟨depth, execution, _⟩ := space x member
  exact ⟨depth, ⟨execution⟩⟩

/-- Source correctness remains independent of the average resource contract.
Output, samplewise space and the integrand all observe this same execution. -/
theorem ExpectedTimeSpaceOOn.runs_correct {program : Complexity.Program α β}
    {parameterValid : κ → Prop} {law : κ → PMF α} {valid : α → Prop}
    {post : α → β → Prop} {timeTarget : κ → Nat} {spaceTarget : α → Nat}
    (bounds : program.ExpectedTimeSpaceOOn parameterValid law valid timeTarget spaceTarget)
    (correct : program.Correct valid post) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ parameter, parameterValid parameter → ∀ wordWidths : α → Nat,
        (∀ x ∈ (law parameter).support,
          timeWidth overhead x (timeTarget parameter) ≤ wordWidths x) →
        program.expectedSteps (law parameter) wordWidths ≤
            (timeBound (timeTarget parameter) : ℝ≥0∞) ∧
          ∀ x ∈ (law parameter).support,
            ∃ depth, ∃ execution : program.Execution x (wordWidths x) depth,
              (∃ output, execution.Represents output ∧ post x output) ∧
              program.actualSteps x (wordWidths x) = (execution.result.steps : ℝ≥0∞) ∧
              execution.spaceWords ≤ spaceBound (spaceTarget x) := by
  obtain ⟨supported, overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro parameter legal wordWidths admitted
  obtain ⟨timed, space⟩ := runs parameter legal wordWidths admitted
  refine ⟨timed, ?_⟩
  intro x member
  obtain ⟨depth, execution, spaced⟩ := space x member
  exact ⟨depth, execution, correct.post_of_execution (supported parameter legal x member) execution,
    actualSteps_eq execution, spaced⟩

/-- Parsed observation of the same raw-input distribution. The parser does not
load a decoded sample or provide free preprocessing to the program. -/
abbrev ExpectedTimeSpaceOParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop)
    (parameterValid : κ → Prop) (law : κ → PMF α)
    (timeTarget : κ → Nat) (spaceGrowth : ι → Nat) : Prop :=
  program.ExpectedTimeSpaceOOn parameterValid law
    (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    timeTarget (fun raw => ((parseInput raw).map spaceGrowth).getD 0)

theorem TimeSpaceOParsed.to_expected {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid : ι → Prop} {pointTime spaceGrowth : ι → Nat}
    (bounds : program.TimeSpaceOParsed parseInput valid pointTime spaceGrowth)
    (parameterValid : κ → Prop) (law : κ → PMF α) (timeTarget : κ → Nat)
    (supported : ∀ parameter, parameterValid parameter →
      ∀ raw ∈ (law parameter).support,
        ∃ input, parseInput raw = some input ∧ valid input)
    (fiber : ∀ parameter, parameterValid parameter →
      ∀ raw ∈ (law parameter).support, ∀ input, parseInput raw = some input →
        pointTime input = timeTarget parameter) :
    program.ExpectedTimeSpaceOParsed parseInput valid parameterValid law timeTarget spaceGrowth := by
  apply TimeSpaceOOn.to_expected bounds parameterValid law timeTarget supported
  intro parameter legal raw member
  obtain ⟨input, parsed, _⟩ := supported parameter legal raw member
  simp only [parsed, Option.map_some, Option.getD_some, fiber parameter legal raw member input parsed]

theorem ExpectedTimeSpaceOParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {parameterValid : κ → Prop} {law : κ → PMF α} {valid : ι → Prop}
    {post : ι → ο → Prop} {timeTarget : κ → Nat} {spaceGrowth : ι → Nat}
    (bounds : program.ExpectedTimeSpaceOParsed parseInput valid parameterValid law timeTarget spaceGrowth)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ parameter, parameterValid parameter → ∀ wordWidths : α → Nat,
        (∀ raw ∈ (law parameter).support,
          timeWidth overhead raw (timeTarget parameter) ≤ wordWidths raw) →
        program.expectedSteps (law parameter) wordWidths ≤
            (timeBound (timeTarget parameter) : ℝ≥0∞) ∧
          ∀ raw ∈ (law parameter).support, ∀ input, parseInput raw = some input →
            ∃ depth, ∃ execution : program.Execution raw (wordWidths raw) depth,
              (∃ output answer, execution.Represents output ∧
                parseOutput output = some answer ∧ post input answer) ∧
              program.actualSteps raw (wordWidths raw) = (execution.result.steps : ℝ≥0∞) ∧
              execution.spaceWords ≤ spaceBound (spaceGrowth input) := by
  obtain ⟨supported, overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro parameter legal wordWidths admitted
  obtain ⟨timed, space⟩ := runs parameter legal wordWidths admitted
  refine ⟨timed, ?_⟩
  intro raw member input parsed
  obtain ⟨expected, decoded, validInput⟩ := supported parameter legal raw member
  have same : expected = input := Option.some.inj (decoded.symm.trans parsed)
  subst expected
  obtain ⟨depth, execution, spaced⟩ := space raw member
  refine ⟨depth, execution, correct.post_of_execution parsed validInput execution,
    actualSteps_eq execution, ?_⟩
  simpa only [parsed, Option.map_some, Option.getD_some] using spaced

end Complexity.Program
