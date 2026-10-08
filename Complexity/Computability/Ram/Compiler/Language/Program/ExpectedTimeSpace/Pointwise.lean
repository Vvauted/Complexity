/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ExpectedTimeSpace
import Complexity.Probability.ProbabilityMassFunction

/-!
# Input-dependent targets under a specified input law

Some input-distribution specifications allow deterministic parameters, such as a
legal query count, to depend on the sampled fields. Do not condition away legal
samples or fix those parameters independently. Instead average an author-fixed
pointwise growth expression under the same law as the execution cost, and require
that right-hand expectation to be finite. This is not internal random sampling.
Correctness remains a separate all-input contract; `actualSteps_eq` and
`CorrectParsed.post_of_execution` connect each sample to its same observed run.
-/

namespace Complexity.Program

open scoped ENNReal

universe u v w r
variable {α : Type u} {β : Type v} {ι : Type w} {κ : Type r}
variable [Input α] [Output β] [RamInput α]

/-- Expected actual time bounded by the finite expectation of a fixed
input-dependent target, with samplewise space for the same executions. -/
def PointwiseExpectedTimeSpaceOOn (program : Complexity.Program α β)
    (parameterValid : κ → Prop) (law : κ → PMF α) (valid : α → Prop)
    (timeGrowth spaceGrowth : α → Nat) : Prop :=
  (∀ parameter, parameterValid parameter →
    ∀ x ∈ (law parameter).support, valid x) ∧
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
    ∀ parameter, parameterValid parameter → ∀ wordWidths : α → Nat,
      (∀ x ∈ (law parameter).support,
        timeWidth overhead x (timeGrowth x) ≤ wordWidths x) →
      (∑' x, law parameter x * (timeBound (timeGrowth x) : ℝ≥0∞)) < ⊤ ∧
      program.expectedSteps (law parameter) wordWidths ≤
          ∑' x, law parameter x * (timeBound (timeGrowth x) : ℝ≥0∞) ∧
        ∀ x ∈ (law parameter).support,
          ∃ depth, ∃ execution : program.Execution x (wordWidths x) depth,
            execution.spaceWords ≤ spaceBound (spaceGrowth x)

/-- Reuse the existing deterministic certificate. Integrability of the selected
linear envelope is an explicit fact about the task's law, never automatic for
arbitrary PMFs. Finite support discharges it using
`PMF.tsum_mul_natCast_lt_top_of_finite_support`. -/
theorem TimeSpaceOOn.to_pointwise_expected {program : Complexity.Program α β}
    {valid : α → Prop} {timeGrowth spaceGrowth : α → Nat}
    (bounds : program.TimeSpaceOOn valid timeGrowth spaceGrowth)
    (parameterValid : κ → Prop) (law : κ → PMF α)
    (supported : ∀ parameter, parameterValid parameter →
      ∀ x ∈ (law parameter).support, valid x)
    (finite : ∀ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ)) (fun n => (n : ℝ)) →
      ∀ parameter, parameterValid parameter →
        (∑' x, law parameter x * (bound (timeGrowth x) : ℝ≥0∞)) < ⊤) :
    program.PointwiseExpectedTimeSpaceOOn parameterValid law valid timeGrowth spaceGrowth := by
  classical
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨supported, overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro parameter legal wordWidths admitted
  have executed := fun x member =>
    runs x (supported parameter legal x member) (wordWidths x) (admitted x member)
  refine ⟨finite timeBound timeAsymptotic parameter legal, ?_, ?_⟩
  · apply ENNReal.tsum_le_tsum
    intro x
    by_cases member : x ∈ (law parameter).support
    · obtain ⟨depth, execution, timed, _⟩ := executed x member
      rw [actualSteps_eq execution]
      exact mul_le_mul_left' (Nat.cast_le.mpr timed) (law parameter x)
    · rw [((law parameter).apply_eq_zero_iff x).mpr member, zero_mul, zero_mul]
  · intro x member
    obtain ⟨depth, execution, _, spaced⟩ := executed x member
    exact ⟨depth, execution, spaced⟩

/-- Specification decoding does not change the actual random raw input. -/
abbrev PointwiseExpectedTimeSpaceOParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop)
    (parameterValid : κ → Prop) (law : κ → PMF α)
    (timeGrowth spaceGrowth : ι → Nat) : Prop :=
  program.PointwiseExpectedTimeSpaceOOn parameterValid law
    (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    (fun raw => ((parseInput raw).map timeGrowth).getD 0)
    (fun raw => ((parseInput raw).map spaceGrowth).getD 0)

theorem TimeSpaceOParsed.to_pointwise_expected {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid : ι → Prop} {timeGrowth spaceGrowth : ι → Nat}
    (bounds : program.TimeSpaceOParsed parseInput valid timeGrowth spaceGrowth)
    (parameterValid : κ → Prop) (law : κ → PMF α)
    (supported : ∀ parameter, parameterValid parameter →
      ∀ raw ∈ (law parameter).support, ∃ input, parseInput raw = some input ∧ valid input)
    (finite : ∀ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ)) (fun n => (n : ℝ)) →
      ∀ parameter, parameterValid parameter →
        (∑' raw, law parameter raw *
          (bound (((parseInput raw).map timeGrowth).getD 0) : ℝ≥0∞)) < ⊤) :
    program.PointwiseExpectedTimeSpaceOParsed parseInput valid parameterValid law
      timeGrowth spaceGrowth :=
  TimeSpaceOOn.to_pointwise_expected bounds parameterValid law supported finite

end Complexity.Program
