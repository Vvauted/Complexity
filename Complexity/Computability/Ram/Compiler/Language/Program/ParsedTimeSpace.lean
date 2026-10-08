/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ParsedSpace
import Complexity.Computability.Ram.Compiler.Language.Program.TimeSpace

/-!
# Parsed adapters for joint public resource contracts

The public joint contract derives its uniform word scale from the declared
time target and raw input, never from the space target or fitted cost envelope.
These interfaces transport author-fixed parsers. They observe raw
inputs/outputs; no decoded advice or second program is loaded.
Space keeps the library's input-seeded physical footprint, not capacity or
peak-live storage. These invocation contracts are not a Session composition rule.
-/

namespace Complexity.Program

universe u v w z
variable {α : Type u} {β : Type v} {ι : Type w} {ο : Type z}
variable [Input α] [Output β] [RamInput α]

/-- The public same-execution contract through a fixed mathematical parser. -/
abbrev TimeSpaceOParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop)
    (timeGrowth spaceGrowth : ι → Nat) : Prop :=
  program.TimeSpaceOOn (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    (fun raw => ((parseInput raw).map timeGrowth).getD 0)
    (fun raw => ((parseInput raw).map spaceGrowth).getD 0)

/-- Preserve existing stronger input-width certificates without redefining them. -/
theorem TimeSpaceOParsed.of_time_space {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid : ι → Prop} {timeGrowth spaceGrowth : ι → Nat}
    (time : program.TimeOParsed parseInput valid timeGrowth)
    (space : program.SpaceOParsed parseInput valid spaceGrowth) :
    program.TimeSpaceOParsed parseInput valid timeGrowth spaceGrowth :=
  TimeSpaceOOn.of_time_space time space

/-- Restrict legal decoded inputs while keeping the same target word scale. -/
theorem TimeSpaceOParsed.mono_valid {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid valid' : ι → Prop}
    {timeGrowth spaceGrowth : ι → Nat}
    (bounds : program.TimeSpaceOParsed parseInput valid timeGrowth spaceGrowth)
    (inputs : ∀ input, valid' input → valid input) :
    program.TimeSpaceOParsed parseInput valid' timeGrowth spaceGrowth := by
  apply TimeSpaceOOn.mono_valid bounds
  rintro raw ⟨input, parsed, legal⟩
  exact ⟨input, parsed, inputs input legal⟩

/-- Both envelopes and the decoded answer describe one actual execution at
every time-admitted width. Source correctness remains budget independent. -/
theorem TimeSpaceOParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop} {timeGrowth spaceGrowth : ι → Nat}
    (bounds : program.TimeSpaceOParsed parseInput valid timeGrowth spaceGrowth)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ raw input, parseInput raw = some input → valid input →
        ∀ wordWidth, timeWidth overhead raw (timeGrowth input) ≤ wordWidth →
          ∃ depth, ∃ execution : program.Execution raw wordWidth depth,
            (∃ output answer, execution.Represents output ∧
              parseOutput output = some answer ∧ post input answer) ∧
            execution.result.steps ≤ timeBound (timeGrowth input) ∧
              execution.spaceWords ≤ spaceBound (spaceGrowth input) := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro raw input parsed legal wordWidth admitted
  have admitted' : timeWidth overhead raw (((parseInput raw).map timeGrowth).getD 0) ≤
      wordWidth := by
    simpa only [parsed, Option.map_some, Option.getD_some] using admitted
  obtain ⟨depth, execution, timed, spaced⟩ :=
    runs raw ⟨input, parsed, legal⟩ wordWidth admitted'
  refine ⟨depth, execution, correct.post_of_execution parsed legal execution, ?_, ?_⟩
  · simpa only [parsed, Option.map_some, Option.getD_some] using timed
  · simpa only [parsed, Option.map_some, Option.getD_some] using spaced

/-- Exact author-fixed budgets through a fixed parser, without asymptotic
coefficients. Width admission remains an obligation on every legal raw input. -/
abbrev TimeSpaceBoundParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop) (wordWidth : Nat)
    (timeBudget spaceBudget : ι → Nat) : Prop :=
  program.TimeSpaceBound (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    wordWidth (fun raw => ((parseInput raw).map timeBudget).getD 0)
    (fun raw => ((parseInput raw).map spaceBudget).getD 0)

/-- Decoded correctness and the two exact caps observe the same fixed-width run. -/
theorem TimeSpaceBoundParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop} {wordWidth : Nat}
    {timeBudget spaceBudget : ι → Nat}
    (bounds : program.TimeSpaceBoundParsed parseInput valid wordWidth timeBudget spaceBudget)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∀ raw input, parseInput raw = some input → valid input →
      ∃ admitted : width 0 raw ≤ wordWidth,
        ∃ depth, ∃ execution : program.Execution raw wordWidth depth,
          (∃ output answer, execution.Represents output ∧
            parseOutput output = some answer ∧ post input answer) ∧
          execution.result.steps ≤ timeBudget input ∧ execution.spaceWords ≤ spaceBudget input := by
  intro raw input parsed legal
  obtain ⟨admitted, depth, execution, timed, spaced⟩ := bounds raw ⟨input, parsed, legal⟩
  refine ⟨admitted, depth, execution, correct.post_of_execution parsed legal execution, ?_, ?_⟩
  · simpa only [parsed, Option.map_some, Option.getD_some] using timed
  · simpa only [parsed, Option.map_some, Option.getD_some] using spaced

end Complexity.Program
