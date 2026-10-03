/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Space
import Complexity.Computability.Ram.Compiler.Language.Program.Parsed

/-!
# Physical-word space through fixed external formats

Author-fixed mathematical parsers observe the raw interface; they neither run
as host callbacks nor preload decoded objects or algorithmic advice. Only the
selected program executes. If it parses or converts data, its actual accesses
and allocation remain part of that execution.

Space counts the initialized input arena prefix together with distinct physical
addresses accessed by the whole compiled invocation, including stack accesses.
It is not capacity, final heap size, or peak reachable-live storage. The fixed
budget includes width admission and execution existence on every legal input;
the asymptotic interface keeps the uniform raw-input width policy. Correctness
remains the independent, budget-free `CorrectParsed` contract.
-/

namespace Complexity.Program

universe u v w z
variable {α : Type u} {β : Type v} {ι : Type w} {ο : Type z}
variable [Input α] [Output β] [RamInput α]

/-- A finite decoded-input space budget at one author-fixed word width.
Machine fit is an obligation on each legal raw input, not a domain filter. -/
abbrev SpaceBoundParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop) (wordWidth : Nat)
    (budget : ι → Nat) : Prop :=
  program.SpaceBound (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    wordWidth (fun raw => ((parseInput raw).map budget).getD 0)

/-- A decoded mathematical growth target with uniform same-program space
over the fixed raw interface. Decoding does not supply free preprocessing. -/
abbrev SpaceOParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop) (growth : ι → Nat) : Prop :=
  program.SpaceOOn (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    (fun raw => ((parseInput raw).map growth).getD 0)

/-- Restrict legal decoded inputs and enlarge their finite budgets, retaining
the same width and actual program. -/
theorem SpaceBoundParsed.mono {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid valid' : ι → Prop}
    {wordWidth : Nat} {budget budget' : ι → Nat}
    (space : program.SpaceBoundParsed parseInput valid wordWidth budget)
    (inputs : ∀ input, valid' input → valid input)
    (budgets : ∀ input, valid' input → budget input ≤ budget' input) :
    program.SpaceBoundParsed parseInput valid' wordWidth budget' := by
  apply SpaceBound.mono space
  · rintro raw ⟨input, parsed, legal⟩
    exact ⟨input, parsed, inputs input legal⟩
  · rintro raw ⟨input, parsed, legal⟩
    simpa only [parsed, Option.map_some, Option.getD_some] using budgets input legal

/-- Reuse the same finite budget on a decoded subtask. -/
theorem SpaceBoundParsed.mono_valid {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid valid' : ι → Prop}
    {wordWidth : Nat} {budget : ι → Nat}
    (space : program.SpaceBoundParsed parseInput valid wordWidth budget)
    (inputs : ∀ input, valid' input → valid input) :
    program.SpaceBoundParsed parseInput valid' wordWidth budget :=
  SpaceBoundParsed.mono space inputs (fun _ _ => Nat.le_refl _)

/-- Restrict the decoded legal domain without changing the growth target or
the uniform raw-input width policy. -/
theorem SpaceOParsed.mono_valid {program : Complexity.Program α β}
    {parseInput : α → Option ι} {valid valid' : ι → Prop} {growth : ι → Nat}
    (space : program.SpaceOParsed parseInput valid growth)
    (inputs : ∀ input, valid' input → valid input) :
    program.SpaceOParsed parseInput valid' growth := by
  apply SpaceO.mono_valid space
  rintro raw ⟨input, parsed, legal⟩
  exact ⟨input, parsed, inputs input legal⟩

/-- Exact decoded correctness and the finite physical-word budget concern
the same actual execution at the fixed author width. -/
theorem SpaceBoundParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop}
    {wordWidth : Nat} {budget : ι → Nat}
    (space : program.SpaceBoundParsed parseInput valid wordWidth budget)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∀ raw input, parseInput raw = some input → valid input →
      ∃ admitted : width 0 raw ≤ wordWidth,
        ∃ depth, ∃ execution : program.Execution raw wordWidth depth,
          (∃ output answer, execution.Represents output ∧
            parseOutput output = some answer ∧ post input answer) ∧
          execution.spaceWords ≤ budget input := by
  intro raw input parsed legal
  obtain ⟨admitted, depth, execution, bounded⟩ := space raw ⟨input, parsed, legal⟩
  refine ⟨admitted, depth, execution, correct.post_of_execution parsed legal execution, ?_⟩
  simpa only [parsed, Option.map_some, Option.getD_some] using bounded

/-- The original mathematical postcondition and uniform space envelope hold
for the very same raw-input execution at every admitted width. -/
theorem SpaceOParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop} {growth : ι → Nat}
    (space : program.SpaceOParsed parseInput valid growth)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ raw input, parseInput raw = some input → valid input →
        ∀ w, width overhead raw ≤ w →
          ∃ depth, ∃ execution : program.Execution raw w depth,
            (∃ output answer, execution.Represents output ∧
              parseOutput output = some answer ∧ post input answer) ∧
            execution.spaceWords ≤ bound (growth input) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro raw input parsed legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs raw ⟨input, parsed, legal⟩ w admitted
  refine ⟨depth, execution, correct.post_of_execution parsed legal execution, ?_⟩
  simpa only [parsed, Option.map_some, Option.getD_some] using bounded

end Complexity.Program
