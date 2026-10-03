/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Parsed
import Complexity.Computability.Ram.Compiler.Language.Program

/-!
# RAM bounds for programs specified through external formats

The machine starts with the raw input, not the parser's mathematical object.
The original mathematical size supplies the bound, while word-width admission
continues to use the raw input's fixed physical presentation. Actual parsing,
reads, working allocation and output construction belong to the same source
program and its counted compiled execution.

Specification parsers are only mathematical observations. This module does not
implement text I/O, decimal parsing, a streaming driver or a free preprocessing
call. A word-token boundary and a byte-text boundary have different input sizes
and must be declared by the task.
-/

namespace Complexity.Program

universe u v w z
variable {α : Type u} {β : Type v} {ι : Type w} {ο : Type z}
variable [Input α] [Output β] [RamInput α]

/-- Apply the original mathematical growth expression to decoded legal inputs,
using the existing uniform same-program RAM bound on the actual raw inputs. -/
abbrev TimeOParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (valid : ι → Prop) (growth : ι → Nat) : Prop :=
  program.TimeOOn (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
    (fun raw => ((parseInput raw).map growth).getD 0)

/-- Independent parsed correctness identifies this very execution's output. -/
theorem CorrectParsed.post_of_execution {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop}
    (correct : program.CorrectParsed parseInput parseOutput valid post)
    {raw : α} {input : ι} (parsed : parseInput raw = some input) (legal : valid input)
    {w depth : Nat} (execution : program.Execution raw w depth) :
    ∃ output answer, execution.Represents output ∧
      parseOutput output = some answer ∧ post input answer := by
  obtain ⟨output, answer, returned, decoded, property⟩ := correct raw input parsed legal
  exact ⟨output, answer, returned.result_of_eval execution.source, decoded, property⟩

/-- The original mathematical postcondition and time bound hold for the same
actual raw-input execution at every admitted width. Decoded data is not loaded
into the machine or used to choose a second computation. -/
theorem TimeOParsed.runs_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop} {growth : ι → Nat}
    (time : program.TimeOParsed parseInput valid growth)
    (correct : program.CorrectParsed parseInput parseOutput valid post) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ raw input, parseInput raw = some input → valid input →
        ∀ w, width overhead raw ≤ w →
          ∃ depth, ∃ execution : program.Execution raw w depth,
            (∃ output answer, execution.Represents output ∧
              parseOutput output = some answer ∧ post input answer) ∧
            execution.result.steps ≤ bound (growth input) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro raw input parsed legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs raw ⟨input, parsed, legal⟩ w admitted
  refine ⟨depth, execution, correct.post_of_execution parsed legal execution, ?_⟩
  simpa only [parsed, Option.map_some, Option.getD_some] using bounded

end Complexity.Program
