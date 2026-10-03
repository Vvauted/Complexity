/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Basic

/-!
# Program specifications through fixed input and output parsers

A program receives and returns its raw interface values. Fixed specification
parsers interpret those values as the original mathematical objects. The source
need not construct the parser's records or lists: it may scan the raw input or
choose its own working representation. Only the actual source computation runs.

The interface author fixes both parsers, independently of a candidate or answer.
A task must establish that every intended legal instance has an accepted input
encoding. Parsers must describe the external format, not precompute a solution.
Their mathematical evaluation neither executes a host callback in the source
nor supplies decoded objects as extra arguments or initial heap objects.

Correctness requires successful source termination and a valid actual output.
It has no time, word-range or memory-capacity premise.
-/

namespace Complexity.Program

universe u v w z
variable {α : Type u} {β : Type v} {ι : Type w} {ο : Type z}
variable [Input α] [Output β]

/-- Interpret the actual raw input and output using author-fixed format parsers,
while retaining the original mathematical legal domain and postcondition. -/
def CorrectParsed (program : Complexity.Program α β)
    (parseInput : α → Option ι) (parseOutput : β → Option ο)
    (valid : ι → Prop) (post : ι → ο → Prop) : Prop :=
  ∀ raw input, parseInput raw = some input → valid input →
    ∃ output answer, program.Returns raw output ∧
      parseOutput output = some answer ∧ post input answer

/-- Parsed correctness is the existing total-correctness contract on raw
values. Parsing changes only the specification, not the selected program. -/
theorem correctParsed_iff_correct {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop} :
    program.CorrectParsed parseInput parseOutput valid post ↔
      program.Correct (fun raw => ∃ input, parseInput raw = some input ∧ valid input)
        (fun raw output => ∃ input answer, parseInput raw = some input ∧
          parseOutput output = some answer ∧ post input answer) := by
  constructor
  · intro correct raw legal
    obtain ⟨input, parsed, valid⟩ := legal
    obtain ⟨output, answer, returned, decoded, property⟩ :=
      correct raw input parsed valid
    exact ⟨output, returned, input, answer, parsed, decoded, property⟩
  · intro correct raw input parsed legal
    obtain ⟨output, returned, input', answer, parsed', decoded, property⟩ :=
      correct raw ⟨input, parsed, legal⟩
    have same : input = input' := Option.some.inj (parsed.symm.trans parsed')
    exact ⟨output, answer, returned, decoded, same.symm ▸ property⟩

/-- Reuse the same raw computation on a restricted domain or weaker post. -/
theorem CorrectParsed.mono {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid valid' : ι → Prop} {post post' : ι → ο → Prop}
    (correct : program.CorrectParsed parseInput parseOutput valid post)
    (inputs : ∀ input, valid' input → valid input)
    (outputs : ∀ input answer, valid' input → post input answer → post' input answer) :
    program.CorrectParsed parseInput parseOutput valid' post' := by
  intro raw input parsed legal
  obtain ⟨output, answer, returned, decoded, property⟩ :=
    correct raw input parsed (inputs input legal)
  exact ⟨output, answer, returned, decoded, outputs input answer legal property⟩

/-- A format round trip ensures that each legal mathematical instance is
actually covered. The encoder here is specification data, not source advice. -/
theorem CorrectParsed.on_encoded {program : Complexity.Program α β}
    {parseInput : α → Option ι} {parseOutput : β → Option ο}
    {valid : ι → Prop} {post : ι → ο → Prop}
    (correct : program.CorrectParsed parseInput parseOutput valid post)
    (encode : ι → α)
    (roundtrip : ∀ input, valid input → parseInput (encode input) = some input)
    {input : ι} (legal : valid input) :
    ∃ output answer, program.Returns (encode input) output ∧
      parseOutput output = some answer ∧ post input answer :=
  correct (encode input) input (roundtrip input legal) legal

end Complexity.Program
