/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax
import Complexity.Computability.Ram.Compiler.Language.Buffer.Replicate
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Mathlib.Tactic.Ring

/-!
# Ordinary String contracts over real character buffers

Character-indexed reads, initialized strings and string rows reuse the existing
buffer operations. Their mathematical equations use ordinary String/List APIs;
no arbitrary `toList` conversion or UTF-8 byte indexing is introduced.
The allocation bound counts the generated caller and initialized cells, conditional
on arena readiness. It is not a complete whole-program time certificate.
-/

namespace Complexity.Examples.Strings

structure Input where
  words : Array String
  row : Nat
  column : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program Text where
  def replicate (length : Nat) (initial : Char) : String := do
    return String.ofList (List.replicate length initial)

  def lookup (text : String) (index : Nat) : Char := do
    return text.toList.getD index 'λ'

  def length (text : String) : Nat := do
    return String.length text

  def row (input : Input) : String := do
    let fallback : String := ""
    return input.words.getD input.row fallback

  def repeatSelected (input : Input) : String := do
    let fallback : String := ""
    let selected := input.words.getD input.row fallback
    let character := selected.toList.getD input.column '🦉'
    return String.ofList (List.replicate selected.length character)

def repeated : Complexity.Program (Nat × Char) String := program% Text.replicate

theorem repeated_correct : repeated.Correct (fun _ => True)
    (fun input result => result = String.ofList (List.replicate input.1 input.2)) := by
  program_correct Text.replicate using fun _ _ => rfl

def lookup : Complexity.Program (String × Nat) Char := program% Text.lookup

theorem lookup_correct : lookup.Correct (fun _ => True)
    (fun input result => result = input.1.toList.getD input.2 'λ') := by
  program_correct Text.lookup using fun _ _ => rfl

def length : Complexity.Program String Nat := program% Text.length

theorem length_correct : length.Correct (fun _ => True)
    (fun input result => result = input.length) := by
  program_correct Text.length using fun _ => rfl

def row : Complexity.Program Input String := program% Text.row

theorem row_correct : row.Correct (fun _ => True)
    (fun input result => result = input.words.getD input.row "") := by
  program_correct Text.row using fun _ => by simp [Text.row_model]

def repeatSelected : Complexity.Program Input String := program% Text.repeatSelected

theorem repeatSelected_correct : repeatSelected.Correct (fun _ => True)
    (fun input result =>
      let selected := input.words.getD input.row ""
      result = String.ofList (List.replicate selected.length
        (selected.toList.getD input.column '🦉'))) := by
  program_correct Text.repeatSelected using fun _ => by simp [Text.repeatSelected_model]

open Complexity.Language Ram.LanguageCompiler Text

/-- Infer the budget from the same real allocator call, including the source wrapper. -/
def replicateBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth initial : Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateId)
        ⟨replicate_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateBody
    ⟨replicate_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _) via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- The initialized code-point cells carry the existing allocator's linear charge. -/
theorem replicateBodyCost_linear (length : Nat) :
    (replicateBodyCost length).val = 14 * length + (replicateBodyCost 0).val := by
  simp only [replicateBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length]
  ring

end Complexity.Examples.Strings
