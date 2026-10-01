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
# Initialized arrays of composite values

One source expression allocates every actual field column, including nested
products and represented scalar fields. Its ordinary mathematical contract does
not expose the columns. The allocation proof preserves existing input arrays.
The triple allocator's inferred RAM body budget counts all three calls and the
generated wrapper; it is conditional on readiness, not a whole-program TimeO.
-/

namespace Complexity.Examples.CompositeArrays

structure Entry where
  label : Char
  value : Int
  enabled : Bool
  deriving Complexity.Program.Input, Complexity.Program.RamInput, Complexity.Program.Output

source_program Columns where
  def triples (input : Nat × (Nat × Nat × Nat)) : Array (Nat × Nat × Nat) := do
    return Array.replicate input.1 input.2

  def entries (input : Nat × Entry) : Array Entry := do
    return Array.replicate input.1 input.2

  def retain (input : Array Nat × Entry) : Char := do
    let entries := Array.replicate input.1.size input.2
    let index := input.1.getD 0 0
    let selected := entries.getD index input.2
    return selected.label

def triples : Complexity.Program (Nat × (Nat × Nat × Nat)) (Array (Nat × Nat × Nat)) :=
  program% Columns.triples

theorem triples_correct : triples.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 input.2) := by
  program_correct Columns.triples using fun _ => rfl

def entries : Complexity.Program (Nat × Entry) (Array Entry) := program% Columns.entries

theorem entries_correct : entries.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 input.2) := by
  program_correct Columns.entries using fun _ => rfl

def retain : Complexity.Program (Array Nat × Entry) Char := program% Columns.retain

theorem retain_correct : retain.Correct (fun _ => True)
    (fun input result => result =
      ((Array.replicate input.1.size input.2).getD (input.1.getD 0 0) input.2).label) := by
  program_correct Columns.retain using fun _ => rfl

open Complexity.Language Ram.LanguageCompiler
open Columns.Operations.arrayReplicate0

/-- The generated allocator composes the existing scalar certificates and real instructions. -/
def tripleBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Nat × Nat × Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateId)
        ⟨replicate_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateBody
    ⟨replicate_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Three actual initialized columns contribute their linear costs. -/
theorem tripleBodyCost_linear (length : Nat) :
    (tripleBodyCost length).val = 42 * length + (tripleBodyCost 0).val := by
  simp only [tripleBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length]
  ring

end Complexity.Examples.CompositeArrays
