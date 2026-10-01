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
The inferred RAM body budgets count every column call and the generated wrapper,
including the optional initializer's packing branch. They are conditional on
readiness, not whole-program TimeO certificates.
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

source_program Optional where
  def naturals (input : Nat × Nat) : Array (Option Nat) := do
    return Array.replicate input.1 (some input.2)

  def missing (length : Nat) : Array (Option Nat) := do
    return Array.replicate length none

  def integers (input : Nat × Int) : Array (Option Int) := do
    return Array.replicate input.1 (some input.2)

  def flags (input : Nat × Bool) : Array (Option Bool) := do
    return Array.replicate input.1 (some input.2)

  def lookup (input : Array (Option Int) × Nat) : Option Int := do
    return input.1.getD input.2 none

  def lookupOr (input : Array (Option Int) × (Nat × Int)) : Option Int := do
    return input.1.getD input.2.1 (some input.2.2)

  def retain (input : Array Nat × Int) : Option Int := do
    let initialized := Array.replicate input.1.size (some input.2)
    let index := input.1.getD 0 0
    return initialized.getD index none

def optionalNaturals : Complexity.Program (Nat × Nat) (Array (Option Nat)) :=
  program% Optional.naturals

theorem optionalNaturals_correct : optionalNaturals.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 (some input.2)) := by
  program_correct Optional.naturals using fun _ => rfl

def missingNaturals : Complexity.Program Nat (Array (Option Nat)) := program% Optional.missing

theorem missingNaturals_correct : missingNaturals.Correct (fun _ => True)
    (fun length result => result = Array.replicate length none) := by
  program_correct Optional.missing using fun _ => rfl

def optionalIntegers : Complexity.Program (Nat × Int) (Array (Option Int)) :=
  program% Optional.integers

theorem optionalIntegers_correct : optionalIntegers.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 (some input.2)) := by
  program_correct Optional.integers using fun _ => rfl

def optionalFlags : Complexity.Program (Nat × Bool) (Array (Option Bool)) :=
  program% Optional.flags

theorem optionalFlags_correct : optionalFlags.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 (some input.2)) := by
  program_correct Optional.flags using fun _ => rfl

def optionalLookup : Complexity.Program (Array (Option Int) × Nat) (Option Int) :=
  program% Optional.lookup

theorem optionalLookup_correct : optionalLookup.Correct (fun _ => True)
    (fun input result => result = input.1.getD input.2 none) := by
  program_correct Optional.lookup using fun _ => rfl

def optionalLookupOr : Complexity.Program (Array (Option Int) × (Nat × Int)) (Option Int) :=
  program% Optional.lookupOr

theorem optionalLookupOr_correct : optionalLookupOr.Correct (fun _ => True)
    (fun input result => result = input.1.getD input.2.1 (some input.2.2)) := by
  program_correct Optional.lookupOr using fun _ => rfl

def optionalRetain : Complexity.Program (Array Nat × Int) (Option Int) := program% Optional.retain

/-- Optional columns allocate normally and preserve the existing input array.
An out-of-range lookup returns the actual optional fallback, not `some 0`. -/
theorem optionalRetain_correct : optionalRetain.Correct (fun _ => True)
    (fun input result => result =
      (Array.replicate input.1.size (some input.2)).getD (input.1.getD 0 0) none) := by
  program_correct Optional.retain using fun _ => rfl

namespace Optional.Operations.arrayReplicate0

/-- The optional allocator pays for its real packing branch and both columns. -/
def bodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Option Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateId)
        ⟨replicate_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateBody
    ⟨replicate_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateBool_arenaCostBound w heapLimit depth)
        at (length, _) via imports.Complexity.Language.Buffer.Replicate.embedding,
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _) via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Presence and payload initialization each contribute their actual linear work. -/
theorem bodyCost_linear (length : Nat) :
    (bodyCost length).val = 28 * length + (bodyCost 0).val := by
  simp only [bodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length,
    Ram.LanguageCompiler.Buffer.Replicate.replicateBoolBodyCost_linear length]
  omega

end Optional.Operations.arrayReplicate0

end Complexity.Examples.CompositeArrays
