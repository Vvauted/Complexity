/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prod.Replicate
import Complexity.Computability.Ram.Compiler.Language.Buffer.Replicate
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Mathlib.Tactic.Ring

/-!
# Allocation-aware costs of scalar-pair replication

The actual body calls the two scalar allocators and constructs the returned
pair. Its budget is inferred from their existing allocation certificates,
the imported-call rules and real local instructions. Function initialization
is included once. Length zero retains both real calls and their fixed costs.

These conditional contracts require the same execution and arena readiness.
They do not provide word bounds, capacity or a whole-program TimeO theorem.
-/

namespace Ram.LanguageCompiler.Buffer.Prod.Replicate

open Complexity.Language
open Complexity.Language.Buffer.Prod.Replicate

/-- Infer the actual pair body's budget, including both imported allocator calls. -/
def replicateNatNatBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Nat × Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateNatNatId)
        ⟨replicateNatNat_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateNatNatBody
    ⟨replicateNatNat_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Both initialized columns contribute their compiler-derived linear allocation costs. -/
theorem replicateNatNatBodyCost_linear (length : Nat) :
    (replicateNatNatBodyCost length).val = 28 * length + (replicateNatNatBodyCost 0).val := by
  simp only [replicateNatNatBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length]
  ring

/-- The function wrapper adds its real initialization once, at the caller's depth. -/
theorem replicateNatNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateNatNatId)
      (fun input : Nat × (Nat × Nat) => replicateNatNat_args input.1 input.2)
      (fun _ _ => True) w heapLimit (depth + 1)
      (fun input => (replicateNatNatBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateNatNatBodyCost input.1).property w heapLimit depth input.2 heap)

/-- Infer the actual pair body's budget, including both imported allocator calls. -/
def replicateNatBoolBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Nat × Bool) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateNatBoolId)
        ⟨replicateNatBool_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateNatBoolBody
    ⟨replicateNatBool_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding,
      (Ram.LanguageCompiler.Buffer.Replicate.replicateBool_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Both initialized columns contribute their compiler-derived linear allocation costs. -/
theorem replicateNatBoolBodyCost_linear (length : Nat) :
    (replicateNatBoolBodyCost length).val = 28 * length + (replicateNatBoolBodyCost 0).val := by
  simp only [replicateNatBoolBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length,
    Ram.LanguageCompiler.Buffer.Replicate.replicateBoolBodyCost_linear length]
  ring

/-- The function wrapper adds its real initialization once, at the caller's depth. -/
theorem replicateNatBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateNatBoolId)
      (fun input : Nat × (Nat × Bool) => replicateNatBool_args input.1 input.2)
      (fun _ _ => True) w heapLimit (depth + 1)
      (fun input => (replicateNatBoolBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateNatBoolBodyCost input.1).property w heapLimit depth input.2 heap)

/-- Infer the actual pair body's budget, including both imported allocator calls. -/
def replicateBoolNatBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Bool × Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateBoolNatId)
        ⟨replicateBoolNat_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateBoolNatBody
    ⟨replicateBoolNat_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateBool_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding,
      (Ram.LanguageCompiler.Buffer.Replicate.replicateNat_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Both initialized columns contribute their compiler-derived linear allocation costs. -/
theorem replicateBoolNatBodyCost_linear (length : Nat) :
    (replicateBoolNatBodyCost length).val = 28 * length + (replicateBoolNatBodyCost 0).val := by
  simp only [replicateBoolNatBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateBoolBodyCost_linear length,
    Ram.LanguageCompiler.Buffer.Replicate.replicateNatBodyCost_linear length]
  ring

/-- The function wrapper adds its real initialization once, at the caller's depth. -/
theorem replicateBoolNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateBoolNatId)
      (fun input : Nat × (Bool × Nat) => replicateBoolNat_args input.1 input.2)
      (fun _ _ => True) w heapLimit (depth + 1)
      (fun input => (replicateBoolNatBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateBoolNatBodyCost input.1).property w heapLimit depth input.2 heap)

/-- Infer the actual pair body's budget, including both imported allocator calls. -/
def replicateBoolBoolBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Bool × Bool) (heap : Heap),
      StmtArenaCostBound program w heapLimit (depth + 1) (program.body replicateBoolBoolId)
        ⟨replicateBoolBool_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit (depth + 1) replicateBoolBoolBody
    ⟨replicateBoolBool_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost [
      (Ram.LanguageCompiler.Buffer.Replicate.replicateBool_arenaCostBound w heapLimit depth)
        at (length, _)
        via imports.Complexity.Language.Buffer.Replicate.embedding]
  · dsimp only
    exact Nat.le_refl _⟩

/-- Both initialized columns contribute their compiler-derived linear allocation costs. -/
theorem replicateBoolBoolBodyCost_linear (length : Nat) :
    (replicateBoolBoolBodyCost length).val = 28 * length + (replicateBoolBoolBodyCost 0).val := by
  simp only [replicateBoolBoolBodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  simp only [Ram.LanguageCompiler.Buffer.Replicate.replicateBoolBodyCost_linear length]
  ring

/-- The function wrapper adds its real initialization once, at the caller's depth. -/
theorem replicateBoolBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateBoolBoolId)
      (fun input : Nat × (Bool × Bool) => replicateBoolBool_args input.1 input.2)
      (fun _ _ => True) w heapLimit (depth + 1)
      (fun input => (replicateBoolBoolBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateBoolBoolBodyCost input.1).property w heapLimit depth input.2 heap)

end Ram.LanguageCompiler.Buffer.Prod.Replicate
