/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.Extract
import Complexity.Computability.Ram.Compiler.Language.Buffer.Rebase
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Buffer

/-!
# Costs of canonical ragged-array extraction

The actual source copies the selected boundary interval, including its sentinel,
and borrows the payload. The bound is linear in the boundary count, independently
of the payload length. It includes allocation, rebasing and the imported call;
source correctness and finite-word arena readiness remain separate.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.Extract

open Complexity.Language
open Complexity.Language.Buffer.Ragged.Extract

private abbrev extractNatCost (count : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (offsets : Array Nat)
      (storage : Buffer .nat × Buffer .nat) (start stop : Nat) (heap : Heap),
      stop + 1 - start = count → storage.1.Contents heap offsets →
      start ≤ stop → stop < offsets.size →
      StmtArenaCostBound program w heapLimit 2 (program.body extractNatId)
        ⟨extractNat_args storage start stop, heap⟩ bound } := ⟨_, by
  intro w heapLimit offsets storage start stop heap sameCount observed ordered bound
  have boundaryStop : start + (stop + 1 - start) = stop + 1 := by omega
  have boundaryFits : start + (stop + 1 - start) ≤ storage.1.length := by
    have size := observed.size_eq
    omega
  have selectedContents := observed.slice boundaryFits
  have selectedSize : (offsets.extract start (start + (stop + 1 - start))).size = count := by
    simp only [Array.size_extract, boundaryStop, Nat.min_eq_left (by omega : stop + 1 ≤ offsets.size)]
    exact sameCount
  change StmtArenaCostBound program w heapLimit 2 extractNatBody
    ⟨extractNat_args storage start stop, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost
    apply StmtArenaCostBound.read_uniform
    intro first
    ram_source_arena_cost
    apply StmtArenaCostBound.read_uniform
    intro last
    ram_source_arena_cost
    apply StmtArenaCostBound.slice_of_success
    intro selected sliced
    change storage.1.slice start (stop + 1 - start) = .ok selected at sliced
    have same := Except.ok.inj (sliced.symm.trans (storage.1.slice_eq boundaryFits))
    subst selected
    ram_source_arena_cost [
      (BufferRebase.copy_arenaCostBound
        (offsets.extract start (start + (stop + 1 - start))) w heapLimit)
        at (_, first) via imports.Rebase.embedding]
    apply StmtArenaCostBound.slice_uniform
    intro cells
    ram_source_arena_cost
  · simp only [selectedSize]
    exact Nat.le_refl _⟩

/-- Core instruction envelope for nat payloads, inferred from the actual source. -/
def extractNatCoreBound (count : Nat) : Nat := (extractNatCost count).val

/-- Every copied boundary pays for initialization and one rebasing iteration. -/
theorem extractNatCoreBound_eq (count : Nat) :
    extractNatCoreBound count =
      (14 + BufferRebase.copyIntoGuardCost.val + BufferRebase.copyIntoBodyCost.val + 10) *
        count + extractNatCoreBound 0 := by
  simp only [extractNatCoreBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [BufferRebase.copyBodyBound_eq count]
  ring

/-- Callable extraction cost on the same canonical row interval, including setup. -/
theorem extractNat_arenaCostBound (rows : Array (Array Nat)) (w heapLimit : Nat) :
    FunctionArenaCostBound program (program.body extractNatId)
      (fun args : (Buffer .nat × Buffer .nat) × Nat × Nat =>
        extractNat_args args.1 args.2.1 args.2.2)
      (fun args heap => (Representation.raggedArray .nat).Rel rows args.1 heap ∧
        args.2.1 ≤ args.2.2 ∧ args.2.2 ≤ rows.size)
      w heapLimit 2 (fun args => extractNatCoreBound (args.2.2 + 1 - args.2.1) + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap allowed
  exact (extractNatCost _).property w heapLimit rows.flattenOffsets
    args.1 args.2.1 args.2.2 heap rfl allowed.1.1 allowed.2.1
    (by simpa only [Array.size_flattenOffsets] using Nat.lt_succ_of_le allowed.2.2)

private abbrev extractBoolCost (count : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (offsets : Array Nat)
      (storage : Buffer .nat × Buffer .bool) (start stop : Nat) (heap : Heap),
      stop + 1 - start = count → storage.1.Contents heap offsets →
      start ≤ stop → stop < offsets.size →
      StmtArenaCostBound program w heapLimit 2 (program.body extractBoolId)
        ⟨extractBool_args storage start stop, heap⟩ bound } := ⟨_, by
  intro w heapLimit offsets storage start stop heap sameCount observed ordered bound
  have boundaryStop : start + (stop + 1 - start) = stop + 1 := by omega
  have boundaryFits : start + (stop + 1 - start) ≤ storage.1.length := by
    have size := observed.size_eq
    omega
  have selectedContents := observed.slice boundaryFits
  have selectedSize : (offsets.extract start (start + (stop + 1 - start))).size = count := by
    simp only [Array.size_extract, boundaryStop, Nat.min_eq_left (by omega : stop + 1 ≤ offsets.size)]
    exact sameCount
  change StmtArenaCostBound program w heapLimit 2 extractBoolBody
    ⟨extractBool_args storage start stop, heap⟩ _
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost
    apply StmtArenaCostBound.read_uniform
    intro first
    ram_source_arena_cost
    apply StmtArenaCostBound.read_uniform
    intro last
    ram_source_arena_cost
    apply StmtArenaCostBound.slice_of_success
    intro selected sliced
    change storage.1.slice start (stop + 1 - start) = .ok selected at sliced
    have same := Except.ok.inj (sliced.symm.trans (storage.1.slice_eq boundaryFits))
    subst selected
    ram_source_arena_cost [
      (BufferRebase.copy_arenaCostBound
        (offsets.extract start (start + (stop + 1 - start))) w heapLimit)
        at (_, first) via imports.Rebase.embedding]
    apply StmtArenaCostBound.slice_uniform
    intro cells
    ram_source_arena_cost
  · simp only [selectedSize]
    exact Nat.le_refl _⟩

/-- Core instruction envelope for bool payloads, inferred from the actual source. -/
def extractBoolCoreBound (count : Nat) : Nat := (extractBoolCost count).val

/-- Every copied boundary pays for initialization and one rebasing iteration. -/
theorem extractBoolCoreBound_eq (count : Nat) :
    extractBoolCoreBound count =
      (14 + BufferRebase.copyIntoGuardCost.val + BufferRebase.copyIntoBodyCost.val + 10) *
        count + extractBoolCoreBound 0 := by
  simp only [extractBoolCoreBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [BufferRebase.copyBodyBound_eq count]
  ring

/-- Callable extraction cost on the same canonical row interval, including setup. -/
theorem extractBool_arenaCostBound (rows : Array (Array Bool)) (w heapLimit : Nat) :
    FunctionArenaCostBound program (program.body extractBoolId)
      (fun args : (Buffer .nat × Buffer .bool) × Nat × Nat =>
        extractBool_args args.1 args.2.1 args.2.2)
      (fun args heap => (Representation.raggedArray .bool).Rel rows args.1 heap ∧
        args.2.1 ≤ args.2.2 ∧ args.2.2 ≤ rows.size)
      w heapLimit 2 (fun args => extractBoolCoreBound (args.2.2 + 1 - args.2.1) + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap allowed
  exact (extractBoolCost _).property w heapLimit rows.flattenOffsets
    args.1 args.2.1 args.2.2 heap rfl allowed.1.1 allowed.2.1
    (by simpa only [Array.size_flattenOffsets] using Nat.lt_succ_of_le allowed.2.2)

end Ram.LanguageCompiler.Buffer.Ragged.Extract
