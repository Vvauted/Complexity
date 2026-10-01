/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.Nested
import Complexity.Computability.Ram.Compiler.Language.Buffer.Ragged.Extract

/-!
# Costs of defaulted nested ragged-array reads

An in-bounds read copies exactly the selected row's boundaries and its sentinel,
not its payload. A failed bounds check returns the fallback without allocating.
The uniform envelope is linear in the selected row count (zero out of bounds),
with the actual imported calls and branch instructions included. It does not
supply termination, word ranges, capacity or a whole-program complexity theorem.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.Nested

open Complexity.Language
open Complexity.Language.Buffer.Ragged.Nested

private abbrev getNatCost (count : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (rows : Array (Array (Array Nat)))
      (storage : Buffer .nat × (Buffer .nat × Buffer .nat))
      (index : Nat) (fallback : Buffer .nat × Buffer .nat) (heap : Heap),
      (rows.getD index #[]).size + 1 = count →
      (Representation.raggedArrayOf (Representation.raggedArray .nat)).Rel
        rows storage heap →
      StmtArenaCostBound program w heapLimit 3 (program.body getNatId)
        ⟨getNat_args storage index fallback, heap⟩ bound } := ⟨_, by
  intro w heapLimit rows storage index fallback heap sameCount observed
  have length := Representation.raggedArrayOf_size observed
  change StmtArenaCostBound program w heapLimit 3 getNatBody
    ⟨getNat_args storage index fallback, heap⟩ _
  apply StmtArenaCostBound.mono
  · repeat' apply StmtArenaCostBound.letPrim
    apply StmtArenaCostBound.ite
    · intro selected
      change decide (index < storage.1.length - 1) = true at selected
      have inside : index < rows.size := by
        have available := of_decide_eq_true selected
        omega
      have firstBound : index < rows.flattenOffsets.size := by simp; omega
      have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
      have firstRead := observed.1.read firstBound
      have lastRead := observed.1.read lastBound
      change heap.read storage.1 index = .ok rows.flattenOffsets[index] at firstRead
      change heap.read storage.1 (index + 1) = .ok rows.flattenOffsets[index + 1] at lastRead
      have rowSize := Array.flattenOffsets_succ rows inside
      have ordered : rows.flattenOffsets[index] ≤ rows.flattenOffsets[index + 1] := by omega
      have stopBound := Array.flattenOffsets_le rows (index + 1) lastBound
      have selectedCount :
          rows.flattenOffsets[index + 1] + 1 - rows.flattenOffsets[index] = count := by
        simp only [Array.getD, dif_pos inside] at sameCount
        rw [rowSize]
        simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using sameCount
      apply StmtArenaCostBound.read_of_success
      intro first loadedFirst
      change heap.read storage.1 index = .ok first at loadedFirst
      have sameFirst := Except.ok.inj (loadedFirst.symm.trans firstRead)
      subst first
      ram_source_arena_cost
      apply StmtArenaCostBound.read_of_success
      intro last loadedLast
      change heap.read storage.1 (index + 1) = .ok last at loadedLast
      have sameLast := Except.ok.inj (loadedLast.symm.trans lastRead)
      subst last
      have allowed := And.intro observed.2 (And.intro ordered stopBound)
      apply StmtArenaCostBound.mono
      · ram_source_arena_cost [
          (Extract.extractNat_arenaCostBound rows.flatten w heapLimit)
            at (storage.2, rows.flattenOffsets[index], rows.flattenOffsets[index + 1])
            via imports.Extract.embedding]
      · simp only [selectedCount]
        exact Nat.le_refl _
    · intro _
      ram_source_arena_cost
  · dsimp only
    exact Nat.le_refl _⟩

/-- Uniform core bound; one extra boundary retains the final sentinel. -/
def getNatCoreBound (rowCount : Nat) : Nat := (getNatCost (rowCount + 1)).val

/-- Only the copied boundary count contributes a nonconstant instruction charge. -/
theorem getNatCoreBound_le (rowCount : Nat) :
    getNatCoreBound rowCount ≤
      (14 + BufferRebase.copyIntoGuardCost.val + BufferRebase.copyIntoBodyCost.val + 10) *
        rowCount + getNatCoreBound 0 := by
  simp only [getNatCoreBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [Extract.extractNatCoreBound_eq (rowCount + 1), Extract.extractNatCoreBound_eq 1]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- The callable bound observes the original rows without inspecting a fallback's contents. -/
theorem getNat_arenaCostBound (rows : Array (Array (Array Nat))) (w heapLimit : Nat) :
    FunctionArenaCostBound program (program.body getNatId)
      (fun args : (Buffer .nat × (Buffer .nat × Buffer .nat)) × Nat ×
          (Buffer .nat × Buffer .nat) => getNat_args args.1 args.2.1 args.2.2)
      (fun args heap =>
        (Representation.raggedArrayOf (Representation.raggedArray .nat)).Rel
          rows args.1 heap)
      w heapLimit 3 (fun args => getNatCoreBound (rows.getD args.2.1 #[]).size + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap observed
  exact (getNatCost _).property w heapLimit rows args.1 args.2.1 args.2.2 heap rfl observed

private abbrev getBoolCost (count : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (rows : Array (Array (Array Bool)))
      (storage : Buffer .nat × (Buffer .nat × Buffer .bool))
      (index : Nat) (fallback : Buffer .nat × Buffer .bool) (heap : Heap),
      (rows.getD index #[]).size + 1 = count →
      (Representation.raggedArrayOf (Representation.raggedArray .bool)).Rel
        rows storage heap →
      StmtArenaCostBound program w heapLimit 3 (program.body getBoolId)
        ⟨getBool_args storage index fallback, heap⟩ bound } := ⟨_, by
  intro w heapLimit rows storage index fallback heap sameCount observed
  have length := Representation.raggedArrayOf_size observed
  change StmtArenaCostBound program w heapLimit 3 getBoolBody
    ⟨getBool_args storage index fallback, heap⟩ _
  apply StmtArenaCostBound.mono
  · repeat' apply StmtArenaCostBound.letPrim
    apply StmtArenaCostBound.ite
    · intro selected
      change decide (index < storage.1.length - 1) = true at selected
      have inside : index < rows.size := by
        have available := of_decide_eq_true selected
        omega
      have firstBound : index < rows.flattenOffsets.size := by simp; omega
      have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
      have firstRead := observed.1.read firstBound
      have lastRead := observed.1.read lastBound
      change heap.read storage.1 index = .ok rows.flattenOffsets[index] at firstRead
      change heap.read storage.1 (index + 1) = .ok rows.flattenOffsets[index + 1] at lastRead
      have rowSize := Array.flattenOffsets_succ rows inside
      have ordered : rows.flattenOffsets[index] ≤ rows.flattenOffsets[index + 1] := by omega
      have stopBound := Array.flattenOffsets_le rows (index + 1) lastBound
      have selectedCount :
          rows.flattenOffsets[index + 1] + 1 - rows.flattenOffsets[index] = count := by
        simp only [Array.getD, dif_pos inside] at sameCount
        rw [rowSize]
        simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using sameCount
      apply StmtArenaCostBound.read_of_success
      intro first loadedFirst
      change heap.read storage.1 index = .ok first at loadedFirst
      have sameFirst := Except.ok.inj (loadedFirst.symm.trans firstRead)
      subst first
      ram_source_arena_cost
      apply StmtArenaCostBound.read_of_success
      intro last loadedLast
      change heap.read storage.1 (index + 1) = .ok last at loadedLast
      have sameLast := Except.ok.inj (loadedLast.symm.trans lastRead)
      subst last
      have allowed := And.intro observed.2 (And.intro ordered stopBound)
      apply StmtArenaCostBound.mono
      · ram_source_arena_cost [
          (Extract.extractBool_arenaCostBound rows.flatten w heapLimit)
            at (storage.2, rows.flattenOffsets[index], rows.flattenOffsets[index + 1])
            via imports.Extract.embedding]
      · simp only [selectedCount]
        exact Nat.le_refl _
    · intro _
      ram_source_arena_cost
  · dsimp only
    exact Nat.le_refl _⟩

/-- Uniform core bound; one extra boundary retains the final sentinel. -/
def getBoolCoreBound (rowCount : Nat) : Nat := (getBoolCost (rowCount + 1)).val

/-- Only the copied boundary count contributes a nonconstant instruction charge. -/
theorem getBoolCoreBound_le (rowCount : Nat) :
    getBoolCoreBound rowCount ≤
      (14 + BufferRebase.copyIntoGuardCost.val + BufferRebase.copyIntoBodyCost.val + 10) *
        rowCount + getBoolCoreBound 0 := by
  simp only [getBoolCoreBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [Extract.extractBoolCoreBound_eq (rowCount + 1), Extract.extractBoolCoreBound_eq 1]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- The callable bound observes the original rows without inspecting a fallback's contents. -/
theorem getBool_arenaCostBound (rows : Array (Array (Array Bool))) (w heapLimit : Nat) :
    FunctionArenaCostBound program (program.body getBoolId)
      (fun args : (Buffer .nat × (Buffer .nat × Buffer .bool)) × Nat ×
          (Buffer .nat × Buffer .bool) => getBool_args args.1 args.2.1 args.2.2)
      (fun args heap =>
        (Representation.raggedArrayOf (Representation.raggedArray .bool)).Rel
          rows args.1 heap)
      w heapLimit 3 (fun args => getBoolCoreBound (rows.getD args.2.1 #[]).size + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap observed
  exact (getBoolCost _).property w heapLimit rows args.1 args.2.1 args.2.2 heap rfl observed

end Ram.LanguageCompiler.Buffer.Ragged.Nested
