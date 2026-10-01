/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.Nested
import Complexity.Computability.Ram.Compiler.Language.Buffer.Ragged.Extract.Ready

/-!
# Readiness of defaulted nested ragged-array reads

The real bounds check selects either allocating extraction or the unchanged
fallback. In bounds, only the selected row's boundaries and final sentinel are
allocated; out of bounds, neither the fallback nor its cells are copied.
The mathematical result and old aliases refer to the actual final heap.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.Nested

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.Ragged.Nested

/-- Retained boundary cells of a defaulted nested-row read. Even an empty valid
row reserves its sentinel; an invalid index reserves nothing. -/
def getReserve {α : Type*} (rows : Array (Array α)) (index : Nat) : Nat :=
  if index < rows.size then (rows.getD index #[]).size + 1 else 0

/-- Measure the actual natural-row read. All array sizes and the selected index
fit the word width; no bound on unread natural payload values is assumed. -/
theorem getNat_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (rows : Array (Array (Array Nat))) (index : Nat) (fallback : Array (Array Nat))
    (storage : Buffer .nat × (Buffer .nat × Buffer .nat))
    (defaultView : Buffer .nat × Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArrayOf (Representation.raggedArray .nat)).Rel
      rows storage heap)
    (defaultObserved : (Representation.raggedArray .nat).Rel fallback defaultView heap)
    (rowsFit : rows.size + 1 < 2 ^ w) (innerFit : rows.flatten.size + 1 < 2 ^ w)
    (payloadFit : rows.flatten.flatten.size < 2 ^ w) (indexFits : index < 2 ^ w)
    (defaultFits : ValueFits w (τ := .prod (.buffer .nat) (.buffer .nat)) defaultView)
    (capacity : cursor + getReserve rows index ≤ heapLimit) :
    ArenaMeasured program w heapLimit 3 (program.body getNatId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        finalCursor = cursor + getReserve rows index ∧
        (Representation.raggedArray .nat).Rel (rows.getD index fallback) returned finish.heap ∧
        PreservesContents heap finish.heap)
      ⟨getNat_args storage index defaultView, heap⟩ cursor := by
  have outerSize := Representation.raggedArrayOf_size observed
  have offsetsFits : storage.1.length < 2 ^ w := by omega
  have lengthFits : storage.1.length - 1 < 2 ^ w := by omega
  have innerSize : storage.2.1.length = rows.flatten.size + 1 :=
    Representation.raggedArray_length observed.2
  have innerFits : storage.2.1.length < 2 ^ w := by omega
  have payloadSize : rows.flatten.flatten.size = storage.2.2.length := observed.2.2.size_eq
  have cellsFits : storage.2.2.length < 2 ^ w := by omega
  by_cases inside : index < rows.size
  · have selected : decide (index < storage.1.length - 1) = true := by
      apply decide_eq_true
      omega
    have firstBound : index < rows.flattenOffsets.size := by simp; omega
    have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
    let first := rows.flattenOffsets[index]
    let last := rows.flattenOffsets[index + 1]
    have firstRead : heap.read storage.1 index = .ok first := observed.1.read firstBound
    have lastRead : heap.read storage.1 (index + 1) = .ok last := observed.1.read lastBound
    have firstBounded : first ≤ rows.flatten.size := Array.flattenOffsets_le rows index firstBound
    have lastBounded : last ≤ rows.flatten.size :=
      Array.flattenOffsets_le rows (index + 1) lastBound
    have firstFits : first < 2 ^ w := by omega
    have lastFits : last < 2 ^ w := by omega
    have nextFits : index + 1 < 2 ^ w := by omega
    have rowSize := Array.flattenOffsets_succ rows inside
    have ordered : first ≤ last := by dsimp only [first, last]; omega
    have selectedCount : last + 1 - first = getReserve rows index := by
      dsimp only [first, last]
      rw [rowSize]
      simp only [getReserve, if_pos inside, Array.getD, dif_pos inside,
        Nat.add_assoc, Nat.add_sub_cancel_left]
      rfl
    have worker := Extract.extractNat_arenaMeasured (heapLimit := heapLimit) (cursor := cursor)
      positive rows.flatten storage.2 first last heap observed.2 ordered lastBounded
      innerFit payloadFit (by simpa only [selectedCount] using capacity)
    change ArenaMeasured program w heapLimit 3 getNatBody _ _ _
    ram_source_arena_step
    apply ArenaMeasured.read (value := first)
    · exact firstRead
    · exact offsetsFits
    · exact indexFits
    · exact firstFits
    ram_source_arena_step
    apply ArenaMeasured.read (value := last)
    · exact lastRead
    · exact offsetsFits
    · exact nextFits
    · exact lastFits
    ram_source_arena_step
    ram_source_arena_call measured using worker
      as workerFinish returned workerCursor workerSteps workerObserved workerFits
      via imports.Extract.embedding
    have cursorEq : workerCursor = cursor + getReserve rows index := by
      simpa only [selectedCount] using workerObserved.1
    have result : (Representation.raggedArray .nat).Rel
        (rows.getD index fallback) returned workerFinish.heap := by
      simpa only [first, last, Array.extract_flatten_row rows inside, Array.getD,
        dif_pos inside] using workerObserved.2.1
    have preserved : PreservesContents heap workerFinish.heap := workerObserved.2.2
    ram_source_arena_step
    exact ⟨cursorEq, result, preserved⟩
  · have selected : decide (index < storage.1.length - 1) = false := by
      apply decide_eq_false
      omega
    have noReserve : getReserve rows index = 0 := by simp only [getReserve, if_neg inside]
    have result : (Representation.raggedArray .nat).Rel
        (rows.getD index fallback) defaultView heap := by
      simpa only [Array.getD, dif_neg inside] using defaultObserved
    have preserved : PreservesContents heap heap := fun {_} _ _ contents => contents
    change ArenaMeasured program w heapLimit 3 getNatBody _ _ _
    ram_source_arena_step
    exact ⟨by simp only [noReserve, Nat.add_zero], result, preserved⟩

/-- Measure the actual Boolean-row read. All array sizes and the selected index
fit the word width; no bound on unread Boolean payload values is assumed. -/
theorem getBool_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (rows : Array (Array (Array Bool))) (index : Nat) (fallback : Array (Array Bool))
    (storage : Buffer .nat × (Buffer .nat × Buffer .bool))
    (defaultView : Buffer .nat × Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArrayOf (Representation.raggedArray .bool)).Rel
      rows storage heap)
    (defaultObserved : (Representation.raggedArray .bool).Rel fallback defaultView heap)
    (rowsFit : rows.size + 1 < 2 ^ w) (innerFit : rows.flatten.size + 1 < 2 ^ w)
    (payloadFit : rows.flatten.flatten.size < 2 ^ w) (indexFits : index < 2 ^ w)
    (defaultFits : ValueFits w (τ := .prod (.buffer .nat) (.buffer .bool)) defaultView)
    (capacity : cursor + getReserve rows index ≤ heapLimit) :
    ArenaMeasured program w heapLimit 3 (program.body getBoolId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        finalCursor = cursor + getReserve rows index ∧
        (Representation.raggedArray .bool).Rel (rows.getD index fallback) returned finish.heap ∧
        PreservesContents heap finish.heap)
      ⟨getBool_args storage index defaultView, heap⟩ cursor := by
  have outerSize := Representation.raggedArrayOf_size observed
  have offsetsFits : storage.1.length < 2 ^ w := by omega
  have lengthFits : storage.1.length - 1 < 2 ^ w := by omega
  have innerSize : storage.2.1.length = rows.flatten.size + 1 :=
    Representation.raggedArray_length observed.2
  have innerFits : storage.2.1.length < 2 ^ w := by omega
  have payloadSize : rows.flatten.flatten.size = storage.2.2.length := observed.2.2.size_eq
  have cellsFits : storage.2.2.length < 2 ^ w := by omega
  by_cases inside : index < rows.size
  · have selected : decide (index < storage.1.length - 1) = true := by
      apply decide_eq_true
      omega
    have firstBound : index < rows.flattenOffsets.size := by simp; omega
    have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
    let first := rows.flattenOffsets[index]
    let last := rows.flattenOffsets[index + 1]
    have firstRead : heap.read storage.1 index = .ok first := observed.1.read firstBound
    have lastRead : heap.read storage.1 (index + 1) = .ok last := observed.1.read lastBound
    have firstBounded : first ≤ rows.flatten.size := Array.flattenOffsets_le rows index firstBound
    have lastBounded : last ≤ rows.flatten.size :=
      Array.flattenOffsets_le rows (index + 1) lastBound
    have firstFits : first < 2 ^ w := by omega
    have lastFits : last < 2 ^ w := by omega
    have nextFits : index + 1 < 2 ^ w := by omega
    have rowSize := Array.flattenOffsets_succ rows inside
    have ordered : first ≤ last := by dsimp only [first, last]; omega
    have selectedCount : last + 1 - first = getReserve rows index := by
      dsimp only [first, last]
      rw [rowSize]
      simp only [getReserve, if_pos inside, Array.getD, dif_pos inside,
        Nat.add_assoc, Nat.add_sub_cancel_left]
      rfl
    have worker := Extract.extractBool_arenaMeasured (heapLimit := heapLimit) (cursor := cursor)
      positive rows.flatten storage.2 first last heap observed.2 ordered lastBounded
      innerFit payloadFit (by simpa only [selectedCount] using capacity)
    change ArenaMeasured program w heapLimit 3 getBoolBody _ _ _
    ram_source_arena_step
    apply ArenaMeasured.read (value := first)
    · exact firstRead
    · exact offsetsFits
    · exact indexFits
    · exact firstFits
    ram_source_arena_step
    apply ArenaMeasured.read (value := last)
    · exact lastRead
    · exact offsetsFits
    · exact nextFits
    · exact lastFits
    ram_source_arena_step
    ram_source_arena_call measured using worker
      as workerFinish returned workerCursor workerSteps workerObserved workerFits
      via imports.Extract.embedding
    have cursorEq : workerCursor = cursor + getReserve rows index := by
      simpa only [selectedCount] using workerObserved.1
    have result : (Representation.raggedArray .bool).Rel
        (rows.getD index fallback) returned workerFinish.heap := by
      simpa only [first, last, Array.extract_flatten_row rows inside, Array.getD,
        dif_pos inside] using workerObserved.2.1
    have preserved : PreservesContents heap workerFinish.heap := workerObserved.2.2
    ram_source_arena_step
    exact ⟨cursorEq, result, preserved⟩
  · have selected : decide (index < storage.1.length - 1) = false := by
      apply decide_eq_false
      omega
    have noReserve : getReserve rows index = 0 := by simp only [getReserve, if_neg inside]
    have result : (Representation.raggedArray .bool).Rel
        (rows.getD index fallback) defaultView heap := by
      simpa only [Array.getD, dif_neg inside] using defaultObserved
    have preserved : PreservesContents heap heap := fun {_} _ _ contents => contents
    change ArenaMeasured program w heapLimit 3 getBoolBody _ _ _
    ram_source_arena_step
    exact ⟨by simp only [noReserve, Nat.add_zero], result, preserved⟩

/-- Reuse the measured natural-row read as an indexed resource contract.
Argument ranges come from the caller; the reserve depends on the selected row,
never on the fallback's contents or length. -/
theorem getNat_arenaResources {w : Nat} (positive : 0 < w)
    (rows : Array (Array (Array Nat))) (fallback : Array (Array Nat)) (heapLimit : Nat) :
    FunctionArenaResources program (program.body getNatId)
      (fun args : (Buffer .nat × (Buffer .nat × Buffer .nat)) × Nat ×
          (Buffer .nat × Buffer .nat) => getNat_args args.1 args.2.1 args.2.2)
      (fun args heap =>
        (Representation.raggedArrayOf (Representation.raggedArray .nat)).Rel
          rows args.1 heap ∧
        (Representation.raggedArray .nat).Rel fallback args.2.2 heap)
      w heapLimit 3 (fun args => getReserve rows args.2.1) := by
  intro args heap cursor observed fits capacity finish value execution
  have ranges : args.1.1.length < 2 ^ w ∧ args.1.2.1.length < 2 ^ w ∧
      args.1.2.2.length < 2 ^ w := fits .here
  have outerSize : args.1.1.length = rows.size + 1 := by
    simpa only [Array.size_flattenOffsets] using
      (show args.1.1.length = rows.flattenOffsets.size from observed.1.1.size_eq.symm)
  have innerSize : args.1.2.1.length = rows.flatten.size + 1 :=
    Representation.raggedArray_length observed.1.2
  have payloadSize : rows.flatten.flatten.size = args.1.2.2.length := observed.1.2.2.size_eq
  obtain ⟨finalCursor, steps, ready, _, returned, _, cursorEq, _⟩ :=
    (getNat_arenaMeasured positive rows args.2.1 fallback args.1 args.2.2 heap
      observed.1 observed.2 (by simpa only [outerSize] using ranges.1)
      (by simpa only [innerSize] using ranges.2.1)
      (by simpa only [payloadSize] using ranges.2.2)
      (fits (.there .here)) (fits (.there (.there .here))) capacity).at_exec execution
  exact ⟨finalCursor, ready, cursorEq.le⟩

/-- Reuse the measured Boolean-row read as an indexed resource contract.
Argument ranges come from the caller; the reserve depends on the selected row,
never on the fallback's contents or length. -/
theorem getBool_arenaResources {w : Nat} (positive : 0 < w)
    (rows : Array (Array (Array Bool))) (fallback : Array (Array Bool)) (heapLimit : Nat) :
    FunctionArenaResources program (program.body getBoolId)
      (fun args : (Buffer .nat × (Buffer .nat × Buffer .bool)) × Nat ×
          (Buffer .nat × Buffer .bool) => getBool_args args.1 args.2.1 args.2.2)
      (fun args heap =>
        (Representation.raggedArrayOf (Representation.raggedArray .bool)).Rel
          rows args.1 heap ∧
        (Representation.raggedArray .bool).Rel fallback args.2.2 heap)
      w heapLimit 3 (fun args => getReserve rows args.2.1) := by
  intro args heap cursor observed fits capacity finish value execution
  have ranges : args.1.1.length < 2 ^ w ∧ args.1.2.1.length < 2 ^ w ∧
      args.1.2.2.length < 2 ^ w := fits .here
  have outerSize : args.1.1.length = rows.size + 1 := by
    simpa only [Array.size_flattenOffsets] using
      (show args.1.1.length = rows.flattenOffsets.size from observed.1.1.size_eq.symm)
  have innerSize : args.1.2.1.length = rows.flatten.size + 1 :=
    Representation.raggedArray_length observed.1.2
  have payloadSize : rows.flatten.flatten.size = args.1.2.2.length := observed.1.2.2.size_eq
  obtain ⟨finalCursor, steps, ready, _, returned, _, cursorEq, _⟩ :=
    (getBool_arenaMeasured positive rows args.2.1 fallback args.1 args.2.2 heap
      observed.1 observed.2 (by simpa only [outerSize] using ranges.1)
      (by simpa only [innerSize] using ranges.2.1)
      (by simpa only [payloadSize] using ranges.2.2)
      (fits (.there .here)) (fits (.there (.there .here))) capacity).at_exec execution
  exact ⟨finalCursor, ready, cursorEq.le⟩

end Ram.LanguageCompiler.Buffer.Ragged.Nested
