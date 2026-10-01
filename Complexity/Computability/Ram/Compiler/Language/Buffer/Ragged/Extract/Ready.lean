/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.Extract
import Complexity.Computability.Ram.Compiler.Language.Buffer.Rebase.Ready
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Buffer

/-!
# Readiness of canonical ragged-array extraction

The actual endpoint reads and borrowed slices compose with the allocating
rebasing worker. The result keeps the ordinary array-extraction relation at the
actual final heap, preserves old contents, and reserves exactly one cell for each
selected boundary including the sentinel. Payload values are not read or copied,
so no payload-value range premise is required.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.Extract

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.Ragged.Extract

/-- Extract a natural-valued row interval with finite-word readiness and exact
retained allocation. Payload contents remain borrowed; their values need no bound. -/
theorem extractNat_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (rows : Array (Array Nat)) (storage : Buffer .nat × Buffer .nat)
    (start stop : Nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (ordered : start ≤ stop) (bound : stop ≤ rows.size)
    (rowsFit : rows.size + 1 < 2 ^ w) (payloadFits : rows.flatten.size < 2 ^ w)
    (capacity : cursor + (stop + 1 - start) ≤ heapLimit) :
    ArenaMeasured program w heapLimit 2 (program.body extractNatId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        finalCursor = cursor + (stop + 1 - start) ∧
        (Representation.raggedArray .nat).Rel (rows.extract start stop) returned finish.heap ∧
        PreservesContents heap finish.heap)
      ⟨extractNat_args storage start stop, heap⟩ cursor := by
  change storage.1.Contents heap rows.flattenOffsets ∧
    storage.2.Contents heap rows.flatten at observed
  have firstBound : start < rows.flattenOffsets.size := by simp; omega
  have lastBound : stop < rows.flattenOffsets.size := by simp; omega
  let first := rows.flattenOffsets[start]
  let last := rows.flattenOffsets[stop]
  have firstRead : heap.read storage.1 start = .ok first := observed.1.read firstBound
  have lastRead : heap.read storage.1 stop = .ok last := observed.1.read lastBound
  have firstFits : first < 2 ^ w := (Array.flattenOffsets_le rows start firstBound).trans_lt payloadFits
  have lastFits : last < 2 ^ w := (Array.flattenOffsets_le rows stop lastBound).trans_lt payloadFits
  have offsetSize : rows.size + 1 = storage.1.length := by
    simpa only [Array.size_flattenOffsets] using observed.1.size_eq
  have offsetsFit : storage.1.length < 2 ^ w := by omega
  have payloadFit : storage.2.length < 2 ^ w := by
    simpa only [observed.2.size_eq] using payloadFits
  have startFits : start < 2 ^ w := by omega
  have stopFits : stop < 2 ^ w := by omega
  have stopNextFits : stop + 1 < 2 ^ w := by omega
  have countFits : stop + 1 - start < 2 ^ w := by omega
  have boundaryStop : start + (stop + 1 - start) = stop + 1 := by omega
  have boundaryBound : start + (stop + 1 - start) ≤ storage.1.length := by omega
  let selected : Buffer .nat :=
    ⟨storage.1.object, storage.1.offset + start, stop + 1 - start⟩
  let selectedValues := rows.flattenOffsets.extract start (stop + 1)
  have selectedContents : selected.Contents heap selectedValues := by
    simpa only [boundaryStop] using observed.1.slice boundaryBound
  have selectedSize : selectedValues.size = stop + 1 - start := by
    simp only [selectedValues, Array.size_extract, Array.size_flattenOffsets,
      Nat.min_eq_left (by omega : stop + 1 ≤ rows.size + 1)]
  have selectedFits : ∀ i (hi : i < selectedValues.size), selectedValues[i] < 2 ^ w := by
    intro i hi
    dsimp only [selectedValues]
    rw [Array.getElem_extract]
    exact (Array.flattenOffsets_le rows _ _).trans_lt payloadFits
  have offsetStep := Array.flattenOffsets_add_extract_size rows ordered bound
  have offsetsOrdered : first ≤ last := by dsimp only [first, last]; omega
  have payloadStop : first + (last - first) = last := by omega
  have payloadBound : first + (last - first) ≤ storage.2.length := by
    rw [payloadStop, ← observed.2.size_eq]
    exact Array.flattenOffsets_le rows stop lastBound
  let cells : Buffer .nat := ⟨storage.2.object, storage.2.offset + first, last - first⟩
  have cellsContents : cells.Contents heap (rows.extract start stop).flatten := by
    have sliced := observed.2.slice payloadBound
    rw [payloadStop, Array.extract_flatten_rows rows ordered bound] at sliced
    exact sliced
  have payloadLengthFits : last - first < 2 ^ w := by omega
  have worker := BufferRebase.copy_arenaMeasured (heapLimit := heapLimit) (cursor := cursor)
    positive selected first selectedValues heap selectedContents selectedFits
    (by simpa only [selectedSize] using countFits) firstFits
    (by simpa only [selectedSize] using capacity)
  change ArenaMeasured program w heapLimit 2 extractNatBody _ _ _
  ram_source_arena_step
  apply ArenaMeasured.read (value := first)
  · exact firstRead
  · exact offsetsFit
  · exact startFits
  · exact firstFits
  ram_source_arena_step
  apply ArenaMeasured.read (value := last)
  · exact lastRead
  · exact offsetsFit
  · exact stopFits
  · exact lastFits
  ram_source_arena_step
  apply ArenaMeasured.slice (view := selected)
  · exact storage.1.slice_eq boundaryBound
  · exact offsetsFit
  · exact startFits
  · exact countFits
  · exact countFits
  ram_source_arena_step
  ram_source_arena_call measured using worker
    as workerFinish boundaries workerCursor workerSteps workerObserved workerFits
    via imports.Rebase.embedding
  have cursorEq := workerObserved.1
  have preserved : PreservesContents heap workerFinish.heap := workerObserved.2.2.2
  have boundariesContents : boundaries.Contents workerFinish.heap
      (rows.extract start stop).flattenOffsets := by
    simpa only [selectedValues, first, Array.flattenOffsets_extract rows ordered bound] using
      workerObserved.2.1
  have cellsNow := preserved cells _ cellsContents
  ram_source_arena_step
  apply ArenaMeasured.slice (view := cells)
  · exact storage.2.slice_eq payloadBound
  · exact payloadFit
  · exact firstFits
  · exact payloadLengthFits
  · exact payloadLengthFits
  ram_source_arena_step
  exact ⟨by simpa only [selectedSize] using cursorEq,
    ⟨boundariesContents, cellsNow⟩, preserved⟩

/-- Extract a Boolean-valued row interval with finite-word readiness and exact
retained allocation. Payload contents remain borrowed; their values need no bound. -/
theorem extractBool_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (rows : Array (Array Bool)) (storage : Buffer .nat × Buffer .bool)
    (start stop : Nat) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (ordered : start ≤ stop) (bound : stop ≤ rows.size)
    (rowsFit : rows.size + 1 < 2 ^ w) (payloadFits : rows.flatten.size < 2 ^ w)
    (capacity : cursor + (stop + 1 - start) ≤ heapLimit) :
    ArenaMeasured program w heapLimit 2 (program.body extractBoolId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        finalCursor = cursor + (stop + 1 - start) ∧
        (Representation.raggedArray .bool).Rel (rows.extract start stop) returned finish.heap ∧
        PreservesContents heap finish.heap)
      ⟨extractBool_args storage start stop, heap⟩ cursor := by
  change storage.1.Contents heap rows.flattenOffsets ∧
    storage.2.Contents heap rows.flatten at observed
  have firstBound : start < rows.flattenOffsets.size := by simp; omega
  have lastBound : stop < rows.flattenOffsets.size := by simp; omega
  let first := rows.flattenOffsets[start]
  let last := rows.flattenOffsets[stop]
  have firstRead : heap.read storage.1 start = .ok first := observed.1.read firstBound
  have lastRead : heap.read storage.1 stop = .ok last := observed.1.read lastBound
  have firstFits : first < 2 ^ w := (Array.flattenOffsets_le rows start firstBound).trans_lt payloadFits
  have lastFits : last < 2 ^ w := (Array.flattenOffsets_le rows stop lastBound).trans_lt payloadFits
  have offsetSize : rows.size + 1 = storage.1.length := by
    simpa only [Array.size_flattenOffsets] using observed.1.size_eq
  have offsetsFit : storage.1.length < 2 ^ w := by omega
  have payloadFit : storage.2.length < 2 ^ w := by
    simpa only [observed.2.size_eq] using payloadFits
  have startFits : start < 2 ^ w := by omega
  have stopFits : stop < 2 ^ w := by omega
  have stopNextFits : stop + 1 < 2 ^ w := by omega
  have countFits : stop + 1 - start < 2 ^ w := by omega
  have boundaryStop : start + (stop + 1 - start) = stop + 1 := by omega
  have boundaryBound : start + (stop + 1 - start) ≤ storage.1.length := by omega
  let selected : Buffer .nat :=
    ⟨storage.1.object, storage.1.offset + start, stop + 1 - start⟩
  let selectedValues := rows.flattenOffsets.extract start (stop + 1)
  have selectedContents : selected.Contents heap selectedValues := by
    simpa only [boundaryStop] using observed.1.slice boundaryBound
  have selectedSize : selectedValues.size = stop + 1 - start := by
    simp only [selectedValues, Array.size_extract, Array.size_flattenOffsets,
      Nat.min_eq_left (by omega : stop + 1 ≤ rows.size + 1)]
  have selectedFits : ∀ i (hi : i < selectedValues.size), selectedValues[i] < 2 ^ w := by
    intro i hi
    dsimp only [selectedValues]
    rw [Array.getElem_extract]
    exact (Array.flattenOffsets_le rows _ _).trans_lt payloadFits
  have offsetStep := Array.flattenOffsets_add_extract_size rows ordered bound
  have offsetsOrdered : first ≤ last := by dsimp only [first, last]; omega
  have payloadStop : first + (last - first) = last := by omega
  have payloadBound : first + (last - first) ≤ storage.2.length := by
    rw [payloadStop, ← observed.2.size_eq]
    exact Array.flattenOffsets_le rows stop lastBound
  let cells : Buffer .bool := ⟨storage.2.object, storage.2.offset + first, last - first⟩
  have cellsContents : cells.Contents heap (rows.extract start stop).flatten := by
    have sliced := observed.2.slice payloadBound
    rw [payloadStop, Array.extract_flatten_rows rows ordered bound] at sliced
    exact sliced
  have payloadLengthFits : last - first < 2 ^ w := by omega
  have worker := BufferRebase.copy_arenaMeasured (heapLimit := heapLimit) (cursor := cursor)
    positive selected first selectedValues heap selectedContents selectedFits
    (by simpa only [selectedSize] using countFits) firstFits
    (by simpa only [selectedSize] using capacity)
  change ArenaMeasured program w heapLimit 2 extractBoolBody _ _ _
  ram_source_arena_step
  apply ArenaMeasured.read (value := first)
  · exact firstRead
  · exact offsetsFit
  · exact startFits
  · exact firstFits
  ram_source_arena_step
  apply ArenaMeasured.read (value := last)
  · exact lastRead
  · exact offsetsFit
  · exact stopFits
  · exact lastFits
  ram_source_arena_step
  apply ArenaMeasured.slice (view := selected)
  · exact storage.1.slice_eq boundaryBound
  · exact offsetsFit
  · exact startFits
  · exact countFits
  · exact countFits
  ram_source_arena_step
  ram_source_arena_call measured using worker
    as workerFinish boundaries workerCursor workerSteps workerObserved workerFits
    via imports.Rebase.embedding
  have cursorEq := workerObserved.1
  have preserved : PreservesContents heap workerFinish.heap := workerObserved.2.2.2
  have boundariesContents : boundaries.Contents workerFinish.heap
      (rows.extract start stop).flattenOffsets := by
    simpa only [selectedValues, first, Array.flattenOffsets_extract rows ordered bound] using
      workerObserved.2.1
  have cellsNow := preserved cells _ cellsContents
  ram_source_arena_step
  apply ArenaMeasured.slice (view := cells)
  · exact storage.2.slice_eq payloadBound
  · exact payloadFit
  · exact firstFits
  · exact payloadLengthFits
  · exact payloadLengthFits
  ram_source_arena_step
  exact ⟨by simpa only [selectedSize] using cursorEq,
    ⟨boundariesContents, cellsNow⟩, preserved⟩


end Ram.LanguageCompiler.Buffer.Ragged.Extract
