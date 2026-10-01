/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Array.Flatten.Extract
import Complexity.Language.Buffer.Rebase
import Complexity.Language.Representation.RaggedArray
import Complexity.Language.Eval.Simp

/-!
# Extracting canonical ragged-array intervals

The actual program copies and rebases the selected boundary interval, including
its final sentinel, and borrows the corresponding payload slice. Every old
contents observation survives. Unlike a scalar row lookup, this operation
allocates and performs work proportional to the number of selected boundaries.
The contracts describe ordered, in-bounds intervals; they do not silently clamp
invalid bounds or change the canonical input representation.
-/

namespace Complexity.Language.Buffer.Ragged

source_program% Extract importing Rebase where
  def extractNat (storage : Buffer Nat × Buffer Nat) (start : Nat) (stop : Nat) :
      Buffer Nat × Buffer Nat := do
    let offsets := storage.1
    let payload := storage.2
    let first ← offsets.get start
    let last ← offsets.get stop
    let selected ← offsets.slice start (stop + 1 - start)
    let boundaries ← Rebase.copy selected first
    let cells ← payload.slice first (last - first)
    return (boundaries, cells)

  def extractBool (storage : Buffer Nat × Buffer Bool) (start : Nat) (stop : Nat) :
      Buffer Nat × Buffer Bool := do
    let offsets := storage.1
    let payload := storage.2
    let first ← offsets.get start
    let last ← offsets.get stop
    let selected ← offsets.slice start (stop + 1 - start)
    let boundaries ← Rebase.copy selected first
    let cells ← payload.slice first (last - first)
    return (boundaries, cells)

namespace Extract

private theorem extract_eval {kind : CellTy} (rows : Array (Array (CellValue kind)))
    (storage : Buffer .nat × Buffer kind) (start stop : Nat) (heap : Heap)
    (observed : (Representation.raggedArray kind).Rel rows storage heap)
    (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    ∃ returned finish,
      (do
        let first ← storage.1.readM start
        let last ← storage.1.readM stop
        let selected ← storage.1.sliceM start (stop + 1 - start)
        let boundaries ← Rebase.copy selected first
        let cells ← storage.2.sliceM first (last - first)
        pure (boundaries, cells)) heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray kind).Rel (rows.extract start stop) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  change storage.1.Contents heap rows.flattenOffsets ∧
    storage.2.Contents heap rows.flatten at observed
  have firstBound : start < rows.flattenOffsets.size := by simp; omega
  have lastBound : stop < rows.flattenOffsets.size := by simp; omega
  have firstRead := observed.1.read firstBound
  have lastRead := observed.1.read lastBound
  change heap.read storage.1 start = .ok rows.flattenOffsets[start] at firstRead
  change heap.read storage.1 stop = .ok rows.flattenOffsets[stop] at lastRead
  have boundaryStop : start + (stop + 1 - start) = stop + 1 := by omega
  have boundaryFits : start + (stop + 1 - start) ≤ storage.1.length := by
    have size := Representation.raggedArray_length observed
    omega
  let selected : Buffer .nat :=
    ⟨storage.1.object, storage.1.offset + start, stop + 1 - start⟩
  have selectedContents : selected.Contents heap
      (rows.flattenOffsets.extract start (stop + 1)) := by
    simpa only [boundaryStop] using observed.1.slice boundaryFits
  have offsetStep := Array.flattenOffsets_add_extract_size rows ordered bound
  have offsetOrdered : rows.flattenOffsets[start] ≤ rows.flattenOffsets[stop] := by omega
  have payloadStop : rows.flattenOffsets[start] +
      (rows.flattenOffsets[stop] - rows.flattenOffsets[start]) =
        rows.flattenOffsets[stop] := by omega
  have payloadFits : rows.flattenOffsets[start] +
      (rows.flattenOffsets[stop] - rows.flattenOffsets[start]) ≤ storage.2.length := by
    rw [payloadStop, ← observed.2.size_eq]
    exact Array.flattenOffsets_le rows stop lastBound
  let cells : Buffer kind := ⟨storage.2.object,
    storage.2.offset + rows.flattenOffsets[start],
    rows.flattenOffsets[stop] - rows.flattenOffsets[start]⟩
  have cellContents : cells.Contents heap (rows.extract start stop).flatten := by
    have sliced := observed.2.slice payloadFits
    rw [payloadStop, Array.extract_flatten_rows rows ordered bound] at sliced
    exact sliced
  obtain ⟨boundaries, finish, execution, result, shape, preserved⟩ :=
    Rebase.copy_eval_exists_preserving _ selected rows.flattenOffsets[start]
      heap selectedContents
  refine ⟨(boundaries, cells), finish, ?_, ?_, shape, preserved⟩
  · simp only [source_eval, firstRead, lastRead, storage.1.slice_eq boundaryFits]
    change (do
      let boundaries ← Rebase.copy selected rows.flattenOffsets[start]
      let result ← storage.2.sliceM rows.flattenOffsets[start]
        (rows.flattenOffsets[stop] - rows.flattenOffsets[start])
      pure (boundaries, result)) heap = _
    simp only [source_eval, execution, storage.2.slice_eq payloadFits]
    rfl
  · change boundaries.Contents finish (rows.extract start stop).flattenOffsets ∧
      cells.Contents finish (rows.extract start stop).flatten
    exact ⟨by simpa only [Array.flattenOffsets_extract rows ordered bound] using result,
      preserved cells _ cellContents⟩

/-- Natural payload extraction returns the canonical mathematical row interval
at the actual changed heap, while preserving every old view. -/
theorem extractNat_eval_exists_preserving (rows : Array (Array Nat))
    (storage : Buffer .nat × Buffer .nat) (start stop : Nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    ∃ returned finish,
      extractNat storage start stop heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray .nat).Rel (rows.extract start stop) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  simpa only [extractNat_eq] using
    extract_eval (kind := .nat) rows storage start stop heap observed ordered bound

/-- Boolean payload extraction uses the same rebasing operation and retains
empty rows, the final sentinel, and all pre-existing aliases. -/
theorem extractBool_eval_exists_preserving (rows : Array (Array Bool))
    (storage : Buffer .nat × Buffer .bool) (start stop : Nat) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    ∃ returned finish,
      extractBool storage start stop heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray .bool).Rel (rows.extract start stop) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  simpa only [extractBool_eq] using
    extract_eval (kind := .bool) rows storage start stop heap observed ordered bound

end Extract
end Complexity.Language.Buffer.Ragged
