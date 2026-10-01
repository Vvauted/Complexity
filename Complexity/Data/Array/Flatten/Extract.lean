/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Array.Flatten

/-!
# Extracting rows from flattened arrays

A row interval selects a contiguous payload interval. Its boundary slice must
be rebased by the first selected offset; merely borrowing that slice would
retain the original absolute offsets. These are mathematical identities, not
free runtime operations or changes to the canonical storage representation.
-/

namespace Array

variable {α : Type*}

/-- A prefix splits at any earlier row boundary. -/
theorem flattenOffsets_add_extract_size (rows : Array (Array α))
    {start stop : Nat} (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    rows.flattenOffsets[stop]'(by simp; omega) =
      rows.flattenOffsets[start]'(by simp; omega) + (rows.extract start stop).flatten.size := by
  simp only [getElem_flattenOffsets]
  have split : rows.extract 0 start ++ rows.extract start stop = rows.extract 0 stop := by
    rw [extract_append_extract]
    simp only [Nat.zero_min, Nat.max_eq_right ordered]
  rw [← split, flatten_append, size_append]

/-- Extracting consecutive rows selects exactly the corresponding payload interval. -/
theorem extract_flatten_rows (rows : Array (Array α))
    {start stop : Nat} (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    rows.flatten.extract
      (rows.flattenOffsets[start]'(by simp; omega))
      (rows.flattenOffsets[stop]'(by simp; omega)) = (rows.extract start stop).flatten := by
  have initial := extract_flatten_prefix rows bound
  have sliced := congrArg
    (fun xs => xs.extract (rows.extract 0 start).flatten.size
      (rows.extract 0 stop).flatten.size) initial
  simp only [extract_extract, Nat.zero_add, Nat.min_self] at sliced
  simp only [getElem_flattenOffsets]
  rw [sliced]
  have split : rows.extract 0 start ++ rows.extract start stop = rows.extract 0 stop := by
    rw [extract_append_extract]
    simp only [Nat.zero_min, Nat.max_eq_right ordered]
  rw [← split, flatten_append, size_append, extract_append_right, extract_size]

/-- The canonical offsets of a row interval are its real offset slice minus
the first selected offset. Empty rows and an empty interval retain the sentinel. -/
theorem flattenOffsets_extract (rows : Array (Array α))
    {start stop : Nat} (ordered : start ≤ stop) (bound : stop ≤ rows.size) :
    (rows.extract start stop).flattenOffsets =
      (rows.flattenOffsets.extract start (stop + 1)).map
        (fun offset => offset - rows.flattenOffsets[start]'(by simp; omega)) := by
  apply Array.ext
  · simp only [size_flattenOffsets, size_extract, size_map,
      Nat.min_eq_left bound, Nat.min_eq_left (by omega : stop + 1 ≤ rows.size + 1)]
    omega
  intro index leftBound rightBound
  have active : start + index ≤ stop := by
    simp only [size_flattenOffsets, size_extract, Nat.min_eq_left bound] at leftBound
    omega
  rw [getElem_map, getElem_extract, getElem_flattenOffsets]
  rw [extract_extract, Nat.add_zero, Nat.min_eq_left active]
  have step := flattenOffsets_add_extract_size rows (start := start)
    (stop := start + index) (by omega) (by omega)
  rw [step, Nat.add_sub_cancel_left]

end Array
