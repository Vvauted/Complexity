/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.Array.Extract
import Init.Data.Array.OfFn
import Mathlib.Logic.Embedding.Basic
import Lean.Elab.Tactic.Omega

/-!
# Row boundaries in flattened arrays

The boundary array has one more entry than the number of rows. Repeated
boundaries retain empty rows, including trailing empty rows. Together with
`Array.flatten` it determines the original nested array exactly.

These definitions describe a storage layout. They do not give a free executable
flattening operation or a cost bound for constructing that layout.
-/

namespace Array

universe u
variable {α : Type u}

/-- Cumulative row boundaries, including the start and the final end boundary. -/
def flattenOffsets (rows : Array (Array α)) : Array Nat :=
  ofFn fun i : Fin (rows.size + 1) => (rows.extract 0 i).flatten.size

@[simp] theorem size_flattenOffsets (rows : Array (Array α)) :
    rows.flattenOffsets.size = rows.size + 1 := by simp [flattenOffsets]

@[simp] theorem getElem_flattenOffsets (rows : Array (Array α)) (i : Nat)
    (h : i < rows.flattenOffsets.size) :
    rows.flattenOffsets[i] = (rows.extract 0 i).flatten.size := by
  simp [flattenOffsets]

/-- Pointwise element views preserve every row boundary, including empty rows. -/
@[simp] theorem flattenOffsets_map {β : Type*} (f : α → β) (rows : Array (Array α)) :
    (rows.map (Array.map f)).flattenOffsets = rows.flattenOffsets := by
  apply Array.ext (by simp)
  intro i hx hy
  simp only [getElem_flattenOffsets, ← map_extract, ← map_flatten, size_map]

/-- The flattened prefix ends at precisely its own length. -/
theorem extract_flatten_prefix (rows : Array (Array α)) {i : Nat} (h : i ≤ rows.size) :
    rows.flatten.extract 0 (rows.extract 0 i).flatten.size = (rows.extract 0 i).flatten := by
  have split : rows.extract 0 i ++ rows.extract i rows.size = rows := by
    simp [extract_append_extract, Nat.max_eq_right h]
  have flat := congrArg Array.flatten split
  rw [flatten_append] at flat
  conv_lhs => rw [← flat]
  simp

/-- Every boundary fits inside the flattened payload. -/
theorem flattenOffsets_le (rows : Array (Array α)) (i : Nat)
    (h : i < rows.flattenOffsets.size) : rows.flattenOffsets[i] ≤ rows.flatten.size := by
  have bound : i ≤ rows.size := by rw [size_flattenOffsets] at h; omega
  have split : rows.extract 0 i ++ rows.extract i rows.size = rows := by
    simp [extract_append_extract, Nat.max_eq_right bound]
  have sizes := congrArg (fun x => x.flatten.size) split
  simp only [flatten_append, size_append] at sizes
  rw [getElem_flattenOffsets]
  omega

/-- Adjacent boundaries differ by exactly that row's length. -/
theorem flattenOffsets_succ (rows : Array (Array α)) {i : Nat} (h : i < rows.size) :
    rows.flattenOffsets[i + 1]'(by simp; omega) =
      rows.flattenOffsets[i]'(by simp; omega) + rows[i].size := by
  simp only [getElem_flattenOffsets]
  rw [extract_succ_right (by omega) h, flatten_push, size_append]

/-- Reading between adjacent boundaries recovers the whole row, even if empty. -/
theorem extract_flatten_row (rows : Array (Array α)) {i : Nat} (h : i < rows.size) :
    rows.flatten.extract
      (rows.flattenOffsets[i]'(by simp; omega))
      (rows.flattenOffsets[i + 1]'(by simp; omega)) = rows[i] := by
  simp only [getElem_flattenOffsets]
  have initialRows := extract_flatten_prefix rows (i := i + 1) (by omega)
  have sliced := congrArg
    (fun xs => xs.extract (rows.extract 0 i).flatten.size
      (rows.extract 0 (i + 1)).flatten.size) initialRows
  simp only [extract_extract, Nat.zero_add, Nat.min_self] at sliced
  rw [sliced, extract_succ_right (by omega) h, flatten_push, size_append,
    extract_append_right, extract_size]

/-- Boundaries and payload form a lossless presentation of ordinary nested arrays. -/
def flattenEmbedding : Array (Array α) ↪ Array Nat × Array α where
  toFun rows := (rows.flattenOffsets, rows.flatten)
  inj' := by
    intro xs ys same
    have offsets : xs.flattenOffsets = ys.flattenOffsets := congrArg Prod.fst same
    have payload : xs.flatten = ys.flatten := congrArg Prod.snd same
    have sizes : xs.size = ys.size := by
      have := congrArg Array.size offsets
      simpa only [size_flattenOffsets, Nat.add_right_cancel_iff] using this
    apply Array.ext sizes
    intro i hx hy
    have start : xs.flattenOffsets[i]'(by simp; omega) =
        ys.flattenOffsets[i]'(by simp; omega) := by simp only [offsets]
    have stop : xs.flattenOffsets[i + 1]'(by simp; omega) =
        ys.flattenOffsets[i + 1]'(by simp; omega) := by simp only [offsets]
    rw [← extract_flatten_row xs hx, ← extract_flatten_row ys hy, payload, start, stop]

end Array
