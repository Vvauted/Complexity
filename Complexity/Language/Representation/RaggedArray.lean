/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Array.Flatten
import Complexity.Language.Representation.Preservation
import Complexity.Language.Buffer.Resize

/-!
# Nested arrays with row boundaries

Two actual buffers store cumulative row boundaries and the flattened payload.
The observation retains all rows and their order, including empty rows. A row
is a borrowed slice of the payload; this gives neither ownership nor persistence
across arbitrary writes. No new heap cell kind or host-side decoder is used.
-/

namespace Complexity.Language.Representation

/-- A canonical ragged array backed by a boundary buffer and a payload buffer. -/
def raggedArray (kind : CellTy) :
    Representation (Array (Array (CellValue kind))) (.prod (.buffer .nat) (.buffer kind)) :=
  ((array .nat).prod (array kind)).comap Array.flattenEmbedding

@[simp] theorem raggedArray_rel (kind : CellTy) (rows : Array (Array (CellValue kind)))
    (value : Buffer .nat × Buffer kind) (heap : Heap) :
    (raggedArray kind).Rel rows value heap ↔
      value.1.Contents heap rows.flattenOffsets ∧ value.2.Contents heap rows.flatten := Iff.rfl

/-- The final boundary is retained even for zero rows. -/
theorem raggedArray_length {kind : CellTy} {rows : Array (Array (CellValue kind))}
    {value : Buffer .nat × Buffer kind} {heap : Heap}
    (observed : (raggedArray kind).Rel rows value heap) :
    value.1.length = rows.size + 1 := by
  rw [raggedArray_rel] at observed
  simpa only [Array.size_flattenOffsets] using observed.1.size_eq.symm

/-- The ordinary row count is the actual boundary count minus its final sentinel. -/
theorem raggedArray_size {kind : CellTy} {rows : Array (Array (CellValue kind))}
    {value : Buffer .nat × Buffer kind} {heap : Heap}
    (observed : (raggedArray kind).Rel rows value heap) :
    rows.size = value.1.length - 1 := by rw [raggedArray_length observed]; omega

/-- Every row denotes an actual fitting slice of the payload in the same heap. -/
theorem raggedArray_row {kind : CellTy} {rows : Array (Array (CellValue kind))}
    {value : Buffer .nat × Buffer kind} {heap : Heap}
    (observed : (raggedArray kind).Rel rows value heap) {i : Nat} (bound : i < rows.size) :
    (⟨value.2.object, value.2.offset + rows.flattenOffsets[i]'(by simp; omega),
      rows[i].size⟩ : Buffer kind).Contents heap rows[i] := by
  rw [raggedArray_rel] at observed
  have stop := Array.flattenOffsets_le rows (i + 1) (by simp; omega)
  rw [Array.flattenOffsets_succ rows bound, observed.2.size_eq] at stop
  have sliced := observed.2.slice stop
  rw [← Array.flattenOffsets_succ rows bound, Array.extract_flatten_row rows bound] at sliced
  exact sliced

/-- Preserve both real observations; heap shape alone does not preserve arrays. -/
theorem Preserves.raggedArray {kind : CellTy} {initial finish : Heap}
    (boundaries : (array .nat).Preserves initial finish)
    (payload : (array kind).Preserves initial finish) :
    (raggedArray kind).Preserves initial finish :=
  Preserves.comap Array.flattenEmbedding (Preserves.prod boundaries payload)

end Complexity.Language.Representation
