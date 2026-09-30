/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Array.Flatten
import Complexity.Language.Representation.Preservation
import Complexity.Language.Representation.Array
import Complexity.Language.Buffer.Resize

/-!
# Nested arrays with row boundaries

One actual buffer stores cumulative row boundaries alongside the existing
flattened-payload representation. Scalar payloads use a second buffer; product
columns share the same boundaries. The observation retains all rows and their
order, including empty rows. Row views give neither ownership nor persistence
across arbitrary writes. No new heap cell kind or host-side decoder is used.
-/

namespace Complexity.Language.Representation

universe u v

/-- One shared boundary buffer and an existing representation of the flattened
payload. Product columns share these boundaries, without duplicating objects. -/
def raggedArrayOf {α : Type u} {τ : Ty} (payload : Representation (Array α) τ) :
    Representation (Array (Array α)) (.prod (.buffer .nat) τ) :=
  ((array .nat).prod payload).comap Array.flattenEmbedding

@[simp] theorem raggedArrayOf_rel {α : Type u} {τ : Ty}
    (payload : Representation (Array α) τ) (rows : Array (Array α))
    (value : Buffer .nat × Value τ) (heap : Heap) :
    (raggedArrayOf payload).Rel rows value heap ↔
      value.1.Contents heap rows.flattenOffsets ∧ payload.Rel rows.flatten value.2 heap := Iff.rfl

/-- The row count depends only on the shared boundary buffer. -/
theorem raggedArrayOf_size {α : Type u} {τ : Ty} {payload : Representation (Array α) τ}
    {rows : Array (Array α)} {value : Buffer .nat × Value τ} {heap : Heap}
    (observed : (raggedArrayOf payload).Rel rows value heap) :
    rows.size = value.1.length - 1 := by
  rw [raggedArrayOf_rel] at observed
  have sized := observed.1.size_eq
  simp only [Array.size_flattenOffsets] at sized
  omega

/-- Reuse the same boundaries when exposing a lossless element view. -/
theorem raggedArrayOf_map {α : Type u} {β : Type v} {τ : Ty}
    (payload : Representation (Array β) τ) (view : α ↪ β)
    {rows : Array (Array α)} {value : Buffer .nat × Value τ} {heap : Heap}
    (observed : (raggedArrayOf (payload.comap view.arrayMap)).Rel rows value heap) :
    (raggedArrayOf payload).Rel (rows.map (Array.map view)) value heap := by
  rw [raggedArrayOf_rel] at observed ⊢
  have cells : payload.Rel (rows.flatten.map view) value.2 heap := observed.2
  exact ⟨by simpa only [Array.flattenOffsets_map] using observed.1,
    by simpa only [← Array.map_flatten] using cells⟩

/-- The first payload column is a row view using the original shared boundaries. -/
theorem raggedArrayOf_fst {α : Type u} {β : Type v} {τ σ : Ty}
    {left : Representation (Array α) τ} {right : Representation (Array β) σ}
    {rows : Array (Array (α × β))} {value : Buffer .nat × (Value τ × Value σ)} {heap : Heap}
    (observed : (raggedArrayOf (arrayProd left right)).Rel rows value heap) :
    (raggedArrayOf left).Rel (rows.map (Array.map Prod.fst)) (value.1, value.2.1) heap := by
  rw [raggedArrayOf_rel] at observed ⊢
  have cells : left.Rel (rows.flatten.map Prod.fst) value.2.1 heap := observed.2.1
  exact ⟨by simpa only [Array.flattenOffsets_map] using observed.1,
    by simpa only [← Array.map_flatten] using cells⟩

/-- The second payload column retains the same boundaries and row order. -/
theorem raggedArrayOf_snd {α : Type u} {β : Type v} {τ σ : Ty}
    {left : Representation (Array α) τ} {right : Representation (Array β) σ}
    {rows : Array (Array (α × β))} {value : Buffer .nat × (Value τ × Value σ)} {heap : Heap}
    (observed : (raggedArrayOf (arrayProd left right)).Rel rows value heap) :
    (raggedArrayOf right).Rel (rows.map (Array.map Prod.snd)) (value.1, value.2.2) heap := by
  rw [raggedArrayOf_rel] at observed ⊢
  have cells : right.Rel (rows.flatten.map Prod.snd) value.2.2 heap := observed.2.2
  exact ⟨by simpa only [Array.flattenOffsets_map] using observed.1,
    by simpa only [← Array.map_flatten] using cells⟩

/-- Row observations survive exactly the supplied boundary and payload frames. -/
theorem Preserves.raggedArrayOf {α : Type u} {τ : Ty}
    {payload : Representation (Array α) τ} {initial finish : Heap}
    (boundaries : (array .nat).Preserves initial finish)
    (contents : payload.Preserves initial finish) :
    (raggedArrayOf payload).Preserves initial finish :=
  Preserves.comap Array.flattenEmbedding (Preserves.prod boundaries contents)

/-- A canonical ragged array backed by a boundary buffer and a payload buffer. -/
def raggedArray (kind : CellTy) :
    Representation (Array (Array (CellValue kind))) (.prod (.buffer .nat) (.buffer kind)) :=
  raggedArrayOf (array kind)

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
