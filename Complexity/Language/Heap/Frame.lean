/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Shape

/-!
# Cell-local heap frames

A footprint is a set of object identifiers paired with absolute cell indices.
`Heap.PreservesOutside` permits updates within that set while retaining heap
shape and every read outcome outside it. In particular, recursive operations
can protect other nodes stored in the same arrays, without asserting that the
arrays occupy different heap objects.

The relation concerns the actual initial and final heaps. It does not assign
ownership, copy data, or introduce a new execution semantics.
-/

namespace Complexity.Language

namespace Heap

/-- A successful read supplies its object lookup, whole-view extent, local
index bound and native array value. These facts can also justify a later write. -/
theorem read_eq_ok_iff {heap : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ} :
    heap.read buffer index = .ok value ↔
      ∃ (values : Array (CellValue τ)) (_ : heap.object? τ buffer.object = some values)
        (extent : buffer.offset + buffer.length ≤ values.size) (bound : index < buffer.length),
        getElem values (buffer.offset + index) (by omega) = value := by
  constructor
  · intro readValue
    cases found : heap.object? τ buffer.object with
    | none => simp [read, found] at readValue
    | some values =>
        by_cases extent : buffer.offset + buffer.length ≤ values.size
        · by_cases bound : index < buffer.length
          · exact ⟨values, rfl, extent, bound,
              Except.ok.inj ((read_eq found extent bound).symm.trans readValue)⟩
          · simp [read, found, extent, bound] at readValue
        · simp [read, found, extent] at readValue
  · rintro ⟨values, found, extent, bound, rfl⟩
    exact read_eq found extent bound

/-- A successful read establishes all access conditions for writing a new
value to the same cell. No second object or index proof is needed. -/
theorem write_exists_of_read {heap : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {previous : CellValue τ}
    (readValue : heap.read buffer index = .ok previous) (value : CellValue τ) :
    ∃ finish, heap.write buffer index value = .ok finish := by
  obtain ⟨values, found, extent, bound, _⟩ := read_eq_ok_iff.mp readValue
  exact ⟨heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value),
    write_eq_ok_iff.mpr ⟨values, found, extent, bound, rfl⟩⟩

private theorem object?_eq_none_of_type_ne {heap : Heap} {τ σ : CellTy}
    {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) (different : τ ≠ σ) :
    heap.object? σ object = none := by
  cases otherFound : heap.object? σ object with
  | none => rfl
  | some otherValues =>
      have sameStored : HeapObject.buffer τ values = .buffer σ otherValues :=
        Option.some.inj ((object?_eq_some_iff.mp found).symm.trans
          (object?_eq_some_iff.mp otherFound))
      exact (different (congrArg HeapObject.kind sameStored)).elim

/-- A write cannot change reads at a different scalar type, even if the object
identifiers coincide: the latter reads retain their invalid-object error. -/
theorem read_write_of_type_ne {heap finish : Heap} {τ σ : CellTy}
    {buffer : Buffer τ} {other : Buffer σ} {index otherIndex : Nat}
    {value : CellValue τ} (written : heap.write buffer index value = .ok finish)
    (different : τ ≠ σ) :
    finish.read other otherIndex = heap.read other otherIndex := by
  by_cases sameObject : buffer.object = other.object
  · obtain ⟨values, found, _, _, rfl⟩ := write_eq_ok_iff.mp written
    have original : heap.object? σ other.object = none := by
      rw [← sameObject]
      exact object?_eq_none_of_type_ne found different
    have updated :
        (heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)).object?
          σ other.object = none := by
      rw [← sameObject]
      exact object?_eq_none_of_type_ne (object?_replace_self (object_lt_size found)) different
    simp only [read, original, updated]
  · exact read_write_of_ne written sameObject

/-- Reads at a different object/cell pair are unchanged, including errors and
reads through a buffer with a different scalar type. -/
theorem read_write_of_ne_location {heap finish : Heap} {τ σ : CellTy}
    {buffer : Buffer τ} {other : Buffer σ} {index otherIndex : Nat}
    {value : CellValue τ} (written : heap.write buffer index value = .ok finish)
    (different : (buffer.object, buffer.offset + index) ≠
      (other.object, other.offset + otherIndex)) :
    finish.read other otherIndex = heap.read other otherIndex := by
  by_cases sameObject : buffer.object = other.object
  · by_cases sameType : τ = σ
    · subst σ
      apply read_write_of_ne_cell written sameObject
      intro sameCell
      exact different (Prod.ext sameObject sameCell)
    · exact read_write_of_type_ne written sameType
  · exact read_write_of_ne written sameObject

/-- Disjoint views retain all read outcomes after a write, including invalid
indices. The two views may be disjoint slices of the same object. -/
theorem read_write_of_disjoint {heap finish : Heap} {τ σ : CellTy}
    {buffer : Buffer τ} {other : Buffer σ} {index otherIndex : Nat}
    {value : CellValue τ} (written : heap.write buffer index value = .ok finish)
    (separated : buffer.Disjoint other) :
    finish.read other otherIndex = heap.read other otherIndex := by
  by_cases sameObject : buffer.object = other.object
  · by_cases sameType : τ = σ
    · subst σ
      obtain ⟨values, found, _, indexBound, updatedHeap⟩ := write_eq_ok_iff.mp written
      by_cases otherBound : otherIndex < other.length
      · apply read_write_of_ne_cell written sameObject
        intro sameCell
        have intervals := separated.resolve_left (fun different => different sameObject)
        exact Set.disjoint_left.mp intervals
          (show buffer.offset + index ∈
            Set.Ico buffer.offset (buffer.offset + buffer.length) from ⟨by omega, by omega⟩)
          (show buffer.offset + index ∈
            Set.Ico other.offset (other.offset + other.length) from ⟨by omega, by omega⟩)
      · subst finish
        have original : heap.object? τ other.object = some values := by
          simpa only [← sameObject] using found
        have updated :
            (heap.replace buffer.object
              (values.setIfInBounds (buffer.offset + index) value)).object? τ other.object =
                some (values.setIfInBounds (buffer.offset + index) value) := by
          rw [← sameObject]
          exact object?_replace_self (object_lt_size found)
        simp [read, original, updated, otherBound]
    · exact read_write_of_type_ne written sameType
  · exact read_write_of_ne written sameObject

/-- Existing object shapes and every read outside the allowed absolute cells
are preserved. This includes failed reads, not only previously observed values. -/
structure PreservesOutside (allowed : Set (Nat × Nat)) (initial finish : Heap) : Prop where
  /-- Existing object identifiers, scalar types and extents survive. -/
  shape : ShapeExtends initial finish
  /-- Every read outside the footprint retains its exact result. -/
  read_eq : ∀ {τ : CellTy} (buffer : Buffer τ) (index : Nat),
    (buffer.object, buffer.offset + index) ∉ allowed →
      finish.read buffer index = initial.read buffer index

namespace PreservesOutside

/-- An unchanged heap preserves every cell. -/
theorem refl (allowed : Set (Nat × Nat)) (heap : Heap) :
    PreservesOutside allowed heap heap :=
  ⟨ShapeExtends.refl heap, fun _ _ _ => rfl⟩

/-- Cell-local frames compose through the actual intermediate heap. -/
theorem trans {allowed : Set (Nat × Nat)} {initial middle finish : Heap}
    (first : PreservesOutside allowed initial middle)
    (second : PreservesOutside allowed middle finish) :
    PreservesOutside allowed initial finish :=
  ⟨first.shape.trans second.shape,
    fun buffer index outside =>
      (second.read_eq buffer index outside).trans (first.read_eq buffer index outside)⟩

/-- Permitting more cells weakens the frame without changing either heap. -/
theorem mono {allowed larger : Set (Nat × Nat)} {initial finish : Heap}
    (preserved : PreservesOutside allowed initial finish) (included : allowed ⊆ larger) :
    PreservesOutside larger initial finish :=
  ⟨preserved.shape, fun buffer index outside =>
    preserved.read_eq buffer index (fun member => outside (included member))⟩

/-- A successful write modifies at most its single absolute cell. -/
theorem write_singleton {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    PreservesOutside {(buffer.object, buffer.offset + index)} heap finish := by
  refine ⟨shapeExtends_write written, ?_⟩
  intro σ other otherIndex outside
  apply read_write_of_ne_location written
  intro same
  exact outside (Set.mem_singleton_iff.mpr same.symm)

/-- A successful write is framed by any footprint containing its actual cell. -/
theorem write {allowed : Set (Nat × Nat)} {heap finish : Heap} {τ : CellTy}
    {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (member : (buffer.object, buffer.offset + index) ∈ allowed) :
    PreservesOutside allowed heap finish :=
  (write_singleton written).mono (Set.singleton_subset_iff.mpr member)

/-- A view whose cells all lie outside the footprint retains its ordinary
array contents, even when allowed cells belong to the same object. -/
theorem contents {allowed : Set (Nat × Nat)} {initial finish : Heap}
    (preserved : PreservesOutside allowed initial finish) {τ : CellTy}
    {buffer : Buffer τ} {values : Array (CellValue τ)}
    (observed : buffer.Contents initial values)
    (outside : ∀ index, index < buffer.length →
      (buffer.object, buffer.offset + index) ∉ allowed) :
    buffer.Contents finish values := by
  apply Buffer.Contents.of_read (observed.valid.mono preserved.shape) observed.size_eq
  intro index bound
  rw [preserved.read_eq buffer index (outside index (by simpa only [observed.size_eq] using bound))]
  exact observed.read bound

end PreservesOutside

end Heap

namespace Buffer

/-- Valid local indices in disjoint views denote different absolute cells,
including when the views are slices of the same object. -/
theorem Disjoint.location_ne {τ σ : CellTy} {buffer : Buffer τ} {other : Buffer σ}
    (separated : buffer.Disjoint other) {index otherIndex : Nat}
    (bound : index < buffer.length) (otherBound : otherIndex < other.length) :
    (buffer.object, buffer.offset + index) ≠ (other.object, other.offset + otherIndex) := by
  intro same
  have sameObject : buffer.object = other.object := congrArg Prod.fst same
  have sameCell : buffer.offset + index = other.offset + otherIndex := congrArg Prod.snd same
  rcases separated with different | intervals
  · exact different sameObject
  · exact Set.disjoint_left.mp intervals
      (show buffer.offset + index ∈ Set.Ico buffer.offset (buffer.offset + buffer.length)
        from ⟨by omega, by omega⟩)
      (show buffer.offset + index ∈ Set.Ico other.offset (other.offset + other.length)
        from ⟨by omega, by omega⟩)

end Buffer

end Complexity.Language
