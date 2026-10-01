/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.Extract

/-!
# Defaulted reads of rows containing ragged arrays

An in-bounds access uses the real outer boundaries and extracts the selected
inner interval with freshly rebased boundaries. The payload remains borrowed.
An out-of-bounds access returns the entire fallback without allocation.
The operation preserves all prior contents observations, but an in-bounds
access is linear in the selected boundary count, not a constant-time view.
-/

namespace Complexity.Language.Buffer.Ragged

source_program% Nested importing Extract where
  def getNat (storage : Buffer Nat × (Buffer Nat × Buffer Nat)) (index : Nat)
      (fallback : Buffer Nat × Buffer Nat) : Buffer Nat × Buffer Nat := do
    let offsets := storage.1
    if index < offsets.length - 1 then
      let first ← offsets.get index
      let last ← offsets.get (index + 1)
      let row ← Extract.extractNat storage.2 first last
      return row
    else
      return fallback

  def getBool (storage : Buffer Nat × (Buffer Nat × Buffer Bool)) (index : Nat)
      (fallback : Buffer Nat × Buffer Bool) : Buffer Nat × Buffer Bool := do
    let offsets := storage.1
    if index < offsets.length - 1 then
      let first ← offsets.get index
      let last ← offsets.get (index + 1)
      let row ← Extract.extractBool storage.2 first last
      return row
    else
      return fallback

namespace Nested

private theorem read_row_eval {kind : CellTy}
    (extract : (Buffer .nat × Buffer kind) → Nat → Nat →
      ExceptT Fault (StateT Heap Part) (Buffer .nat × Buffer kind))
    (extractCorrect : ∀ (rows : Array (Array (CellValue kind)))
      (storage : Buffer .nat × Buffer kind) (start stop : Nat) (heap : Heap),
      (Representation.raggedArray kind).Rel rows storage heap → start ≤ stop →
        stop ≤ rows.size →
      ∃ returned finish, extract storage start stop heap = Part.some (.ok returned, finish) ∧
        (Representation.raggedArray kind).Rel (rows.extract start stop) returned finish ∧
        heap.ShapeExtends finish ∧ PreservesContents heap finish)
    (rows : Array (Array (Array (CellValue kind)))) (index : Nat)
    (fallback : Array (Array (CellValue kind)))
    (storage : Buffer .nat × (Buffer .nat × Buffer kind))
    (defaultView : Buffer .nat × Buffer kind) (heap : Heap)
    (observed : (Representation.raggedArrayOf (Representation.raggedArray kind)).Rel
      rows storage heap)
    (defaultObserved : (Representation.raggedArray kind).Rel fallback defaultView heap) :
    ∃ returned finish,
      (if index < storage.1.length - 1 then do
        let first ← storage.1.readM index
        let last ← storage.1.readM (index + 1)
        extract storage.2 first last
      else pure defaultView) heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray kind).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  have length := Representation.raggedArrayOf_size observed
  by_cases bound : index < rows.size
  · have firstBound : index < rows.flattenOffsets.size := by simp; omega
    have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
    have available : index < storage.1.length - 1 := by omega
    have firstRead := observed.1.read firstBound
    have lastRead := observed.1.read lastBound
    change heap.read storage.1 index = .ok rows.flattenOffsets[index] at firstRead
    change heap.read storage.1 (index + 1) = .ok rows.flattenOffsets[index + 1] at lastRead
    have rowSize := Array.flattenOffsets_succ rows bound
    have ordered : rows.flattenOffsets[index] ≤ rows.flattenOffsets[index + 1] := by omega
    have stopBound := Array.flattenOffsets_le rows (index + 1) lastBound
    obtain ⟨returned, finish, execution, result, shape, preserved⟩ :=
      extractCorrect rows.flatten storage.2 rows.flattenOffsets[index]
        rows.flattenOffsets[index + 1] heap observed.2 ordered stopBound
    refine ⟨returned, finish, ?_, ?_, shape, preserved⟩
    · simp only [if_pos available, source_eval, firstRead, lastRead]
      exact execution
    · simpa only [Array.extract_flatten_row rows bound, Array.getD, dif_pos bound] using result
  · have unavailable : ¬index < storage.1.length - 1 := by omega
    exact ⟨defaultView, heap, by simp only [if_neg unavailable]; rfl,
      by simpa only [Array.getD, dif_neg bound] using defaultObserved,
      Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The same natural-row lookup observes the ordinary triple-array getD at its
actual return heap, including the unchanged out-of-bounds fallback. -/
theorem getNat_eval_exists_preserving (rows : Array (Array (Array Nat))) (index : Nat)
    (fallback : Array (Array Nat)) (storage : Buffer .nat × (Buffer .nat × Buffer .nat))
    (defaultView : Buffer .nat × Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArrayOf (Representation.raggedArray .nat)).Rel
      rows storage heap)
    (defaultObserved : (Representation.raggedArray .nat).Rel fallback defaultView heap) :
    ∃ returned finish,
      getNat storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray .nat).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  simpa only [getNat_eq, bind_pure, decide_eq_true_eq] using read_row_eval (kind := .nat)
    Extract.extractNat Extract.extractNat_eval_exists_preserving
    rows index fallback storage defaultView heap observed defaultObserved

/-- Boolean rows use the same canonical boundary rebasing, retaining all old aliases. -/
theorem getBool_eval_exists_preserving (rows : Array (Array (Array Bool))) (index : Nat)
    (fallback : Array (Array Bool)) (storage : Buffer .nat × (Buffer .nat × Buffer .bool))
    (defaultView : Buffer .nat × Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArrayOf (Representation.raggedArray .bool)).Rel
      rows storage heap)
    (defaultObserved : (Representation.raggedArray .bool).Rel fallback defaultView heap) :
    ∃ returned finish,
      getBool storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.raggedArray .bool).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  simpa only [getBool_eq, bind_pure, decide_eq_true_eq] using read_row_eval (kind := .bool)
    Extract.extractBool Extract.extractBool_eval_exists_preserving
    rows index fallback storage defaultView heap observed defaultObserved

end Nested
end Complexity.Language.Buffer.Ragged
