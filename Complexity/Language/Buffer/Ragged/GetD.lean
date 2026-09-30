/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.RepresentedFunction
import Complexity.Language.Representation.RaggedArray
import Complexity.Language.Eval.Simp

/-!
# Defaulted row reads from nested arrays

Each in-bounds access reads two actual boundaries and forms a checked borrowed
slice of the payload. No row is copied. An out-of-bounds access returns the
whole fallback view without reading either buffer. Both branches retain the
exact heap, preserving all aliases and existing observations.
-/

namespace Complexity.Language.Buffer.Ragged

source_program% GetD where
  def getNat (storage : Buffer Nat × Buffer Nat) (index : Nat)
      (fallback : Buffer Nat) : Buffer Nat := do
    let offsets := storage.1
    if index < offsets.length - 1 then
      let payload := storage.2
      let first ← offsets.get index
      let last ← offsets.get (index + 1)
      let row ← payload.slice first (last - first)
      return row
    else
      return fallback

  def getBool (storage : Buffer Nat × Buffer Bool) (index : Nat)
      (fallback : Buffer Bool) : Buffer Bool := do
    let offsets := storage.1
    if index < offsets.length - 1 then
      let payload := storage.2
      let first ← offsets.get index
      let last ← offsets.get (index + 1)
      let row ← payload.slice first (last - first)
      return row
    else
      return fallback

namespace GetD

private theorem readM_getD {kind : CellTy} (rows : Array (Array (CellValue kind)))
    (index : Nat) (fallback : Array (CellValue kind))
    (storage : Buffer .nat × Buffer kind) (defaultView : Buffer kind) (heap : Heap)
    (observed : (Representation.raggedArray kind).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback) :
    ∃ returned,
      (if index < storage.1.length - 1 then do
        let first ← storage.1.readM index
        let last ← storage.1.readM (index + 1)
        storage.2.sliceM first (last - first)
      else pure defaultView) heap = Part.some (.ok returned, heap) ∧
        returned.Contents heap (rows.getD index fallback) := by
  have length := Representation.raggedArray_length observed
  by_cases bound : index < rows.size
  · have firstBound : index < rows.flattenOffsets.size := by simp; omega
    have lastBound : index + 1 < rows.flattenOffsets.size := by simp; omega
    have available : index < storage.1.length - 1 := by omega
    have firstRead := observed.1.read firstBound
    have lastRead := observed.1.read lastBound
    change heap.read storage.1 index = .ok rows.flattenOffsets[index] at firstRead
    change heap.read storage.1 (index + 1) = .ok rows.flattenOffsets[index + 1] at lastRead
    have rowLength := Array.flattenOffsets_succ rows bound
    have fits : rows.flattenOffsets[index] + rows[index].size ≤ storage.2.length := by
      have stop := Array.flattenOffsets_le rows (index + 1) lastBound
      have payloadSize : rows.flatten.size = storage.2.length := observed.2.size_eq
      rw [rowLength, payloadSize] at stop
      exact stop
    refine ⟨⟨storage.2.object, storage.2.offset + rows.flattenOffsets[index],
      rows[index].size⟩, ?_, ?_⟩
    · simp only [if_pos available, source_eval, firstRead, lastRead, rowLength,
        Nat.add_sub_cancel_left, storage.2.slice_eq fits]
    · simpa only [Array.getD, dif_pos bound] using
        Representation.raggedArray_row observed bound
  · have unavailable : ¬index < storage.1.length - 1 := by omega
    exact ⟨defaultView, by simp only [if_neg unavailable]; rfl,
      by simpa only [Array.getD, dif_neg bound] using defaultObserved⟩

/-- The real row lookup returns a view of Lean's defaulted row in the unchanged heap. -/
theorem getNat_eval (rows : Array (Array Nat)) (index : Nat) (fallback : Array Nat)
    (storage : Buffer .nat × Buffer .nat) (defaultView : Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback) :
    ∃ returned, getNat storage index defaultView heap = Part.some (.ok returned, heap) ∧
      returned.Contents heap (rows.getD index fallback) := by
  simpa [getNat_eq] using
    readM_getD (kind := .nat) rows index fallback storage defaultView heap observed defaultObserved

/-- Both the selected row and the fallback observe real buffers, not host arrays. -/
def natRepresentation :
    FunctionRepresentation (Array (Array Nat) × Nat × Array Nat)
      (fun _ => Array Nat) signatures[getNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons (Representation.raggedArray .nat)
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single (Representation.array .nat))))
    (fun _ => Representation.array .nat)

/-- Defaulted row lookup refines the ordinary Lean array operation. -/
theorem getNat_refines :
    RepresentedFunction.Refines program getNatId natRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  change input.2.1 = args.tail.head at index
  obtain ⟨returned, execution, result⟩ := getNat_eval input.1 input.2.1 input.2.2
    args.head args.tail.tail.head heap contents fallback
  refine ⟨returned, heap, ?_, result⟩
  rw [getNat_observe, ← index]
  exact execution

/-- Every prior contents observation survives, including aliases of a selected row. -/
theorem getNat_eval_exists_preserving (rows : Array (Array Nat)) (index : Nat)
    (fallback : Array Nat) (storage : Buffer .nat × Buffer .nat)
    (defaultView : Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (defaultObserved : (Representation.array .nat).Rel fallback defaultView heap) :
    ∃ returned finish,
      getNat storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  obtain ⟨returned, execution, result⟩ :=
    getNat_eval rows index fallback storage defaultView heap observed defaultObserved
  exact ⟨returned, heap, execution, result, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- The real row lookup returns a view of Lean's defaulted row in the unchanged heap. -/
theorem getBool_eval (rows : Array (Array Bool)) (index : Nat) (fallback : Array Bool)
    (storage : Buffer .nat × Buffer .bool) (defaultView : Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback) :
    ∃ returned, getBool storage index defaultView heap = Part.some (.ok returned, heap) ∧
      returned.Contents heap (rows.getD index fallback) := by
  simpa [getBool_eq] using
    readM_getD (kind := .bool) rows index fallback storage defaultView heap observed defaultObserved

/-- Both the selected row and the fallback observe real buffers, not host arrays. -/
def boolRepresentation :
    FunctionRepresentation (Array (Array Bool) × Nat × Array Bool)
      (fun _ => Array Bool) signatures[getBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons (Representation.raggedArray .bool)
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single (Representation.array .bool))))
    (fun _ => Representation.array .bool)

/-- Defaulted row lookup refines the ordinary Lean array operation. -/
theorem getBool_refines :
    RepresentedFunction.Refines program getBoolId boolRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  change input.2.1 = args.tail.head at index
  obtain ⟨returned, execution, result⟩ := getBool_eval input.1 input.2.1 input.2.2
    args.head args.tail.tail.head heap contents fallback
  refine ⟨returned, heap, ?_, result⟩
  rw [getBool_observe, ← index]
  exact execution

/-- Every prior contents observation survives, including aliases of a selected row. -/
theorem getBool_eval_exists_preserving (rows : Array (Array Bool)) (index : Nat)
    (fallback : Array Bool) (storage : Buffer .nat × Buffer .bool)
    (defaultView : Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (defaultObserved : (Representation.array .bool).Rel fallback defaultView heap) :
    ∃ returned finish,
      getBool storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.array .bool).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  obtain ⟨returned, execution, result⟩ :=
    getBool_eval rows index fallback storage defaultView heap observed defaultObserved
  exact ⟨returned, heap, execution, result, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame observes the selected or fallback row. -/
theorem getNat_eval_exists (rows : Array (Array Nat)) (index : Nat)
    (fallback : Array Nat) (storage : Buffer .nat × Buffer .nat)
    (defaultView : Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (defaultObserved : (Representation.array .nat).Rel fallback defaultView heap) :
    ∃ returned finish,
      getNat storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, result, shape, _⟩ :=
    getNat_eval_exists_preserving rows index fallback storage defaultView heap
      observed defaultObserved
  exact ⟨returned, finish, execution, result, shape⟩


/-- The standard represented-call frame observes the selected or fallback row. -/
theorem getBool_eval_exists (rows : Array (Array Bool)) (index : Nat)
    (fallback : Array Bool) (storage : Buffer .nat × Buffer .bool)
    (defaultView : Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (defaultObserved : (Representation.array .bool).Rel fallback defaultView heap) :
    ∃ returned finish,
      getBool storage index defaultView heap = Part.some (.ok returned, finish) ∧
      (Representation.array .bool).Rel (rows.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, result, shape, _⟩ :=
    getBool_eval_exists_preserving rows index fallback storage defaultView heap
      observed defaultObserved
  exact ⟨returned, finish, execution, result, shape⟩


end GetD
end Complexity.Language.Buffer.Ragged
