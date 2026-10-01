/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Ragged.GetD
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Buffer
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic

/-!
# Readiness of borrowed defaulted row reads

The existing row operation reads two boundaries and returns a checked slice,
or returns the whole fallback out of bounds. It never reads payload cells,
copies rows or allocates storage. Its exact descriptor, contents, unchanged
heap and cursor can be reused by subsequent calls. Costs are supplied
independently by the existing compiler-derived operation bounds.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.GetD

open Complexity.Language
open Complexity.Language.Buffer.Ragged.GetD

/-- Mathematical description of the descriptor returned by the actual row
operation. Computing this specification is not a free runtime operation. -/
def getView {kind : CellTy} (rows : Array (Array (CellValue kind))) (index : Nat)
    (storage : Buffer .nat × Buffer kind) (fallback : Buffer kind) : Buffer kind :=
  if inside : index < rows.size then
    ⟨storage.2.object, storage.2.offset + rows.flattenOffsets[index]'(by simp; omega),
      rows[index].size⟩
  else fallback

/-- The described descriptor observes exactly the selected row or fallback
in the supplied heap. This is a representation fact, not an execution rule. -/
theorem getView_contents {kind : CellTy} {rows : Array (Array (CellValue kind))}
    {storage : Buffer .nat × Buffer kind} {defaultView : Buffer kind}
    {heap : Heap} {fallback : Array (CellValue kind)}
    (observed : (Representation.raggedArray kind).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback) (index : Nat) :
    (getView (kind := kind) rows index storage defaultView).Contents heap
      (rows.getD index fallback) := by
  by_cases inside : index < rows.size
  · simpa only [getView, dif_pos inside, Array.getD] using
      Representation.raggedArray_row observed inside
  · simpa only [getView, dif_neg inside, Array.getD] using defaultObserved

/-- The selected descriptor fits whenever the whole payload and fallback do.
This also covers empty rows and out-of-bounds selection. -/
theorem getView_length_fits {kind : CellTy} {rows : Array (Array (CellValue kind))}
    {storage : Buffer .nat × Buffer kind} {defaultView : Buffer kind} {w : Nat}
    (payloadFits : rows.flatten.size < 2 ^ w)
    (defaultFits : defaultView.length < 2 ^ w) (index : Nat) :
    (getView (kind := kind) rows index storage defaultView).length < 2 ^ w := by
  by_cases inside : index < rows.size
  · simp only [getView, dif_pos inside]
    have stop := Array.flattenOffsets_le rows (index + 1) (by simp; omega)
    rw [Array.flattenOffsets_succ rows inside] at stop
    omega
  · simpa only [getView, dif_neg inside] using defaultFits

/-- The actual nat row selection retains its borrowed view and exact heap.
No bound on unread payload values is required. -/
theorem getNat_arenaMeasured {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (rows : Array (Array Nat)) (index : Nat) (fallback : Array Nat)
    (storage : Buffer .nat × Buffer .nat) (defaultView : Buffer .nat) (heap : Heap)
    (observed : (Representation.raggedArray .nat).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback)
    (rowsFit : rows.size + 1 < 2 ^ w) (payloadFits : rows.flatten.size < 2 ^ w)
    (indexFits : index < 2 ^ w) (defaultFits : defaultView.length < 2 ^ w) :
    ArenaMeasured program w heapLimit depth (program.body getNatId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        returned = getView (kind := .nat) rows index storage defaultView ∧
        returned.Contents finish.heap (rows.getD index fallback) ∧
        finish.heap = heap ∧ finalCursor = cursor)
      ⟨getNat_args storage index defaultView, heap⟩ cursor := by
  have offsetsSize := Representation.raggedArray_length observed
  change storage.1.Contents heap rows.flattenOffsets ∧
    storage.2.Contents heap rows.flatten at observed
  have offsetsFits : storage.1.length < 2 ^ w := by omega
  have lengthFits : storage.1.length - 1 < 2 ^ w := by omega
  have payloadFit : storage.2.length < 2 ^ w := by
    simpa only [observed.2.size_eq] using payloadFits
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
    have firstFits : first < 2 ^ w :=
      (Array.flattenOffsets_le rows index firstBound).trans_lt payloadFits
    have lastFits : last < 2 ^ w :=
      (Array.flattenOffsets_le rows (index + 1) lastBound).trans_lt payloadFits
    have nextFits : index + 1 < 2 ^ w := by omega
    have rowStep : last = first + rows[index].size :=
      Array.flattenOffsets_succ rows inside
    have countEq : last - first = rows[index].size := by omega
    have countFits : last - first < 2 ^ w := by omega
    have payloadBound : first + (last - first) ≤ storage.2.length := by
      have lastBounded := Array.flattenOffsets_le rows (index + 1) lastBound
      rw [observed.2.size_eq] at lastBounded
      omega
    let view : Buffer .nat :=
      ⟨storage.2.object, storage.2.offset + first, last - first⟩
    have viewed : view.Contents heap (rows.getD index fallback) := by
      simpa only [view, first, countEq, Array.getD, dif_pos inside] using
        Representation.raggedArray_row observed inside
    have viewEq : view = getView (kind := .nat) rows index storage defaultView := by
      simp only [view, getView, dif_pos inside, countEq, first]
    change ArenaMeasured program w heapLimit depth getNatBody _ _ _
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
    apply ArenaMeasured.slice (view := view)
    · exact storage.2.slice_eq payloadBound
    · exact payloadFit
    · exact firstFits
    · exact countFits
    · exact countFits
    ram_source_arena_step
  · have selected : decide (index < storage.1.length - 1) = false := by
      apply decide_eq_false
      omega
    change ArenaMeasured program w heapLimit depth getNatBody _ _ _
    ram_source_arena_step
    simpa only [getView, dif_neg inside, Array.getD, true_and] using defaultObserved

/-- The actual bool row selection retains its borrowed view and exact heap.
No bound on unread payload values is required. -/
theorem getBool_arenaMeasured {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (rows : Array (Array Bool)) (index : Nat) (fallback : Array Bool)
    (storage : Buffer .nat × Buffer .bool) (defaultView : Buffer .bool) (heap : Heap)
    (observed : (Representation.raggedArray .bool).Rel rows storage heap)
    (defaultObserved : defaultView.Contents heap fallback)
    (rowsFit : rows.size + 1 < 2 ^ w) (payloadFits : rows.flatten.size < 2 ^ w)
    (indexFits : index < 2 ^ w) (defaultFits : defaultView.length < 2 ^ w) :
    ArenaMeasured program w heapLimit depth (program.body getBoolId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        returned = getView (kind := .bool) rows index storage defaultView ∧
        returned.Contents finish.heap (rows.getD index fallback) ∧
        finish.heap = heap ∧ finalCursor = cursor)
      ⟨getBool_args storage index defaultView, heap⟩ cursor := by
  have offsetsSize := Representation.raggedArray_length observed
  change storage.1.Contents heap rows.flattenOffsets ∧
    storage.2.Contents heap rows.flatten at observed
  have offsetsFits : storage.1.length < 2 ^ w := by omega
  have lengthFits : storage.1.length - 1 < 2 ^ w := by omega
  have payloadFit : storage.2.length < 2 ^ w := by
    simpa only [observed.2.size_eq] using payloadFits
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
    have firstFits : first < 2 ^ w :=
      (Array.flattenOffsets_le rows index firstBound).trans_lt payloadFits
    have lastFits : last < 2 ^ w :=
      (Array.flattenOffsets_le rows (index + 1) lastBound).trans_lt payloadFits
    have nextFits : index + 1 < 2 ^ w := by omega
    have rowStep : last = first + rows[index].size :=
      Array.flattenOffsets_succ rows inside
    have countEq : last - first = rows[index].size := by omega
    have countFits : last - first < 2 ^ w := by omega
    have payloadBound : first + (last - first) ≤ storage.2.length := by
      have lastBounded := Array.flattenOffsets_le rows (index + 1) lastBound
      rw [observed.2.size_eq] at lastBounded
      omega
    let view : Buffer .bool :=
      ⟨storage.2.object, storage.2.offset + first, last - first⟩
    have viewed : view.Contents heap (rows.getD index fallback) := by
      simpa only [view, first, countEq, Array.getD, dif_pos inside] using
        Representation.raggedArray_row observed inside
    have viewEq : view = getView (kind := .bool) rows index storage defaultView := by
      simp only [view, getView, dif_pos inside, countEq, first]
    change ArenaMeasured program w heapLimit depth getBoolBody _ _ _
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
    apply ArenaMeasured.slice (view := view)
    · exact storage.2.slice_eq payloadBound
    · exact payloadFit
    · exact firstFits
    · exact countFits
    · exact countFits
    ram_source_arena_step
  · have selected : decide (index < storage.1.length - 1) = false := by
      apply decide_eq_false
      omega
    change ArenaMeasured program w heapLimit depth getBoolBody _ _ _
    ram_source_arena_step
    simpa only [getView, dif_neg inside, Array.getD, true_and] using defaultObserved

end Ram.LanguageCompiler.Buffer.Ragged.GetD
