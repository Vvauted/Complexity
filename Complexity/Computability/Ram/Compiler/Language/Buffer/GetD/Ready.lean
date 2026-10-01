/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.GetD
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Buffer
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic

/-!
# Readiness of defaulted scalar-array reads

The actual bounds check selects a read or the supplied fallback. Only the
selected natural value needs a cell-range proof; unrelated cells are not read.
Both branches retain the exact heap and cursor. These witnesses use the existing
compiler counts, separately bounded by the defaulted reader's cost contracts.
-/

namespace Ram.LanguageCompiler.Buffer.GetD

open Complexity.Language
open Complexity.Language.Buffer.GetD

/-- Measure the actual natural read, without bounding unobserved array cells. -/
theorem getNat_arenaMeasured {w heapLimit depth cursor : Nat}
    (values : Array Nat) (index fallback : Nat) (source : Buffer .nat) (heap : Heap)
    (observed : source.Contents heap values)
    (lengthFits : source.length < 2 ^ w) (indexFits : index < 2 ^ w)
    (fallbackFits : fallback < 2 ^ w) (resultFits : values.getD index fallback < 2 ^ w) :
    ArenaMeasured program w heapLimit depth (program.body getNatId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        returned = values.getD index fallback ∧ finish.heap = heap ∧ finalCursor = cursor)
      ⟨getNat_args source index fallback, heap⟩ cursor := by
  by_cases inside : index < values.size
  · have selected : decide (index < source.length) = true := by
      apply decide_eq_true
      simpa only [observed.size_eq] using inside
    have selectedFits : values[index] < 2 ^ w := by
      simpa only [Array.getD, dif_pos inside] using resultFits
    change ArenaMeasured program w heapLimit depth getNatBody _ _ _
    ram_source_arena_step
    apply ArenaMeasured.read (value := values[index])
    · exact observed.read inside
    · exact lengthFits
    · exact indexFits
    · exact selectedFits
    ram_source_arena_step
    simp only [Array.getD, dif_pos inside]
    rfl
  · have selected : decide (index < source.length) = false := by
      apply decide_eq_false
      simpa only [observed.size_eq] using inside
    change ArenaMeasured program w heapLimit depth getNatBody _ _ _
    ram_source_arena_step
    simp only [Array.getD, dif_neg inside]

/-- Boolean lookup has the same branch-sensitive read and unchanged heap. -/
theorem getBool_arenaMeasured {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (values : Array Bool) (index : Nat) (fallback : Bool) (source : Buffer .bool) (heap : Heap)
    (observed : source.Contents heap values)
    (lengthFits : source.length < 2 ^ w) (indexFits : index < 2 ^ w) :
    ArenaMeasured program w heapLimit depth (program.body getBoolId)
      (fun finish control finalCursor _ => ∃ returned, control = .returned returned ∧
        returned = values.getD index fallback ∧ finish.heap = heap ∧ finalCursor = cursor)
      ⟨getBool_args source index fallback, heap⟩ cursor := by
  have booleanFits : ∀ value : Bool, ValueFits w (τ := .bool) value := by
    intro value
    cases value
    · exact Nat.two_pow_pos w
    · exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  have fallbackFits := booleanFits fallback
  by_cases inside : index < values.size
  · have selected : decide (index < source.length) = true := by
      apply decide_eq_true
      simpa only [observed.size_eq] using inside
    have selectedFits := booleanFits values[index]
    change ArenaMeasured program w heapLimit depth getBoolBody _ _ _
    ram_source_arena_step
    apply ArenaMeasured.read (value := values[index])
    · exact observed.read inside
    · exact lengthFits
    · exact indexFits
    · exact selectedFits
    ram_source_arena_step
    simp only [Array.getD, dif_pos inside]
    rfl
  · have selected : decide (index < source.length) = false := by
      apply decide_eq_false
      simpa only [observed.size_eq] using inside
    change ArenaMeasured program w heapLimit depth getBoolBody _ _ _
    ram_source_arena_step
    simp only [Array.getD, dif_neg inside]

end Ram.LanguageCompiler.Buffer.GetD
