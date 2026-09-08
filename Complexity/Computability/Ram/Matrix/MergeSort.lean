/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.Vector
import Complexity.Computability.Ram.Array.Traversal
import Complexity.Computability.Ram.Matrix.Writeback
import Complexity.Tactic.Ram.Model

/-!
# The existing merge-sort call on a matrix row

This module reuses the original recursive array function; it introduces no
sorting program. Its fixed call refines ordinary native matrix modification.
Length preservation is already encoded by the finite-function model, and the
two-buffer write-back rule restores the parent matrix despite actual scratch
writes. Scratch must be allocated outside the matrix. All original scratch,
I/O, return-value and caller-register facts remain available.

The native specification uses mathlib's row-update and sorted-permutation
facts. Correctness does not require an instruction budget; actual time bounds
remain the existing merge-sort call's separate obligation.
-/

namespace Ram.Source.Matrix

variable {w heapLimit selfFn : Nat} {functions : Program} {base scratch : Word w}

/-- Sort one borrowed row by calling the existing array function. The returned
matrix is a native mathlib row update; scratch changes are retained in the
original shared-state assertion, not hidden behind a false row-only frame. -/
theorem sort_row_stateM (entry : State w) (i : Fin m) (dst : Reg)
    (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (Array.MergeSort.function selfFn))
    (hdisjoint : ArraysDisjoint scratch n base (m * n)) :
    Refines functions heapLimit (Nat.clog 2 n + 1)
      (.call [dst] selfFn [.var 0, .var 1, .var 2])
      (fun A s => s = entry ∧ MatrixAt heapLimit base A s ∧
        (∃ workspace, workspace.length = n ∧ ArrayAt heapLimit scratch workspace s) ∧
        s.regs 0 = arrayAddr base (i.val * n) ∧ s.regs 1 = scratch ∧
        (s.regs 2).toNat = n)
      (fun result finish => MatrixAt heapLimit base result.2 finish ∧
        finish.regs dst = 0 ∧
        Array.MergeSort.SharedStateRep heapLimit (arrayAddr base (i.val * n))
          scratch n entry (List.ofFn (result.2 i)) finish.mem finish.input finish.outputRev ∧
        ∀ r, r ≠ dst → finish.regs r = entry.regs r)
      (modify (fun A : Matrix (Fin m) (Fin n) (Word w) =>
        A.updateRow i (Array.MergeSort.sortedFin (A i))) :
        StateM (Matrix (Fin m) (Fin n) (Word w)) PUnit).run := by
  rintro A s ⟨same, represented, workspace, rowPointer, scratchPointer, count⟩
  subst s
  apply Verification.TotalWP.of_contract
    (Array.MergeSort.call_fin_stateM_refines (heapLimit := heapLimit)
      (base := arrayAddr base (i.val * n)) (scratch := scratch)
      n entry dst hw lookup (A i))
  · refine ⟨⟨represented.row_array i, ?_, ?_, rowPointer, scratchPointer, ?_⟩, rfl⟩
    · simpa only [List.length_ofFn] using workspace
    · simpa only [List.length_ofFn] using represented.1.row_disjoint i hdisjoint.symm
    · simpa only [List.length_ofFn] using count
  · rintro finish ⟨zero, shared, locals⟩
    refine ⟨represented.replace_row_array_two i shared.1 shared.2.2.1 hdisjoint,
      zero, ?_, locals⟩
    ram_model at shared ⊢

open Std.Do in
/-- Native verification states the mathematical result and untouched rows
without any RAM registers, memory layout, stack bounds or time arithmetic. -/
theorem sort_row_spec (original : Matrix (Fin m) (Fin n) (Word w)) (i : Fin m) :
    ⦃fun A => ⌜A = original⌝⦄
      (modify (fun A : Matrix (Fin m) (Fin n) (Word w) =>
        A.updateRow i (Array.MergeSort.sortedFin (A i))) :
        StateM (Matrix (Fin m) (Fin n) (Word w)) PUnit)
    ⦃⇓ _ A => ⌜Array.SortedPerm (List.ofFn (original i)) (List.ofFn (A i)) ∧
      ∀ j, j ≠ i → A j = original j⌝⦄ := by
  mvcgen
  rename_i A hA result
  dsimp [result]
  rw [hA]
  constructor
  · simpa only [Matrix.updateRow_self, Array.MergeSort.ofFn_sortedFin] using
      Array.MergeSort.sorted_spec (List.ofFn (original i))
  · intro j different
    exact Matrix.updateRow_ne different

end Ram.Source.Matrix
