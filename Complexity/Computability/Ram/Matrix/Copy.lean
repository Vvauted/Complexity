/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Traversal
import Complexity.Computability.Ram.Matrix.Writeback
import Complexity.Computability.Ram.Verification.StateM.Basic

/-!
# Existing array copy as a native matrix row update

The executable statement is the already verified fixed `Source.Array.copy`
loop. Its destination is a borrowed row; the write-back theorem recovers the
whole mathlib matrix. The model is ordinary native `modify` with
`Matrix.updateRow`, so further correctness reasoning can use native stateful
specifications and existing matrix facts.

The functional interface has no instruction budget. The underlying copy
contract separately retains its actual `19 * n + 2` bound, all final operand
registers, source contents, memory frame and I/O. A row update is not treated
as a one-step machine instruction. Source and destination must be disjoint;
the source need not be disjoint from the rest of the matrix.
-/

namespace Ram.Source.Matrix

variable {heapLimit depth : Nat} {program : Program} {base source : Word w}

/-- Copy a represented finite function into a matrix row using the existing
array loop, and expose its result as ordinary native state modification.
The original copy postcondition remains available for subsequent calls. -/
theorem copy_row_stateM (entry : State w) (i : Fin m) (values : Fin n → Word w)
    (hw : 0 < w)
    (hdisjoint : ArraysDisjoint source n (arrayAddr base (i.val * n)) n) :
    Refines program heapLimit depth Array.copy
      (fun A s => s = entry ∧ MatrixAt heapLimit base A s ∧
        ArrayAt heapLimit source (List.ofFn values) s ∧
        s.regs 0 = source ∧ s.regs 1 = arrayAddr base (i.val * n) ∧
        (s.regs 2).toNat = n)
      (fun result finish => MatrixAt heapLimit base result.2 finish ∧
        Array.CopyPost heapLimit source (arrayAddr base (i.val * n))
          (List.ofFn values) entry finish)
      (modify (fun A : Matrix (Fin m) (Fin n) (Word w) => A.updateRow i values) :
        StateM (Matrix (Fin m) (Fin n) (Word w)) PUnit).run := by
  rintro A s ⟨same, represented, inputArray, sourcePointer, destinationPointer, count⟩
  subst s
  have copied := Array.copy_total_contract (program := program)
    (heapLimit := heapLimit) (depth := depth)
    (xs := List.ofFn values) (ys := List.ofFn (A i)) hw
    (by simp only [List.length_ofFn])
    (by simpa only [List.length_ofFn] using hdisjoint)
  apply Verification.TotalWP.of_relContract copied
  · exact ⟨inputArray, represented.row_array i, sourcePointer, destinationPointer,
      by simpa only [List.length_ofFn] using count⟩
  · intro finish post
    exact ⟨represented.replace_row_array i post.destination_array
      (by simpa only [List.length_ofFn] using post.frame), post⟩

end Ram.Source.Matrix
