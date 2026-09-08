/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Indexed
import Complexity.Computability.Ram.Array.Slice
import Complexity.Computability.Ram.Matrix.Frame
import Complexity.Computability.Ram.Memory.Indexed.Writeback

/-!
# Recovering a matrix after modifying a view

The generic indexed write-back rule recovers ordinary mathlib row and column
updates from a new view and the block's actual memory frame. Row-major rows
also expose the existing contiguous array representation, so verified array
operations can update a row without reproving every untouched matrix entry.
These are representation theorems, not new bulk machine instructions.
-/

namespace Ram

/-- A row's indexed address is the corresponding ordinary array address. -/
theorem matrixAddr_row (base : Word w) (i : Fin m) (j : Fin n) :
    matrixAddr base i j = arrayAddr (arrayAddr base (i.val * n)) j.val := by
  rw [arrayAddr_add, matrixAddr_eq]

namespace MatrixRep

variable {before after : Word w → Word w} {base : Word w}
  {A : Matrix (Fin m) (Fin n) (Word w)}

/-- Recover the whole matrix from a modified row and equality outside that
row. Address separation follows from the original row-major fitting bound. -/
theorem replace_row (h : MatrixRep before base A) (i : Fin m)
    {values : Fin n → Word w} (updated : IndexedRep after (matrixAddr base i) values)
    (frame : Set.EqOn after before (Set.range (matrixAddr base i : Fin n → Word w))ᶜ) :
    MatrixRep after base (A.updateRow i values) := by
  have joined := h.indexed.replace_on (matrixAddr_injective h.fits)
    (changed := {p : Fin m × Fin n | p.1 = i})
    (new := fun p => values p.2)
    (by rintro ⟨r, c⟩ (rfl : r = i); exact updated c)
    (by
      intro address outside
      apply frame
      rintro ⟨j, rfl⟩
      exact outside ⟨(i, j), rfl, rfl⟩)
  refine ⟨h.fits, ?_⟩
  intro p
  simpa only [Function.uncurry, Set.piecewise, Set.mem_setOf_eq,
    Matrix.updateRow_apply] using joined p

/-- Columns use the same write-back rule even though their cells are not
contiguous. This does not assert a row-major layout for a transposed matrix. -/
theorem replace_col (h : MatrixRep before base A) (j : Fin n)
    {values : Fin m → Word w}
    (updated : IndexedRep after (fun i => matrixAddr base i j) values)
    (frame : Set.EqOn after before (Set.range (fun i : Fin m => matrixAddr base i j))ᶜ) :
    MatrixRep after base (A.updateCol j values) := by
  have joined := h.indexed.replace_on (matrixAddr_injective h.fits)
    (changed := {p : Fin m × Fin n | p.2 = j})
    (new := fun p => values p.1)
    (by rintro ⟨r, c⟩ (rfl : c = j); exact updated r)
    (by
      intro address outside
      apply frame
      rintro ⟨i, rfl⟩
      exact outside ⟨(i, j), rfl, rfl⟩)
  refine ⟨h.fits, ?_⟩
  intro p
  simpa only [Function.uncurry, Set.piecewise, Set.mem_setOf_eq,
    Matrix.updateCol_apply] using joined p

/-- The start of a valid row does not wrap, including an empty row. -/
theorem row_base_toNat (h : MatrixRep before base A) (i : Fin m) :
    (arrayAddr base (i.val * n)).toNat = base.toNat + i.val * n := by
  apply arrayAddr_toNat
  by_cases hn : n = 0
  · simpa only [hn, Nat.mul_zero, Nat.add_zero] using Word.toNat_lt base
  · have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hrow
    have hfit := h.fits
    omega

/-- A row inherits disjointness of the whole matrix allocation. -/
theorem row_disjoint (h : MatrixRep before base A) (i : Fin m)
    {other : Word w} {length : Nat}
    (hdisjoint : ArraysDisjoint base (m * n) other length) :
    ArraysDisjoint (arrayAddr base (i.val * n)) n other length := by
  unfold ArraysDisjoint at hdisjoint ⊢
  rw [h.row_base_toNat i]
  have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hrow
  omega

/-- Borrow a row as a standard list view, without a runtime allocation. -/
theorem row_array (h : MatrixRep before base A) (i : Fin m) :
    ArrayRep before (arrayAddr base (i.val * n)) (List.ofFn (A i)) := by
  apply ArrayRep.ofFn_iff_indexed.mpr
  refine ⟨?_, ?_⟩
  · rw [h.row_base_toNat i]
    have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hrow
    have hfit := h.fits
    omega
  · intro j
    simpa only [matrixAddr_row] using h.lookup i j

/-- The physical cells of a row are exactly its natural-address interval.
This converts an existing array frame into the indexed write-back frame. -/
theorem row_range (h : MatrixRep before base A) (i : Fin m) :
    Set.range (matrixAddr base i : Fin n → Word w) =
      {a : Word w | a.toNat ∈ Set.Ico
        (arrayAddr base (i.val * n)).toNat ((arrayAddr base (i.val * n)).toNat + n)} := by
  apply Set.ext
  intro address
  constructor
  · rintro ⟨j, rfl⟩
    change _ ≤ _ ∧ _ < _
    rw [h.addr_toNat i j, h.row_base_toNat i]
    have hj := j.isLt
    omega
  · intro ha
    change _ ≤ address.toNat ∧ address.toNat < _ at ha
    rw [h.row_base_toNat i] at ha
    let j : Fin n := ⟨address.toNat - (base.toNat + i.val * n), by omega⟩
    refine ⟨j, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [h.addr_toNat i j]
    dsimp [j]
    omega

/-- Any verified array operation on a row can return the parent matrix
directly as a mathlib row update; no other row needs a new proof. -/
theorem replace_row_array (h : MatrixRep before base A) (i : Fin m)
    {values : Fin n → Word w}
    (updated : ArrayRep after (arrayAddr base (i.val * n)) (List.ofFn values))
    (frame : ArrayFrame (arrayAddr base (i.val * n)) n before after) :
    MatrixRep after base (A.updateRow i values) := by
  apply h.replace_row i
  · intro j
    rw [matrixAddr_row]
    exact (ArrayRep.ofFn_iff_indexed.mp updated).2 j
  · rw [h.row_range i]
    exact frame.eqOn

/-- A verified array operation may update both the selected row and its
scratch buffer. Only the scratch interval must avoid the parent matrix;
the original two-buffer frame is used without claiming scratch is unchanged. -/
theorem replace_row_array_two (h : MatrixRep before base A) (i : Fin m)
    {values : Fin n → Word w} {scratch : Word w} {scratchLen : Nat}
    (updated : ArrayRep after (arrayAddr base (i.val * n)) (List.ofFn values))
    (frame : TwoBufferFrame (arrayAddr base (i.val * n)) n scratch scratchLen before after)
    (hdisjoint : ArraysDisjoint scratch scratchLen base (m * n)) :
    MatrixRep after base (A.updateRow i values) := by
  have joined := h.indexed.replace_on_union (after := after) (matrixAddr_injective h.fits)
    (changed := {p : Fin m × Fin n | p.1 = i})
    (new := fun p => values p.2)
    (auxiliary := {a : Word w | a.toNat ∈ Set.Ico scratch.toNat (scratch.toNat + scratchLen)})
    (by
      rintro ⟨r, c⟩ (rfl : r = i)
      change after (matrixAddr base r c) = values c
      simpa only [matrixAddr_row] using (ArrayRep.ofFn_iff_indexed.mp updated).2 c)
    (by
      intro address outside
      apply frame.eqOn
      rintro (hrow | hscratch)
      · have hin : address ∈ Set.range (matrixAddr base i : Fin n → Word w) := by
          rw [h.row_range i]
          exact hrow
        obtain ⟨j, rfl⟩ := hin
        exact outside (Or.inl ⟨(i, j), rfl, rfl⟩)
      · exact outside (Or.inr hscratch))
    (by
      apply Set.disjoint_left.mpr
      rintro address ⟨p, _, rfl⟩ hscratch
      exact Set.disjoint_left.mp (h.disjoint_interval hdisjoint) ⟨p, rfl⟩ hscratch)
  refine ⟨h.fits, ?_⟩
  intro p
  simpa only [Function.uncurry, Set.piecewise, Set.mem_setOf_eq,
    Matrix.updateRow_apply] using joined p

end MatrixRep

namespace Source.MatrixAt

variable {heapLimit : Nat} {base : Word w} {s t : State w}
  {A : Matrix (Fin m) (Fin n) (Word w)}

/-- Source-level borrowing retains the row's heap bound automatically. -/
theorem row_array (h : MatrixAt heapLimit base A s) (i : Fin m) :
    ArrayAt heapLimit (arrayAddr base (i.val * n)) (List.ofFn (A i)) s := by
  refine ⟨h.1.row_array i, ?_⟩
  rw [List.length_ofFn, h.1.row_base_toNat i]
  have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hrow
  have hheap := h.2
  omega

/-- The source heap bound belongs to the whole allocation and is retained
when an existing array operation changes one row. -/
theorem replace_row_array (h : MatrixAt heapLimit base A s) (i : Fin m)
    {values : Fin n → Word w}
    (updated : ArrayAt heapLimit (arrayAddr base (i.val * n)) (List.ofFn values) t)
    (frame : ArrayFrame (arrayAddr base (i.val * n)) n s.mem t.mem) :
    MatrixAt heapLimit base (A.updateRow i values) t :=
  ⟨h.1.replace_row_array i updated.1 frame, h.2⟩

/-- Recover the entire source matrix after a row operation with a separate
scratch buffer, without discarding the operation's two-buffer effect. -/
theorem replace_row_array_two (h : MatrixAt heapLimit base A s) (i : Fin m)
    {values : Fin n → Word w} {scratch : Word w} {scratchLen : Nat}
    (updated : ArrayAt heapLimit (arrayAddr base (i.val * n)) (List.ofFn values) t)
    (frame : TwoBufferFrame (arrayAddr base (i.val * n)) n scratch scratchLen s.mem t.mem)
    (hdisjoint : ArraysDisjoint scratch scratchLen base (m * n)) :
    MatrixAt heapLimit base (A.updateRow i values) t :=
  ⟨h.1.replace_row_array_two i updated.1 frame hdisjoint, h.2⟩

end Source.MatrixAt
end Ram
