/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Frame
import Ram.Matrix.Memory

/-!
# Retaining matrix models across existing array effects

Matrices use the same generic `Set.EqOn` frame rule as indexed functions.
Existing array and two-buffer contracts therefore preserve a disjoint matrix
without unfolding the callee or proving its unchanged entries again. The
machine's no-wrap and source-heap bounds remain in `MatrixRep` and `MatrixAt`.
-/

namespace Ram

namespace MatrixRep

variable {before after : Word w → Word w} {base : Word w}
  {A : Matrix (Fin m) (Fin n) (Word w)}

theorem congr_eqOn (h : MatrixRep before base A)
    (hmem : Set.EqOn after before
      (Set.range (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w)))) :
    MatrixRep after base A := ⟨h.fits, h.indexed.congr_eqOn hmem⟩

/-- Any proved effect disjoint from the matrix's observed cells retains it. -/
theorem frame {writes : Set (Word w)} (h : MatrixRep before base A)
    (hframe : Set.EqOn after before writesᶜ)
    (hdisjoint : Disjoint
      (Set.range (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w))) writes) :
    MatrixRep after base A := ⟨h.fits, h.indexed.frame hframe hdisjoint⟩

/-- Every represented entry lies in the ordinary half-open matrix interval. -/
theorem addr_mem_Ico (h : MatrixRep before base A) (i : Fin m) (j : Fin n) :
    (matrixAddr base i j).toNat ∈ Set.Ico base.toNat (base.toNat + m * n) := by
  have hi := (finProdFinEquiv (i, j)).isLt
  change j.val + n * i.val < m * n at hi
  rw [Nat.mul_comm n i.val] at hi
  change base.toNat ≤ (matrixAddr base i j).toNat ∧
    (matrixAddr base i j).toNat < base.toNat + m * n
  rw [h.addr_toNat i j]
  omega

/-- The existing interval-disjointness condition supplies the generic set
disjointness needed by frame rules, including rectangular or empty matrices. -/
theorem disjoint_interval {other : Word w} {length : Nat}
    (h : MatrixRep before base A) (hdisjoint : ArraysDisjoint other length base (m * n)) :
    Disjoint (Set.range (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w)))
      {a : Word w | a.toNat ∈ Set.Ico other.toNat (other.toNat + length)} := by
  apply Set.disjoint_left.mpr
  rintro address ⟨⟨i, j⟩, rfl⟩ hmem
  have hmatrix := h.addr_mem_Ico i j
  change other.toNat ≤ (matrixAddr base i j).toNat ∧
    (matrixAddr base i j).toNat < other.toNat + length at hmem
  change base.toNat ≤ (matrixAddr base i j).toNat ∧
    (matrixAddr base i j).toNat < base.toNat + m * n at hmatrix
  unfold ArraysDisjoint at hdisjoint
  omega

end MatrixRep

/-- A pre-existing array contract's frame preserves a disjoint matrix model. -/
theorem ArrayFrame.preserves_matrix {before after : Word w → Word w}
    {base other : Word w} {length : Nat} {A : Matrix (Fin m) (Fin n) (Word w)}
    (h : ArrayFrame base length before after)
    (hdisjoint : ArraysDisjoint base length other (m * n))
    (matrix : MatrixRep before other A) : MatrixRep after other A :=
  matrix.frame h.eqOn (matrix.disjoint_interval hdisjoint)

/-- Matrix preservation also consumes the existing two-buffer frame, with
one ordinary interval-disjointness fact for each writable buffer. -/
theorem TwoBufferFrame.preserves_matrix {before after : Word w → Word w}
    {first second other : Word w} {firstLen secondLen : Nat}
    {A : Matrix (Fin m) (Fin n) (Word w)}
    (h : TwoBufferFrame first firstLen second secondLen before after)
    (hfirst : ArraysDisjoint first firstLen other (m * n))
    (hsecond : ArraysDisjoint second secondLen other (m * n))
    (matrix : MatrixRep before other A) : MatrixRep after other A :=
  matrix.frame h.eqOn (Set.disjoint_union_right.mpr
    ⟨matrix.disjoint_interval hfirst, matrix.disjoint_interval hsecond⟩)

namespace Source.MatrixAt

variable {heapLimit : Nat} {base : Word w} {A : Matrix (Fin m) (Fin n) (Word w)}
  {s t : State w}

theorem congr_eqOn (h : MatrixAt heapLimit base A s)
    (hmem : Set.EqOn t.mem s.mem
      (Set.range (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w)))) :
    MatrixAt heapLimit base A t := ⟨h.1.congr_eqOn hmem, h.2⟩

theorem frame {writes : Set (Word w)} (h : MatrixAt heapLimit base A s)
    (hframe : Set.EqOn t.mem s.mem writesᶜ)
    (hdisjoint : Disjoint
      (Set.range (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w))) writes) :
    MatrixAt heapLimit base A t := ⟨h.1.frame hframe hdisjoint, h.2⟩

/-- Preserve both the mathematical matrix and its source-heap bound after
an existing array or array-slice operation. -/
theorem frame_array {other : Word w} {length : Nat} (h : MatrixAt heapLimit base A s)
    (hframe : ArrayFrame other length s.mem t.mem)
    (hdisjoint : ArraysDisjoint other length base (m * n)) : MatrixAt heapLimit base A t :=
  ⟨hframe.preserves_matrix hdisjoint h.1, h.2⟩

theorem frame_two {first second : Word w} {firstLen secondLen : Nat}
    (h : MatrixAt heapLimit base A s)
    (hframe : TwoBufferFrame first firstLen second secondLen s.mem t.mem)
    (hfirst : ArraysDisjoint first firstLen base (m * n))
    (hsecond : ArraysDisjoint second secondLen base (m * n)) : MatrixAt heapLimit base A t :=
  ⟨hframe.preserves_matrix hfirst hsecond h.1, h.2⟩

end Source.MatrixAt
end Ram
