/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array
import Ram.Memory.Indexed
import Ram.Matrix.Update
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Mathlib matrices in row-major RAM memory

The mathematical model is the existing `Matrix (Fin m) (Fin n) (Word w)`.
`finProdFinEquiv` supplies the row-major layout, including zero dimensions;
the explicit fitting bound prevents modular addresses from aliasing. A real
single-word store is a single entry update expressed with mathlib's
`Matrix.updateRow` and `Function.update`, not a whole-row machine operation.

Rows, columns, transposes and submatrices are views of the same memory through
`IndexedRep`. In particular, transposing a view does not claim that RAM has
rearranged the cells or executed a constant-time matrix transpose.
-/

namespace Ram

/-- Row-major addressing uses mathlib's finite-product equivalence. -/
def matrixAddr (base : Word w) (i : Fin m) (j : Fin n) : Word w :=
  arrayAddr base (finProdFinEquiv (i, j)).val

theorem matrixAddr_eq (base : Word w) (i : Fin m) (j : Fin n) :
    matrixAddr base i j = arrayAddr base (i.val * n + j.val) := by
  change arrayAddr base (j.val + n * i.val) = arrayAddr base (i.val * n + j.val)
  rw [Nat.mul_comm n i.val, Nat.add_comm j.val]

/-- No division or nonempty-dimension premise is needed for a valid entry. -/
theorem matrixAddr_toNat {base : Word w}
    (hfit : base.toNat + m * n ≤ 2 ^ w) (i : Fin m) (j : Fin n) :
    (matrixAddr base i j).toNat = base.toNat + i.val * n + j.val := by
  have hi := (finProdFinEquiv (i, j)).isLt
  have h := arrayAddr_toNat (base := base)
    (i := (finProdFinEquiv (i, j)).val) (by omega)
  change (matrixAddr base i j).toNat = base.toNat + (j.val + n * i.val) at h
  rw [h, Nat.mul_comm n i.val, Nat.add_comm j.val, Nat.add_assoc]

/-- Distinct matrix entries have distinct physical addresses when the full
row-major interval fits in the word-address space. -/
theorem matrixAddr_injective {base : Word w}
    (hfit : base.toNat + m * n ≤ 2 ^ w) :
    Function.Injective (Function.uncurry (matrixAddr base : Fin m → Fin n → Word w)) := by
  intro x y h
  apply finProdFinEquiv.injective
  apply Fin.ext
  have hx := (finProdFinEquiv x).isLt
  have hy := (finProdFinEquiv y).isLt
  exact (arrayAddr_eq_iff (base := base) (i := (finProdFinEquiv x).val)
    (j := (finProdFinEquiv y).val) (by omega) (by omega)).mp h

/-- A pure observation of a rectangular interval, not a machine operation. -/
def matrixContents (mem : Word w → Word w) (base : Word w) (m n : Nat) :
    Matrix (Fin m) (Fin n) (Word w) :=
  Matrix.of fun i j => mem (matrixAddr base i j)

@[simp]
theorem matrixContents_apply (mem : Word w → Word w) (base : Word w)
    (i : Fin m) (j : Fin n) :
    matrixContents mem base m n i j = mem (matrixAddr base i j) := rfl

/-- A non-wrapping row-major representation of an ordinary mathlib matrix. -/
structure MatrixRep (mem : Word w → Word w) (base : Word w)
    (A : Matrix (Fin m) (Fin n) (Word w)) : Prop where
  fits : base.toNat + m * n ≤ 2 ^ w
  indexed : IndexedRep mem (Function.uncurry (matrixAddr base)) (Function.uncurry A)

namespace MatrixRep

variable {mem before after : Word w → Word w} {base : Word w}
  {A B : Matrix (Fin m) (Fin n) (Word w)}

theorem lookup (h : MatrixRep mem base A) (i : Fin m) (j : Fin n) :
    mem (matrixAddr base i j) = A i j := h.indexed (i, j)

theorem addr_toNat (h : MatrixRep mem base A) (i : Fin m) (j : Fin n) :
    (matrixAddr base i j).toNat = base.toNat + i.val * n + j.val :=
  matrixAddr_toNat h.fits i j

theorem contents_eq (h : MatrixRep mem base A) : matrixContents mem base m n = A := by
  funext i j
  exact h.lookup i j

theorem of_contents (mem : Word w → Word w) (base : Word w)
    (hfit : base.toNat + m * n ≤ 2 ^ w) :
    MatrixRep mem base (matrixContents mem base m n) := ⟨hfit, fun _ => rfl⟩

theorem iff_contents_eq : MatrixRep mem base A ↔
    base.toNat + m * n ≤ 2 ^ w ∧ matrixContents mem base m n = A :=
  ⟨fun h => ⟨h.fits, h.contents_eq⟩, fun ⟨hfit, h⟩ => h ▸ of_contents mem base hfit⟩

theorem eq (h : MatrixRep mem base A) (h' : MatrixRep mem base B) : A = B :=
  h.contents_eq.symm.trans h'.contents_eq

theorem predicate_iff (h : MatrixRep mem base A)
    (P : Matrix (Fin m) (Fin n) (Word w) → Prop) :
    P (matrixContents mem base m n) ↔ P A := by rw [h.contents_eq]

theorem congr_mem (h : MatrixRep before base A)
    (hmem : ∀ (i : Fin m) (j : Fin n),
      after (matrixAddr base i j) = before (matrixAddr base i j)) :
    MatrixRep after base A :=
  ⟨h.fits, h.indexed.congr_mem (fun p => hmem p.1 p.2)⟩

/-- A row is the existing finite function `A i`; no new vector type is needed. -/
theorem row (h : MatrixRep mem base A) (i : Fin m) :
    IndexedRep mem (matrixAddr base i) (A i) := fun j => h.lookup i j

/-- Columns use the standard mathematical transpose only as an indexed view. -/
theorem col (h : MatrixRep mem base A) (j : Fin n) :
    IndexedRep mem (fun i => matrixAddr base i j) (A.transpose j) :=
  fun i => h.lookup i j

/-- The transposed view preserves the physical layout; it is not a claim of
a row-major representation of a physically transposed matrix. -/
theorem transpose (h : MatrixRep mem base A) :
    IndexedRep mem (fun p : Fin n × Fin m => matrixAddr base p.2 p.1)
      (Function.uncurry A.transpose) := fun p => h.lookup p.2 p.1

/-- Existing mathlib submatrices also represent views, including repeated or
permuted indices. No injectivity is needed until an update is requested. -/
theorem submatrix {ι κ : Type*} (h : MatrixRep mem base A)
    (rows : ι → Fin m) (cols : κ → Fin n) :
    IndexedRep mem (fun p : ι × κ => matrixAddr base (rows p.1) (cols p.2))
      (Function.uncurry (A.submatrix rows cols)) := fun p => h.lookup (rows p.1) (cols p.2)

/-- One physical store changes one mathematical entry. Both update functions
are mathlib's existing APIs; no independent matrix semantics are introduced. -/
theorem store (h : MatrixRep mem base A) (i : Fin m) (j : Fin n) (value : Word w) :
    MatrixRep (fun a => if a = matrixAddr base i j then value else mem a) base
      (A.updateRow i (Function.update (A i) j value)) := by
  refine ⟨h.fits, ?_⟩
  change IndexedRep _ _
    (Function.uncurry (Function.update A i (Function.update (A i) j value)))
  rw [Function.uncurry_update_update]
  exact h.indexed.store (matrixAddr_injective h.fits) (i, j) value

/-- The same single entry update may be stated through the column API. -/
theorem store_col (h : MatrixRep mem base A) (i : Fin m) (j : Fin n) (value : Word w) :
    MatrixRep (fun a => if a = matrixAddr base i j then value else mem a) base
      (A.updateCol j (Function.update (fun r => A r j) i value)) := by
  simpa only [Matrix.updateCol_update] using h.store i j value

theorem setMem {s : State w} (h : MatrixRep s.mem base A)
    (i : Fin m) (j : Fin n) (value : Word w) :
    MatrixRep (s.setMem (matrixAddr base i j) value).mem base
      (A.updateRow i (Function.update (A i) j value)) := h.store i j value

theorem exec_store {s : State w} (h : MatrixRep s.mem base A)
    (i : Fin m) (j : Fin n) (addrReg src : Reg)
    (haddr : s.regs addrReg = matrixAddr base i j) :
    MatrixRep (execInstr (.store addrReg src) s).mem base
      (A.updateRow i (Function.update (A i) j (s.regs src))) := by
  simpa only [execInstr, State.next_mem, haddr] using h.setMem i j (s.regs src)

end MatrixRep

/-- A single physical store rewrites the observed matrix directly to a
mathlib entry update, so matrix properties can be proved by ordinary rewriting. -/
theorem matrixContents_store {mem : Word w → Word w} {base : Word w}
    (hfit : base.toNat + m * n ≤ 2 ^ w) (i : Fin m) (j : Fin n) (value : Word w) :
    matrixContents (fun a => if a = matrixAddr base i j then value else mem a) base m n =
      (matrixContents mem base m n).updateRow i
        (Function.update (matrixContents mem base m n i) j value) :=
  ((MatrixRep.of_contents mem base hfit).store i j value).contents_eq

namespace Source

/-- A row-major matrix whose complete interval lies in the source heap. -/
def MatrixAt (heapLimit : Nat) (base : Word w)
    (A : Matrix (Fin m) (Fin n) (Word w)) (s : State w) : Prop :=
  MatrixRep s.mem base A ∧ base.toNat + m * n ≤ heapLimit

namespace MatrixAt

variable {heapLimit : Nat} {base : Word w}
  {A : Matrix (Fin m) (Fin n) (Word w)} {s : State w}

theorem addr_lt (h : MatrixAt heapLimit base A s) (i : Fin m) (j : Fin n) :
    (matrixAddr base i j).toNat < heapLimit := by
  have hi := (finProdFinEquiv (i, j)).isLt
  have haddr := arrayAddr_toNat (base := base)
    (i := (finProdFinEquiv (i, j)).val) (by have hfit := h.1.fits; omega)
  change (arrayAddr base (finProdFinEquiv (i, j)).val).toNat < heapLimit
  rw [haddr]
  have hheap := h.2
  omega

/-- Matrix proofs can use all generic indexed read/store contracts and the
source-to-target observation bridge without unfolding the representation. -/
theorem indexed (h : MatrixAt heapLimit base A s) :
    IndexedAt heapLimit (Function.uncurry (matrixAddr base)) (Function.uncurry A) s :=
  ⟨h.1.indexed, fun p => h.addr_lt p.1 p.2⟩

theorem row (h : MatrixAt heapLimit base A s) (i : Fin m) :
    IndexedAt heapLimit (matrixAddr base i) (A i) s :=
  ⟨h.1.row i, fun j => h.addr_lt i j⟩

theorem col (h : MatrixAt heapLimit base A s) (j : Fin n) :
    IndexedAt heapLimit (fun i => matrixAddr base i j) (A.transpose j) s :=
  ⟨h.1.col j, fun i => h.addr_lt i j⟩

theorem transpose (h : MatrixAt heapLimit base A s) :
    IndexedAt heapLimit (fun p : Fin n × Fin m => matrixAddr base p.2 p.1)
      (Function.uncurry A.transpose) s :=
  ⟨h.1.transpose, fun p => h.addr_lt p.2 p.1⟩

theorem submatrix {ι κ : Type*} (h : MatrixAt heapLimit base A s)
    (rows : ι → Fin m) (cols : κ → Fin n) :
    IndexedAt heapLimit (fun p : ι × κ => matrixAddr base (rows p.1) (cols p.2))
      (Function.uncurry (A.submatrix rows cols)) s :=
  ⟨h.1.submatrix rows cols, fun p => h.addr_lt (rows p.1) (cols p.2)⟩

theorem contents_eq (h : MatrixAt heapLimit base A s) :
    matrixContents s.mem base m n = A := h.1.contents_eq

theorem setReg (h : MatrixAt heapLimit base A s) (dst : Reg) (value : Word w) :
    MatrixAt heapLimit base A (s.setReg dst value) := h

theorem setMem (h : MatrixAt heapLimit base A s)
    (i : Fin m) (j : Fin n) (value : Word w) :
    MatrixAt heapLimit base (A.updateRow i (Function.update (A i) j value))
      (s.setMem (matrixAddr base i j) value) := ⟨h.1.store i j value, h.2⟩

end MatrixAt

/-- The compiler's existing observation relation transfers the mathematical
matrix unchanged to the real target heap. -/
theorem State.Observes.matrix {heapLimit locals : Nat} {base : Word w}
    {A : Matrix (Fin m) (Fin n) (Word w)} {s : Source.State w} {t : Ram.State w}
    (ho : State.Observes heapLimit locals s t) (h : MatrixAt heapLimit base A s) :
    MatrixRep t.mem base A := ⟨h.1.fits, ho.indexed h.indexed⟩

end Source
end Ram
