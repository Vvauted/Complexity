/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Slice

/-!
# Two-word references to represented arrays

`Ram.ArrayRef` contains an existing array's base address and word-sized length.
It is passed by value as two ordinary function parameters, not allocated as a
stored descriptor. `ArrayRef.Rep` uses the existing `Source.ArrayAt` assertion
and an exact length equation; the mathematical list is never runtime payload.

A borrowed subarray uses the existing list `drop`/`take` representation theorem.
Forming metadata in Lean is not an executed RAM conversion. When a source
program computes its arguments, their actual expressions are evaluated and
charged by the existing call compiler. Operation-specific endpoint and
overflow assumptions remain in the operation contracts.
-/

namespace Ram

/-- A by-value base address and length. No ownership or allocation is implicit. -/
structure ArrayRef (w : Nat) where
  base : Word w
  length : Word w
  deriving DecidableEq, Repr

namespace ArrayRef

/-- The existing word-parameter ABI representation of one array argument. -/
def args (array : ArrayRef w) : List (Word w) := [array.base, array.length]

@[simp] theorem length_args (array : ArrayRef w) : array.args.length = 2 := rfl

/-- Exact logical contents of a reference in an existing source heap. -/
def Rep (array : ArrayRef w) (heapLimit : Nat) (xs : List (Word w))
    (s : Source.State w) : Prop :=
  array.length.toNat = xs.length ∧ Source.ArrayAt heapLimit array.base xs s

/-- Binding a scalar result does not change an existing array's representation. -/
@[simp] theorem rep_setReg (array : ArrayRef w) (heapLimit : Nat) (xs : List (Word w))
    (s : Source.State w) (dst : Reg) (value : Word w) :
    array.Rep heapLimit xs (s.setReg dst value) ↔ array.Rep heapLimit xs s := Iff.rfl

/-- Function parameter binding leaves the represented heap unchanged. -/
@[simp] theorem rep_enter (array : ArrayRef w) (heapLimit : Nat) (xs : List (Word w))
    (s : Source.State w) (values : List (Word w)) :
    array.Rep heapLimit xs (s.enter values) ↔ array.Rep heapLimit xs s := Iff.rfl

/-- Metadata for a borrowed subarray. This definition moves no heap contents
and is not itself an implementation of in-program pointer arithmetic. -/
def subslice (array : ArrayRef w) (offset length : Word w) : ArrayRef w :=
  ⟨array.base + offset, length⟩

namespace Rep

variable {array : ArrayRef w} {heapLimit : Nat} {xs : List (Word w)} {s : Source.State w}

/-- A represented reference's length is already exactly word-representable. -/
theorem length_lt (h : array.Rep heapLimit xs s) : xs.length < 2 ^ w := by
  rw [← h.1]
  exact array.length.isLt

/-- Recover the literal length encoding used by word-level contracts. -/
theorem length_eq (h : array.Rep heapLimit xs s) :
    array.length = BitVec.ofNat w xs.length := by
  rw [← h.1]
  exact (Word.ofNat_toNat_self array.length).symm

/-- The descriptor carries the same arguments as the existing pointer/length ABI. -/
theorem args_eq (h : array.Rep heapLimit xs s) :
    array.args = [array.base, BitVec.ofNat w xs.length] := by
  rw [args, h.length_eq]

theorem setReg (h : array.Rep heapLimit xs s) (dst : Reg) (value : Word w) :
    array.Rep heapLimit xs (s.setReg dst value) :=
  ⟨h.1, h.2.setReg dst value⟩

theorem enter (h : array.Rep heapLimit xs s) (values : List (Word w)) :
    array.Rep heapLimit xs (s.enter values) := h

/-- A contained subarray is represented by the ordinary list slice, without
an allocation, a copy or another cell-by-cell representation proof. -/
theorem subslice (h : array.Rep heapLimit xs s) (offset length : Word w)
    (span : offset.toNat + length.toNat ≤ array.length.toNat) :
    (array.subslice offset length).Rep heapLimit
      ((xs.drop offset.toNat).take length.toNat) s := by
  have contained : offset.toNat + length.toNat ≤ xs.length := by
    simpa only [h.1] using span
  have exactLength : ((xs.drop offset.toNat).take length.toNat).length = length.toNat := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  refine ⟨exactLength.symm, ?_⟩
  simpa [ArrayRef.subslice, arrayAddr] using
    h.2.slice (offset := offset.toNat) (by omega) length.toNat

end Rep

/-- Build a reference assertion from an existing represented list and an
in-range runtime length; no data is loaded by this proof. -/
theorem rep_mk_iff {base : Word w} {xs : List (Word w)}
    {heapLimit : Nat} {s : Source.State w} (length : xs.length < 2 ^ w) :
    (⟨base, BitVec.ofNat w xs.length⟩ : ArrayRef w).Rep heapLimit xs s ↔
      Source.ArrayAt heapLimit base xs s := by
  simp [Rep, Word.ofNat_toNat_of_lt length]

end ArrayRef
end Ram
