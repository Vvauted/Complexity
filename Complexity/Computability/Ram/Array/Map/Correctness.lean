/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Map.Basic
import Complexity.Computability.Ram.Array.Traversal

/-!
# Correctness of in-place array mapping

The invariant describes a transformed prefix followed by the original unread
suffix. Each iteration loads the next original word, applies the actual helper
contract and stores its returned word in that position. Existing array-update
and frame rules retain the rest of the heap.

The general `TotalWP.forIn` rule supplies loop termination independently of any
instruction budget. Only original input elements require the helper contract.
Array bounds may include the end of the word-address space: the final cursor
is unused, and no strict endpoint assumption is added.
-/

namespace Ram.Source.Array.Map

open Ram.Source.ForIn

private def contents (transform : Word w → Word w) (xs : List (Word w))
    (i : Nat) : List (Word w) :=
  (xs.map transform).take i ++ xs.drop i

private theorem contents_length (transform : Word w → Word w) (xs : List (Word w))
    {i : Nat} (hi : i ≤ xs.length) : (contents transform xs i).length = xs.length := by
  simpa only [contents, List.length_map] using
    copy_prefix_length (xs.map transform) xs (by simp) (by simpa using hi)

private theorem contents_get_next (transform : Word w → Word w) (xs : List (Word w))
    {i : Nat} (hi : i < xs.length) :
    (contents transform xs i)[i]'(by rw [contents_length transform xs hi.le]; exact hi) =
      xs[i] := by
  have frontLength : ((xs.map transform).take i).length = i :=
    List.length_take_of_le (by simpa using hi.le)
  simp only [contents,
    List.getElem_append_right (by omega : ((xs.map transform).take i).length ≤ i),
    frontLength, Nat.sub_self, List.getElem_drop, Nat.add_zero]

private theorem contents_set_next (transform : Word w → Word w) (xs : List (Word w))
    {i : Nat} (hi : i < xs.length) :
    (contents transform xs i).set i (transform xs[i]) = contents transform xs (i + 1) := by
  have mappedIndex : i < (xs.map transform).length := by simpa only [List.length_map] using hi
  have mappedValue : (xs.map transform)[i]'mappedIndex = transform xs[i] := by
    rw [List.getElem_map]
  have updated := copy_prefix_step (xs.map transform) xs (by simp) mappedIndex
  rw [mappedValue] at updated
  exact updated

private theorem contents_finish (transform : Word w → Word w) (xs : List (Word w)) :
    contents transform xs xs.length = xs.map transform := by
  simpa only [contents, List.length_map] using
    copy_prefix_finish (xs.map transform) xs (by simp)

private structure Invariant (heapLimit : Nat) (base : Word w) (xs : List (Word w))
    (transform : Word w → Word w) (entry : State w) (i : Nat) (s : State w) : Prop where
  index_le : i ≤ xs.length
  base_eq : s.regs 0 = base
  index : s.regs 2 = BitVec.ofNat w i
  pointer : s.regs 3 = arrayAddr base i
  remaining : (s.regs 4).toNat = xs.length - i
  array : ArrayAt heapLimit base (contents transform xs i) s
  frame : ArrayFrame base xs.length entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

private theorem Invariant.index_lt {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s) (nonzero : s.regs 4 ≠ 0) :
    i < xs.length := by
  have positive : 0 < (s.regs 4).toNat :=
    Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
  rw [h.remaining] at positive
  omega

private theorem Invariant.address_lt {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s) (hi : i < xs.length) :
    (s.regs 3).toNat < heapLimit := by
  rw [h.pointer]
  exact h.array.addr_lt (by rw [contents_length transform xs h.index_le]; exact hi)

private theorem Invariant.read_next {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s) (hi : i < xs.length) :
    s.mem (s.regs 3) = xs[i] := by
  rw [h.pointer]
  exact (h.array.1.lookup i
    (by rw [contents_length transform xs h.index_le]; exact hi)).trans
      (contents_get_next transform xs hi)

private theorem Invariant.advance {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (hw : 0 < w) (h : Invariant heapLimit base xs transform entry i s)
    (hi : i < xs.length) :
    Invariant heapLimit base xs transform entry (i + 1)
      (advanceState 3 4 (bodyState transform (loadedState 3 5 s))) := by
  let next := advanceState 3 4 (bodyState transform (loadedState 3 5 s))
  let stored := s.setMem (arrayAddr base i) (transform xs[i])
  have loaded := h.read_next hi
  have indexFits : i < (contents transform xs i).length := by
    rw [contents_length transform xs h.index_le]
    exact hi
  have memory : next.mem = stored.mem := by
    simp [next, advanceState, bodyState, loadedState, State.setReg, State.setMem,
      stored, h.base_eq, h.index, loaded, arrayAddr]
  have updated : ArrayAt heapLimit base (contents transform xs (i + 1)) next := by
    have represented := h.array.setMem indexFits (transform xs[i])
    rw [contents_set_next transform xs hi] at represented
    change ArrayRep next.mem base _ ∧ _
    rw [memory]
    exact represented
  have frame : ArrayFrame base xs.length s.mem next.mem := by
    rw [memory]
    simpa only [contents_length transform xs h.index_le] using
      ArrayFrame.store h.array.1 indexFits (transform xs[i])
  have count : next.regs 4 = s.regs 4 - 1 := by
    simp [next, advanceState, bodyState, loadedState, State.setReg, State.setMem]
  have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have positive : 0 < (s.regs 4).toNat := by rw [h.remaining]; omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, updated, h.frame.trans frame, h.input, h.output⟩
  · simp [advanceState, bodyState, loadedState, State.setReg, State.setMem, h.base_eq]
  · simp [advanceState, bodyState, loadedState, State.setReg, State.setMem,
      h.index, BitVec.ofNat_add]
  · simp [advanceState, bodyState, loadedState, State.setReg, State.setMem,
      h.pointer, arrayAddr, BitVec.ofNat_add, BitVec.add_assoc]
  · change (next.regs 4).toNat = xs.length - (i + 1)
    rw [count]
    change (BinOp.eval .sub (s.regs 4) 1).toNat = xs.length - (i + 1)
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [one]; omega), one, h.remaining]
    omega

/-- The actual map loop safely transforms its represented array in place and
preserves memory outside that array and both streams. The helper is required
only on original input elements and independently of any instruction budget.
The final unused cursor may wrap at the array endpoint. -/
theorem code_total_contract {program : Program} {helper : Func} {fn heapLimit depth : Nat}
    {base : Word w} {xs : List (Word w)} {transform : Word w → Word w}
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (correct : ∀ x ∈ xs, FunctionContract program heapLimit depth helper
      (fun args _ => args = [x])
      (fun _ entry value finish => value = [transform x] ∧ finish = entry)) :
    TotalRelContract program heapLimit (depth + 1) (code fn)
      (fun entry => ArrayAt heapLimit base xs entry ∧ entry.regs 0 = base ∧
        (entry.regs 1).toNat = xs.length)
      (fun entry finish => ArrayAt heapLimit base (xs.map transform) finish ∧
        ArrayFrame base xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  rintro entry ⟨represented, base_eq, length_eq⟩
  change Verification.TotalWP program heapLimit (depth + 1) (code fn)
    (fun finish => ArrayAt heapLimit base (xs.map transform) finish ∧
      ArrayFrame base xs.length entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev) entry
  rw [code, Verification.TotalWP.seq_iff, Verification.TotalWP.assign_iff]
  refine ⟨trivial, ?_⟩
  apply Verification.TotalWP.forIn 3 4 5 hw (by decide) (by decide)
    (fun current => ∃ i, Invariant heapLimit base xs transform entry i current)
  · rintro current ⟨i, h⟩ nonzero
    exact h.address_lt (h.index_lt nonzero)
  · rintro current ⟨i, h⟩ nonzero
    have hi := h.index_lt nonzero
    have loaded : (loadedState 3 5 current).regs 5 = xs[i] := by
      simpa only [loadedState, State.setReg_same] using h.read_next hi
    have address :
        ((loadedState 3 5 current).regs 0 + (loadedState 3 5 current).regs 2).toNat <
          heapLimit := by
      have same : current.regs 0 + current.regs 2 = current.regs 3 := by
        rw [h.base_eq, h.index, h.pointer]
        rfl
      simpa [loadedState, State.setReg, same] using h.address_lt hi
    have helperCorrect := correct xs[i] (List.getElem_mem hi)
    have execution := body_safe_at lookup (loadedState 3 5 current)
      (by simpa only [loaded] using helperCorrect) address
    refine ⟨bodyState transform (loadedState 3 5 current), execution,
      ⟨i + 1, Invariant.advance hw h hi⟩, ?_⟩
    simp [bodyState, State.setReg, State.setMem]
  · trivial
  · trivial
  · refine ⟨0, ?_⟩
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ArrayFrame.refl _ _ _, rfl, rfl⟩
    · simpa [initialState, State.eval, Expr.eval, State.setReg] using base_eq
    · simp [initialState, State.eval, Expr.eval, State.setReg]
    · simp [initialState, State.eval, Expr.eval, State.setReg, base_eq, arrayAddr]
    · simpa [initialState, State.eval, Expr.eval, State.setReg] using length_eq
    · simpa [contents, initialState, State.eval, Expr.eval, State.setReg, ArrayAt]
        using represented
  · rintro finish ⟨i, h⟩ zero
    have count := h.remaining
    rw [zero] at count
    have last : i = xs.length := by
      have le := h.index_le
      change 0 = xs.length - i at count
      omega
    subst i
    exact ⟨by simpa only [contents_finish] using h.array, h.frame, h.input, h.output⟩

end Ram.Source.Array.Map
