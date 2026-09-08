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

The shared `TotalWP.forIn_indexed_of_frame` rule maintains private cursor/count progress
and supplies loop termination independently of any instruction budget. The
payload retains only the program's own bindings and mathematical heap effects.
Only original input elements require the helper contract.
Array bounds may include the end of the word-address space: the final cursor
is unused, and no strict endpoint assumption is added.
-/

namespace Ram.Source.Array.Map

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
  base_eq : s.regs 0 = base
  index : s.regs 2 = BitVec.ofNat w i
  array : ArrayAt heapLimit base (contents transform xs i) s
  frame : ArrayFrame base xs.length entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

private theorem Invariant.address_lt {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s) (hi : i < xs.length) :
    (arrayAddr base i).toNat < heapLimit := by
  exact h.array.addr_lt (by rw [contents_length transform xs hi.le]; exact hi)

private theorem Invariant.read_next {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s) (hi : i < xs.length) :
    s.mem (arrayAddr base i) = xs[i] := by
  exact (h.array.1.lookup i
    (by rw [contents_length transform xs hi.le]; exact hi)).trans
      (contents_get_next transform xs hi)

private theorem Invariant.of_localFrame {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s t : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s)
    (frame : State.LocalFrame {3, 4} s t) :
    Invariant heapLimit base xs transform entry i t := by
  refine ⟨(frame.reg_eq (by simp)).trans h.base_eq,
    (frame.reg_eq (by simp)).trans h.index, ?_, ?_,
    frame.input.trans h.input, frame.outputRev.trans h.output⟩
  · simpa only [ArrayAt, frame.mem] using h.array
  · simpa only [frame.mem] using h.frame

private theorem Invariant.body {heapLimit : Nat} {base : Word w}
    {xs : List (Word w)} {transform : Word w → Word w} {entry s : State w} {i : Nat}
    (h : Invariant heapLimit base xs transform entry i s)
    (hi : i < xs.length) :
    Invariant heapLimit base xs transform entry (i + 1)
      (bodyState transform (s.setReg 5 (s.mem (arrayAddr base i)))) := by
  let next := bodyState transform (s.setReg 5 (s.mem (arrayAddr base i)))
  let stored := s.setMem (arrayAddr base i) (transform xs[i])
  have loaded : s.mem (base + BitVec.ofNat w i) = xs[i] := h.read_next hi
  have indexFits : i < (contents transform xs i).length := by
    rw [contents_length transform xs hi.le]
    exact hi
  have memory : next.mem = stored.mem := by
    simp [next, bodyState, State.setReg, State.setMem,
      stored, h.base_eq, h.index, loaded, arrayAddr]
  have updated : ArrayAt heapLimit base (contents transform xs (i + 1)) next := by
    have represented := h.array.setMem indexFits (transform xs[i])
    rw [contents_set_next transform xs hi] at represented
    change ArrayRep next.mem base _ ∧ _
    rw [memory]
    exact represented
  have frame : ArrayFrame base xs.length s.mem next.mem := by
    rw [memory]
    simpa only [contents_length transform xs hi.le] using
      ArrayFrame.store h.array.1 indexFits (transform xs[i])
  refine ⟨?_, ?_, updated, h.frame.trans frame, h.input, h.output⟩
  · simp [bodyState, State.setReg, State.setMem, h.base_eq]
  · simp [bodyState, State.setReg, State.setMem,
      h.index, BitVec.ofNat_add]

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
  apply Verification.TotalWP.forIn_indexed_of_frame 3 4 5 base xs.length hw
    (by decide) (by decide) (by decide) (Invariant heapLimit base xs transform entry)
  · intro i current next frame h
    exact h.of_localFrame frame
  · intro i current hi h
    exact h.address_lt hi
  · intro current finish execution
    exact ⟨execution.regs_eq_of_not_mem_writtenRegs (by simp [body, Stmt.writtenRegs]),
      body_remaining execution⟩
  · intro i current hi h
    let loadedState := current.setReg 5 (current.mem (arrayAddr base i))
    have loaded : loadedState.regs 5 = xs[i] := by
      simpa only [loadedState, State.setReg_same] using h.read_next hi
    have address :
        (loadedState.regs 0 + loadedState.regs 2).toNat < heapLimit := by
      simpa [loadedState, State.setReg, h.base_eq, h.index, arrayAddr] using h.address_lt hi
    have helperCorrect := correct xs[i] (List.getElem_mem hi)
    have execution := body_safe_at lookup loadedState
      (by simpa only [loaded] using helperCorrect) address
    exact ⟨bodyState transform loadedState, execution, h.body hi⟩
  · trivial
  · trivial
  · simpa [State.eval, Expr.eval, State.setReg] using base_eq
  · simpa [State.eval, Expr.eval, State.setReg] using length_eq
  · refine ⟨?_, ?_, ?_, ArrayFrame.refl _ _ _, rfl, rfl⟩
    · simpa [State.setReg] using base_eq
    · simp [State.setReg]
    · simpa [contents, State.setReg, ArrayAt]
        using represented
  · intro finish h
    exact ⟨by simpa only [contents_finish] using h.array, h.frame, h.input, h.output⟩

end Ram.Source.Array.Map
