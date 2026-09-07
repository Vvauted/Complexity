/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Insertion
import Ram.Array.Ordering
import Ram.Array.Range

/-!
# Binary search followed by in-place insertion

The same verified lower-bound and right-shift programs are sequenced without
any host-side computation. Register 6 holds the original prefix length, so it
can restore register 3 after binary search has narrowed its right endpoint.
The array has one allocated spare cell; initialization of that cell is not
required, and all array-external words are preserved.
-/

namespace Ram.Source.Array.BinaryInsertion

/-- Search consumes the right endpoint; its original value stays live in
register 6. Restoring it before the shift is an actual counted assignment. -/
def program : Stmt :=
  .seq (.assign 3 (.var 6))
    (.seq lowerBound (.seq (.assign 3 (.var 6)) Insertion.program))

theorem code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable program = 59 := rfl

theorem wellFormed {locals : Nat} (h : 7 ≤ locals) : program.WellFormed locals := by
  have h3 : 3 < locals := by omega
  have h6 : 6 < locals := by omega
  have h5 : 5 ≤ locals := by omega
  simp only [program, Stmt.WellFormed, Expr.Bounded]
  exact ⟨⟨h3, h6⟩, lowerBound_wellFormed h5, ⟨h3, h6⟩, Insertion.wellFormed h5⟩

/-- Both linked blocks use only ordinary expressions, branches and loops. -/
theorem callsValid (functions : Program) : Compiler.CallsValid functions program := by
  simp [program, lowerBound, lowerBoundLoop, lowerBoundBody,
    Insertion.program, Insertion.loop, Insertion.body, Compiler.CallsValid]

structure Pre (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (spare : Word w) (s : State w) : Prop where
  array : ArrayAt heapLimit base (xs ++ [spare]) s
  base_reg : s.regs 0 = base
  key_reg : s.regs 1 = key
  length_reg : (s.regs 6).toNat = xs.length

/-- The result is standard ordered insertion. The lower-bound index remains
available, while the caller's registers from 5 upward and I/O are retained. -/
structure Post (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (entry finish : State w) : Prop where
  array : ArrayAt heapLimit base (xs.orderedInsert unsignedLE key) finish
  frame : ArrayFrame base (xs.length + 1) entry.mem finish.mem
  base_reg : finish.regs 0 = base
  key_reg : finish.regs 1 = key
  other : ∀ r, 5 ≤ r → finish.regs r = entry.regs r
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  result : LowerBoundSpec xs key (finish.regs 2).toNat

/-- Compose the existing search and shift contracts. The uniform insertion
budget bounds the number of moved cells by the prefix length; search retains
its logarithmic bound. Neither program is unfolded into a new execution proof. -/
theorem contract {control heapLimit depth : Nat} {functions : Program}
    {base key spare : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise unsignedLE) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit base key xs spare) (Post heapLimit base key xs)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 21) := by
  intro entry hpre
  let prepared := entry.setReg 3 (entry.regs 6)
  have hprepare : LocalMeasuredExec control functions heapLimit depth
      (.assign 3 (.var 6)) 2 entry prepared := .assign trivial
  have hsearchPre : LowerBoundPre heapLimit base key xs prepared := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [List.take_append_of_le_length (Nat.le_refl xs.length), List.take_length]
        using (hpre.array.setReg 3 (entry.regs 6)).take xs.length
    · simpa only [prepared, State.setReg] using hpre.base_reg
    · simpa only [prepared, State.setReg] using hpre.key_reg
    · simpa only [prepared, State.setReg] using hpre.length_reg
  obtain ⟨searchSteps, searched, hsearch, hs, hsearchBound⟩ :=
    lowerBound_contract (control := control) (program := functions) (depth := depth)
      hw hsorted prepared hsearchPre
  let restored := searched.setReg 3 (searched.regs 6)
  have hrestore : LocalMeasuredExec control functions heapLimit depth
      (.assign 3 (.var 6)) 2 searched restored := .assign trivial
  have hmem : restored.mem = entry.mem := hs.mem
  have hlength : (restored.regs 3).toNat = xs.length := by
    simp only [restored, State.setReg]
    rw [hs.other 6 (by decide)]
    simpa only [prepared, State.setReg] using hpre.length_reg
  have hposition : (restored.regs 2).toNat = (searched.regs 2).toNat := by
    simp [restored, State.setReg]
  have hinsertPre : Insertion.Pre heapLimit base key (searched.regs 2).toNat
      xs spare restored := by
    refine ⟨hpre.array.of_mem_eq hmem, ?_, ?_, hposition, hlength⟩
    · simpa only [restored, State.setReg] using hs.base_reg
    · simpa only [restored, State.setReg] using hs.key_reg
  obtain ⟨insertSteps, finish, hinsert, hf, hinsertBound⟩ :=
    Insertion.contract (control := control) (functions := functions) (depth := depth)
      (by omega : 0 < w) hs.result.index_le restored hinsertPre
  have hresultReg : finish.regs 2 = searched.regs 2 := by
    simpa only [restored, State.setReg] using hf.registers 2 (by decide)
  have hinsertEq : xs.insertIdx (searched.regs 2).toNat key =
      xs.orderedInsert unsignedLE key :=
    (Insertion.insertIdx_eq_take_cons_drop xs key hs.result.index_le).trans
      hs.result.insert_eq_orderedInsert
  refine ⟨2 + (searchSteps + (2 + insertSteps)), finish,
    .seq hprepare (.seq hsearch (.seq hrestore hinsert)), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hinsertEq] using hf.array
    · simpa only [hmem] using hf.frame
    · simpa only [restored, State.setReg] using
        (hf.registers 0 (by decide)).trans hinsertPre.base_reg
    · simpa only [restored, State.setReg] using
        (hf.registers 1 (by decide)).trans hinsertPre.key_reg
    · intro r hr
      have hr4 : r ≠ 4 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hr)
      have hr3 : r ≠ 3 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hr)
      calc
        finish.regs r = restored.regs r := hf.registers r hr4
        _ = searched.regs r := by simp only [restored, State.setReg, if_neg hr3]
        _ = prepared.regs r := hs.other r hr
        _ = entry.regs r := by simp only [prepared, State.setReg, if_neg hr3]
    · exact hf.input.trans hs.input
    · exact hf.output.trans hs.output
    · simpa only [hresultReg] using hs.result
  · change searchSteps ≤ 25 * Nat.clog 2 (xs.length + 1) + 6 at hsearchBound
    change insertSteps ≤ 19 * (xs.length - (searched.regs 2).toNat) + 11 at hinsertBound
    change 2 + (searchSteps + (2 + insertSteps)) ≤
      25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 21
    have hshift : 19 * (xs.length - (searched.regs 2).toNat) ≤ 19 * xs.length :=
      Nat.mul_le_mul_left 19 (Nat.sub_le _ _)
    omega

end Ram.Source.Array.BinaryInsertion
