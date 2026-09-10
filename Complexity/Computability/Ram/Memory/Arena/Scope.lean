/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic
import Complexity.Computability.Ram.Source.Bounds
import Complexity.Computability.Ram.Source.Frame
import Complexity.Computability.Ram.Source.State.Frame

/-!
# Saving and restoring an arena cursor

`capture` loads the shared cursor at address zero into one caller-local register.
`release` stores that saved word back to address zero. Each block has three
actual compiler instructions and uses the backend's existing expression scratch
registers; only the checkpoint needs a source-local slot.

Release does not clear data, undo stores, or restore the entry heap. Its endpoint
retains every non-metadata cell, local register and stream from immediately before
release. The surrounding compiler supplies a fresh checkpoint register and proves
that the scope body preserves it. Object lifetimes, non-escape and the represented
heap after release are separate obligations, not premises invented by this primitive.
-/

namespace Ram.Source.Arena.Scope

/-- Save the actual shared cursor in the selected caller-local register. -/
def capture (mark : Reg) : Stmt := .assign mark (.load (.const 0))

/-- Restore metadata from the saved word, leaving all data cells untouched. -/
def release (mark : Reg) : Stmt := .store (.const 0) (.var mark)

/-- Constant-address load followed by the assignment to the checkpoint. -/
theorem capture_stmtSize (mark control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (capture mark) = 3 := rfl

/-- The constant address, saved word and store have their actual compiler count. -/
theorem release_stmtSize (mark control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (release mark) = 3 := rfl

theorem capture_regBound (mark : Reg) : (capture mark).regBound = mark + 1 := by
  simp [capture, Stmt.regBound, Expr.varBound]

theorem release_regBound (mark : Reg) : (release mark).regBound = mark + 1 := by
  simp [release, Stmt.regBound, Expr.varBound]

/-- Capture needs only the single fresh source-local checkpoint. -/
theorem capture_wellFormed (mark : Reg) {locals : Nat} (bound : mark + 1 ≤ locals) :
    (capture mark).WellFormed locals := by
  apply Stmt.wellFormed_of_regBound_le
  rwa [capture_regBound]

/-- Release reuses the checkpoint without allocating another source local. -/
theorem release_wellFormed (mark : Reg) {locals : Nat} (bound : mark + 1 ≤ locals) :
    (release mark).WellFormed locals := by
  apply Stmt.wellFormed_of_regBound_le
  rwa [release_regBound]

theorem capture_writtenRegs (mark : Reg) : (capture mark).writtenRegs = {mark} := rfl

theorem release_writtenRegs (mark : Reg) : (release mark).writtenRegs = ∅ := rfl

theorem capture_callsValid (mark : Reg) (program : Program) :
    Compiler.CallsValid program (capture mark) := trivial

theorem release_callsValid (mark : Reg) (program : Program) :
    Compiler.CallsValid program (release mark) := trivial

/-- Capture executes safely when metadata address zero lies below the heap bound.
The saved word is the actual cursor; no value conversion or arena premise is used. -/
theorem capture_measured (mark : Reg) {w control heapLimit depth : Nat} {program : Program}
    (entry : State w) (positive : 0 < heapLimit) :
    LocalMeasuredExec control program heapLimit depth (capture mark) 3 entry
      (entry.setReg mark (entry.mem 0)) := by
  simpa only [capture, State.eval, Expr.eval] using
    (LocalMeasuredExec.assign (control := control) (program := program)
      (d := depth) (s := entry) (dst := mark) (value := .load (.const 0))
      ⟨trivial, by simpa only [Expr.eval, BitVec.toNat_ofNat, Nat.zero_mod] using positive⟩)

/-- Release stores exactly the saved word. Positivity permits this metadata store;
validity of a cursor value and safety of reclaiming its region belong to the caller. -/
theorem release_measured (mark : Reg) {w control heapLimit depth : Nat} {program : Program}
    (entry : State w) (positive : 0 < heapLimit) :
    LocalMeasuredExec control program heapLimit depth (release mark) 3 entry
      (entry.setMem 0 (entry.regs mark)) := by
  simpa only [release, State.eval, Expr.eval] using
    (LocalMeasuredExec.store (control := control) (program := program)
      (d := depth) (s := entry) (address := .const 0) (value := .var mark)
      trivial trivial (by simpa only [State.eval, Expr.eval, BitVec.toNat_ofNat,
        Nat.zero_mod] using positive))

/-- The actual saved cursor and the existing local-frame predicate describe
every capture execution, including every untouched local and shared component. -/
theorem capture_spec (mark : Reg) {w : Nat} {program : Program} {entry finish : State w}
    (execution : Exec program (capture mark) entry finish) :
    finish.regs mark = entry.mem 0 ∧ State.LocalFrame {mark} entry finish := by
  cases execution with
  | assign =>
      exact ⟨State.setReg_same _ _ _, State.LocalFrame.setReg _ _ _⟩

/-- Release changes metadata alone. Data cells retain their current contents,
not those from checkpoint entry, and every local and stream is unchanged. -/
theorem release_spec (mark : Reg) {w : Nat} {program : Program} {entry finish : State w}
    (execution : Exec program (release mark) entry finish) :
    finish.mem 0 = entry.regs mark ∧ Set.EqOn finish.mem entry.mem ({0}ᶜ) ∧
      finish.regs = entry.regs ∧ finish.input = entry.input ∧
      finish.outputRev = entry.outputRev := by
  cases execution with
  | store =>
      refine ⟨State.setMem_same _ _ _, ?_, rfl, rfl, rfl⟩
      intro address outside
      exact State.setMem_ne _ _ address _ (by simpa using outside)

end Ram.Source.Arena.Scope
