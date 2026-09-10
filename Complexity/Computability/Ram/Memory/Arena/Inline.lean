/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Arena.Registers.Allocation

/-!
# Inline arena allocation at five fresh slots

The compiler places the requested length at `next + 1` and initial word at
`next + 2` before this block. The block reads the shared cursor, reserves and
initializes the region, then leaves the descriptor at `next` and `next + 1`.
It uses the standalone allocator's same implementation and generic proof;
there is no added function index, call, or program-specific proof obligation.
-/

namespace Ram.Source.Arena.Inline

/-- The shared allocator specialized to consecutive fresh local slots. -/
def allocate (next : Reg) : Stmt := (inlineRegisters next).allocate

/-- The actual syntax needs exactly the five selected slots. -/
theorem allocate_regBound (next : Reg) : (allocate next).regBound = next + 5 := by
  simp only [allocate, inlineRegisters, Registers.allocate, Registers.prepare,
    Registers.fill, Registers.fillBody, Stmt.regBound, Expr.varBound]
  simp only [Reg] at *
  omega

theorem allocate_wellFormed (next : Reg) {locals : Nat} (bound : next + 5 ≤ locals) :
    (allocate next).WellFormed locals := by
  apply Stmt.wellFormed_of_regBound_le
  rwa [allocate_regBound]

theorem allocate_writtenRegs (next : Reg) :
    (allocate next).writtenRegs = {next, next + 3, next + 4} :=
  (inlineRegisters next).allocate_writtenRegs

theorem allocate_callsValid (next : Reg) (program : Program) :
    Compiler.CallsValid program (allocate next) :=
  (inlineRegisters next).allocate_callsValid program

/-- Static code length, not the number of instructions executed by the loop. -/
theorem allocate_code_size (next control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (allocate next) = 26 := rfl

/-- Successful execution preserves every register below the fresh interval. -/
theorem allocate_preserves_below (next : Reg) {program : Program}
    {heapLimit depth : Nat} {s t : State w}
    (execution : SafeExec program heapLimit depth (allocate next) s t)
    {slot : Reg} (below : slot < next) : t.regs slot = s.regs slot := by
  apply execution.regs_eq_of_not_mem_writtenRegs
  rw [allocate_writtenRegs]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨Nat.ne_of_lt below,
    Nat.ne_of_lt (Nat.lt_of_lt_of_le below (Nat.le_add_right next 3)),
    Nat.ne_of_lt (Nat.lt_of_lt_of_le below (Nat.le_add_right next 4))⟩

/-- Capacity and input-word requirements at the two preloaded operand slots. -/
abbrev Pre (next : Reg) (heapLimit : Nat) (base : Word w) (length : Nat) (value : Word w)
    (entry : State w) : Prop :=
  (inlineRegisters next).Pre heapLimit base length value entry

/-- Initialized contents, returned descriptor, shared cursor and precise frames. -/
abbrev Post (next : Reg) (heapLimit : Nat) (base : Word w) (length : Nat) (value : Word w)
    (entry finish : State w) : Prop :=
  (inlineRegisters next).Post heapLimit base length value entry finish

/-- The same initialized-prefix proof counts actual emitted instructions,
including the fixed work when the requested length is zero. -/
theorem allocate_measured (next : Reg) {program : Program}
    {control heapLimit depth length : Nat} {base value : Word w} {entry : State w}
    (pre : Pre next heapLimit base length value entry) :
    ∃ finish, LocalMeasuredExec control program heapLimit depth (allocate next)
      (14 * length + 14) entry finish ∧ Post next heapLimit base length value entry finish :=
  (inlineRegisters next).allocate_measured pre

/-- Inline allocation terminates without requiring a proposed time budget. -/
theorem allocate_total (next : Reg) {program : Program} {heapLimit depth length : Nat}
    {base value : Word w} :
    TotalRelContract program heapLimit depth (allocate next)
      (Pre next heapLimit base length value) (Post next heapLimit base length value) :=
  (inlineRegisters next).allocate_total

end Ram.Source.Arena.Inline
