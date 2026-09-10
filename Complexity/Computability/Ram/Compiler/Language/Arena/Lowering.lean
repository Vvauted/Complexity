/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Source.Effects

/-!
# Inline lowering of initialized allocation

Two actual assignments materialize the length and initial cell, followed by the
shared allocator implementation. The first two fresh slots hold the returned
descriptor; three further slots are private initialization scratch. No function
is appended to the program table, and existing call indices remain unchanged.

These are the local lowering and static frame facts. Successful initialization,
finite capacity and elapsed instruction counts require the allocation execution
theorems; the static code length is not its running time.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {kind : CellTy}

/-- Allocation introduces no call and therefore no extra function-table entry. -/
theorem lowerAlloc_callsValid (program : Ram.Program) (layout : RegisterMap Γ)
    (next : Reg) (length : Atom Γ .nat) (initial : Atom Γ kind.toTy) :
    Compiler.CallsValid program (lowerAlloc layout next length initial) :=
  ⟨trivial, trivial, (Source.Arena.inlineRegisters next).allocate_callsValid program⟩

/-- The two operands, reservation and one copy of the loop body emit thirty
instructions. Repeated execution of that loop is counted separately. -/
theorem lowerAlloc_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (next : Reg)
    (length : Atom Γ .nat) (initial : Atom Γ kind.toTy) :
    LocalCompiler.stmtSize control localsTable (lowerAlloc layout next length initial) = 30 := by
  simp only [lowerAlloc, Source.Arena.Registers.allocate, Source.Arena.Registers.fill,
    LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
    atomExpr_compile_length, Source.Arena.Registers.prepare_code_size,
    LocalCompiler.stmtSize_while, Source.Arena.Registers.fillBody_code_size,
    Expr.compile, List.length_singleton]

/-- Five fresh slots suffice for every local operand of inline allocation. -/
theorem lowerAlloc_wellFormed (layout : RegisterMap Γ) (next : Reg)
    (length : Atom Γ .nat) (initial : Atom Γ kind.toTy)
    (bounded : layout.Bounded next) :
    (lowerAlloc layout next length initial).WellFormed (next + 5) := by
  refine ⟨⟨Nat.add_lt_add_left (by decide : 1 < 5) next,
      (atomExpr_bounded layout length .nat bounded).mono (Nat.le_add_right next 5)⟩,
    ⟨Nat.add_lt_add_left (by decide : 2 < 5) next,
      (atomExpr_bounded layout initial (Scalar.cell kind) bounded).mono
        (Nat.le_add_right next 5)⟩,
    ?_⟩
  simp [Source.Arena.inlineRegisters, Source.Arena.Registers.allocate,
    Source.Arena.Registers.prepare, Source.Arena.Registers.fill,
    Source.Arena.Registers.fillBody, Ram.Stmt.WellFormed, Expr.Bounded]

/-- Every written local belongs to the five allocated slots, including the
two operand assignments. Shared-memory writes are intentionally not excluded. -/
theorem lowerAlloc_mem_writtenRegs (layout : RegisterMap Γ) (next : Reg)
    (length : Atom Γ .nat) (initial : Atom Γ kind.toTy) (slot : Reg) :
    slot ∈ (lowerAlloc layout next length initial).writtenRegs ↔
      next ≤ slot ∧ slot < next + 5 := by
  simp only [Reg] at *
  simp only [lowerAlloc, Ram.Stmt.writtenRegs, Source.Arena.Registers.allocate_writtenRegs,
    Source.Arena.inlineRegisters, Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  omega

/-- Inline allocation preserves every live caller-local field. This follows
from the existing execution frame theorem, independently of allocation costs. -/
theorem lowerAlloc_regs_eq {program : Ram.Program} {heapLimit depth : Nat}
    {layout : RegisterMap Γ} {next : Reg} {length : Atom Γ .nat}
    {initial : Atom Γ kind.toTy} {entry finish : Source.State w}
    (execution : Source.SafeExec program heapLimit depth
      (lowerAlloc layout next length initial) entry finish)
    {slot : Reg} (outside : slot < next ∨ next + 5 ≤ slot) :
    finish.regs slot = entry.regs slot := by
  apply execution.regs_eq_of_not_mem_writtenRegs
  rw [lowerAlloc_mem_writtenRegs]
  rintro ⟨lower, upper⟩
  rcases outside with below | above
  · exact Nat.not_lt_of_ge lower below
  · exact Nat.not_lt_of_ge above upper

/-- Initialization changes memory but consumes no input and emits no output. -/
theorem lowerAlloc_noIOWrites (layout : RegisterMap Γ) (next : Reg)
    (length : Atom Γ .nat) (initial : Atom Γ kind.toTy) :
    (lowerAlloc layout next length initial).NoIOWrites := by
  simp [lowerAlloc, Source.Arena.Registers.allocate, Source.Arena.Registers.prepare,
    Source.Arena.Registers.fill, Source.Arena.Registers.fillBody, Ram.Stmt.NoIOWrites]

end Ram.LanguageCompiler
