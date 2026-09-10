/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Basic
import Complexity.Computability.Ram.Source.Frame
import Complexity.Computability.Ram.Source.Bounds
import Complexity.Computability.Ram.Source.StraightLine

/-!
# The five registers used by arena allocation

This configuration describes the allocator's existing operands, not a general
register-renaming framework. Both the standalone function and inline lowering
use this same load/reserve/fill program. Layout never changes instruction costs.
-/

namespace Ram.Source.Arena

/-- Two input words, a returned base, and the two initialization-loop locals. -/
structure Registers where
  base : Reg
  length : Reg
  value : Reg
  pointer : Reg
  remaining : Reg
  distinct : [base, length, value, pointer, remaining].Nodup

namespace Registers

private theorem distinct_pairs (r : Registers) :
    (r.base ≠ r.length ∧ r.base ≠ r.value ∧ r.base ≠ r.pointer ∧ r.base ≠ r.remaining) ∧
    (r.length ≠ r.value ∧ r.length ≠ r.pointer ∧ r.length ≠ r.remaining) ∧
    (r.value ≠ r.pointer ∧ r.value ≠ r.remaining) ∧ r.pointer ≠ r.remaining := by
  simpa only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_or, and_true, not_false_eq_true, List.nodup_nil] using r.distinct

theorem base_ne_length (r : Registers) : r.base ≠ r.length := r.distinct_pairs.1.1
theorem base_ne_value (r : Registers) : r.base ≠ r.value := r.distinct_pairs.1.2.1
theorem base_ne_pointer (r : Registers) : r.base ≠ r.pointer := r.distinct_pairs.1.2.2.1
theorem base_ne_remaining (r : Registers) : r.base ≠ r.remaining := r.distinct_pairs.1.2.2.2
theorem length_ne_value (r : Registers) : r.length ≠ r.value := r.distinct_pairs.2.1.1
theorem length_ne_pointer (r : Registers) : r.length ≠ r.pointer := r.distinct_pairs.2.1.2.1
theorem length_ne_remaining (r : Registers) : r.length ≠ r.remaining := r.distinct_pairs.2.1.2.2
theorem value_ne_pointer (r : Registers) : r.value ≠ r.pointer := r.distinct_pairs.2.2.1.1
theorem value_ne_remaining (r : Registers) : r.value ≠ r.remaining := r.distinct_pairs.2.2.1.2
theorem pointer_ne_remaining (r : Registers) : r.pointer ≠ r.remaining := r.distinct_pairs.2.2.2

/-- The standalone function's existing parameter and result layout. -/
def legacy : Registers := ⟨2, 0, 1, 3, 4, by decide⟩

/-- Reserve the interval before any initialization store is executed. -/
def prepare (r : Registers) : Stmt :=
  .seq (.assign r.base (.load (.const 0)))
    (.seq (.store (.const 0) (.bin .add (.var r.base) (.var r.length)))
      (.seq (.assign r.pointer (.var r.base)) (.assign r.remaining (.var r.length))))

/-- One store followed by the ordinary pointer/counter assignments. -/
def fillBody (r : Registers) : Stmt :=
  .seq (.store (.var r.pointer) (.var r.value))
    (.seq (.assign r.pointer (.bin .add (.var r.pointer) (.const 1)))
      (.assign r.remaining (.bin .sub (.var r.remaining) (.const 1))))

def fill (r : Registers) : Stmt := .while (.var r.remaining) r.fillBody

/-- The single allocator implementation, independent of its local-slot layout. -/
def allocate (r : Registers) : Stmt := .seq r.prepare r.fill

theorem prepare_isStraightLine (r : Registers) : r.prepare.IsStraightLine := by
  simp [prepare, Stmt.IsStraightLine]

theorem fillBody_isStraightLine (r : Registers) : r.fillBody.IsStraightLine := by
  simp [fillBody, Stmt.IsStraightLine]

theorem prepare_code_size (r : Registers) (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable r.prepare = 12 := rfl

theorem fillBody_code_size (r : Registers) (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable r.fillBody = 11 := rfl

/-- Only the returned base and two traversal locals are assigned. -/
theorem allocate_writtenRegs (r : Registers) :
    r.allocate.writtenRegs = {r.base, r.pointer, r.remaining} := by
  ext slot
  simp [allocate, prepare, fill, fillBody, Stmt.writtenRegs, or_comm, or_left_comm]

/-- The allocator performs no function calls and needs no callee assumptions. -/
theorem allocate_callsValid (r : Registers) (program : Program) :
    Compiler.CallsValid program r.allocate := by
  simp [allocate, prepare, fill, fillBody, Compiler.CallsValid]

end Registers

/-- Five consecutive fresh slots. The first two hold the returned descriptor;
the next holds the initial word, followed by the loop pointer and counter. -/
def inlineRegisters (next : Reg) : Registers where
  base := next
  length := next + 1
  value := next + 2
  pointer := next + 3
  remaining := next + 4
  distinct := by
    simp [List.nodup_cons, Nat.add_left_cancel_iff]

end Ram.Source.Arena
