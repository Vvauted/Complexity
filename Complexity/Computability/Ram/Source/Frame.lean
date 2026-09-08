/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Safe
import Mathlib.Data.Set.Insert

/-!
# Static frames for caller-local registers

`Stmt.writtenRegs` is a conservative set of destinations in the current local
frame. Assignments and reads write their destination; calls write only their
result destinations because the existing calling convention restores caller
locals. Callee memory and stream effects are unrestricted.

Every completed execution preserves a register outside this set. The set is
not a trace of actual writes: both branches are included, and a statement may
write a register and later restore it. Static exclusion is a sufficient way to
prove an endpoint frame, not a restriction on legal source programs.
-/

namespace Ram

/-- Local destinations a statement may write. Callee-local assignments are
private to its frame; only result receipt can change caller locals. -/
def Stmt.writtenRegs : Stmt → Set Reg
  | .skip | .store .. | .write .. => ∅
  | .assign dst _ | .read dst => {dst}
  | .seq first second => first.writtenRegs ∪ second.writtenRegs
  | .ite _ yes no => yes.writtenRegs ∪ no.writtenRegs
  | .while _ body => body.writtenRegs
  | .call dsts _ _ => {r | r ∈ dsts}

namespace Source

/-- A successful execution preserves any caller local outside its static
write set, irrespective of shared-memory or stream effects. -/
theorem Exec.regs_eq_of_not_mem_writtenRegs {program : Program} {stmt : Stmt}
    {s t : State w} (execution : Exec program stmt s t) {r : Reg}
    (outside : r ∉ stmt.writtenRegs) : t.regs r = s.regs r := by
  revert r
  induction execution with
  | skip => intros; rfl
  | assign =>
    intro r outside
    exact State.setReg_ne _ _ r _ (by simpa [Stmt.writtenRegs] using outside)
  | store => intros; rfl
  | seq _ _ first second =>
    intro r outside
    exact (second (r := r) (fun inside => outside (Or.inr inside))).trans
      (first (r := r) (fun inside => outside (Or.inl inside)))
  | iteTrue _ _ body =>
    intro r outside
    exact body (fun inside => outside (Or.inl inside))
  | iteFalse _ _ body =>
    intro r outside
    exact body (fun inside => outside (Or.inr inside))
  | whileFalse _ => intros; rfl
  | whileTrue _ _ _ body rest =>
    intro r outside
    exact (rest outside).trans (body outside)
  | read _ =>
    intro r outside
    exact State.setReg_ne _ _ r _ (by simpa [Stmt.writtenRegs] using outside)
  | write => intros; rfl
  | call _ _ _ _ _ _ =>
    intro r outside
    exact State.leave_ne _ _ _ r _ outside

/-- The same static frame applies to the original heap-safe execution, without
a second induction or a separately supplied callee contract. -/
theorem SafeExec.regs_eq_of_not_mem_writtenRegs {program : Program} {stmt : Stmt}
    {heapLimit depth : Nat} {s t : State w}
    (execution : SafeExec program heapLimit depth stmt s t) {r : Reg}
    (outside : r ∉ stmt.writtenRegs) : t.regs r = s.regs r :=
  execution.erase.regs_eq_of_not_mem_writtenRegs outside

end Source
end Ram
