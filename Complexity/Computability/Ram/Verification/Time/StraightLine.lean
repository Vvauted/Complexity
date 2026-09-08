/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Exact.Basic
import Complexity.Computability.Ram.Source.StraightLine
import Complexity.Computability.Ram.Verification.Time.Basic

/-!
# Exact costs of straight-line source statements

Every completed execution of a straight-line block takes exactly the length of its
compiled code. This derives the costs of sequences of assignments, memory operations
and I/O from the existing compiler, without repeating their functional proofs.

`Ram.Source.TimeBound.of_isStraightLine` gives the corresponding conditional bound.
It does not establish safety or termination; use `Ram.Source.TotalContract.with_timeBound`
to combine it with a separate total-correctness proof.
-/

namespace Ram.Source

variable {w control heapLimit depth steps : Nat} {program : Program} {stmt : Stmt}
variable {s t : State w} {P : State w → Prop}

/-- A completed straight-line execution takes exactly the number of instructions
emitted by the local-frame compiler. -/
theorem LocalMeasuredExec.steps_eq_stmtSize
    (execution : LocalMeasuredExec control program heapLimit depth stmt steps s t)
    (straight : stmt.IsStraightLine) :
    steps = LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) stmt := by
  revert straight
  induction execution with
  | skip =>
      intro _
      rfl
  | assign _ =>
      intro _
      rfl
  | store _ _ _ =>
      intro _
      rfl
  | seq _ _ first second =>
      intro straight
      rw [LocalCompiler.stmtSize_seq, first straight.1, second straight.2]
  | iteTrue _ _ _ _ =>
      intro straight
      exact False.elim straight
  | iteFalse _ _ _ _ =>
      intro straight
      exact False.elim straight
  | whileFalse _ _ =>
      intro straight
      exact False.elim straight
  | whileTrue _ _ _ _ _ _ =>
      intro straight
      exact False.elim straight
  | read _ =>
      intro _
      rfl
  | write _ =>
      intro _
      rfl
  | call _ _ _ _ _ _ _ =>
      intro straight
      exact False.elim straight

/-- Bound every completed straight-line execution by its compiled code length.
No safety or termination assertion is needed for this conditional cost bound. -/
theorem TimeBound.of_isStraightLine (straight : stmt.IsStraightLine) :
    TimeBound control program heapLimit depth stmt P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) stmt) := by
  intro s _ steps t execution
  exact Nat.le_of_eq (execution.steps_eq_stmtSize straight)

end Ram.Source
