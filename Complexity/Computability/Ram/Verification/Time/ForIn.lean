/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.ForIn
import Complexity.Computability.Ram.Verification.Time.Composition

/-!
# Conditional time bounds for ordinary foreach statements

These rules count the existing `Stmt.forIn` constructors for an arbitrary body
with a uniform conditional bound. The body may change memory, I/O and other
registers; only preservation of the remaining-count register is required for
the loop bound. Each element load observes the current memory and cursor.

The loop rule reuses `while_linear` on states with a completed suffix of the
execution being bounded. It does not assume body totality or readonly storage.
Initialization evaluates the length after the pointer assignment, exactly as
the source statement does. Loads, assignments, guards and back-edges retain
their actual compiled instruction counts.
-/

namespace Ram.Source.TimeBound

variable {w control heapLimit depth bodyBudget : Nat} {program : Program} {body : Stmt}

/-- A completed iteration adds the actual element load and two cursor writes
to the conditional body bound. No register-separation or preservation premise
is needed just to count these instructions. -/
theorem forInBody (pointer remaining element : Reg)
    (time : TimeBound (w := w) control program heapLimit depth body
      (fun _ => True) (fun _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit depth
      (Stmt.forInBody pointer remaining element body)
      (fun _ => True) (fun _ => bodyBudget + 11) := by
  intro s _ steps t execution
  cases execution with
  | seq loaded rest =>
    cases loaded with
    | assign _ =>
      cases rest with
      | seq inner advance =>
        have bodyCount := time _ trivial _ _ inner
        cases advance with
        | seq first second =>
          cases first with
          | assign _ =>
            cases second with
            | assign _ =>
              change 3 + (_ + (4 + 4)) ≤ bodyBudget + 11
              dsimp only at bodyCount
              omega

/-- Bound a completed foreach loop by its initial remaining count. The body
need only preserve that register on its actual safe executions; no totality,
heap preservation or accumulator interface is assumed. -/
theorem forInLoop (pointer remaining element : Reg) (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining)
    (element_ne_remaining : element ≠ remaining)
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs remaining = s.regs remaining)
    (time : TimeBound (w := w) control program heapLimit depth body
      (fun _ => True) (fun _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit depth
      (Stmt.forInLoop pointer remaining element body) (fun _ => True)
      (fun s => (bodyBudget + 14) * (s.regs remaining).toNat + 2) := by
  let iteration := Stmt.forInBody pointer remaining element body
  let completed := fun s : State w => ∃ finish,
    SafeExec program heapLimit depth (.while (.var remaining) iteration) s finish
  have functional : TotalRelContract program heapLimit depth iteration
      (fun s => completed s ∧ s.eval (.var remaining) ≠ 0)
      (fun s t => completed t ∧ (t.regs remaining).toNat < (s.regs remaining).toNat) := by
    rintro s ⟨⟨finish, execution⟩, nonzero⟩
    cases execution with
    | whileFalse _ zero => exact False.elim (nonzero zero)
    | whileTrue _ _ first rest =>
      refine ⟨_, first, ⟨_, rest⟩, ?_⟩
      have decrease := ForIn.body_remaining pointer remaining element
        pointer_ne_remaining element_ne_remaining preserves first
      change s.regs remaining ≠ 0 at nonzero
      have positive : 0 < (s.regs remaining).toNat :=
        Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
      rw [decrease]
      have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
      change (BinOp.eval .sub (s.regs remaining) 1).toNat < (s.regs remaining).toNat
      rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [one]; omega), one]
      omega
  have cost : TimeBound control program heapLimit depth iteration
      (fun s => completed s ∧ s.eval (.var remaining) ≠ 0) (fun _ => bodyBudget + 11) :=
    (forInBody pointer remaining element time).consequence
      (fun _ _ => trivial) (fun _ _ => Nat.le_refl _)
  have bound := while_linear completed (fun s => (s.regs remaining).toNat)
    (bodyBudget + 11) functional cost
  intro s _ steps finish execution
  have bounded := bound s ⟨_, execution.erase⟩ steps finish execution
  change steps ≤ (s.regs remaining).toNat * (1 + 1 + (bodyBudget + 11) + 1) +
    (1 + 1) at bounded
  have coefficient : 1 + 1 + (bodyBudget + 11) + 1 = bodyBudget + 14 := by omega
  rw [coefficient] at bounded
  simpa only [Nat.reduceAdd, Nat.mul_comm] using bounded

/-- The full foreach bound includes both descriptor assignments and the final
guard. Its count is the actual length value after assigning the pointer, not
the length expression evaluated in the original state. -/
theorem forIn (pointer remaining element : Reg) {base length : Expr} (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining)
    (element_ne_remaining : element ≠ remaining)
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs remaining = s.regs remaining)
    (time : TimeBound (w := w) control program heapLimit depth body
      (fun _ => True) (fun _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit depth
      (Stmt.forIn pointer remaining element base length body) (fun _ => True)
      (fun s => (base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (bodyBudget + 14) * ((s.setReg pointer (s.eval base)).eval length).toNat + 4) := by
  intro s _ steps finish execution
  cases execution with
  | seq first rest =>
    cases first with
    | assign _ =>
      cases rest with
      | seq second traversal =>
        cases second with
        | assign _ =>
          have bounded := forInLoop pointer remaining element hw
            pointer_ne_remaining element_ne_remaining preserves time _ trivial _ _ traversal
          dsimp only at bounded ⊢
          simp only [State.setReg_same] at bounded
          simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
            List.length_append, List.length_singleton]
          omega

end Ram.Source.TimeBound
