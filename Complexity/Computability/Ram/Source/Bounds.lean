/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic

/-!
# Inferring local-register bounds from structured code

`Stmt.regBound` counts the register slots actually named by a statement, including
call destinations and argument expressions. It does not constrain callees or
assign an execution cost. Together with parameter and result-field bounds it
lets a compiler infer a function's local frame from its emitted syntax.
-/

namespace Ram.Stmt

/-- One past every register read or written by the actual statement syntax. -/
def regBound : Stmt → Nat
  | .skip => 0
  | .assign dst value => max (dst + 1) value.varBound
  | .store address value => max address.varBound value.varBound
  | .seq first second => max first.regBound second.regBound
  | .ite condition yes no => max condition.varBound (max yes.regBound no.regBound)
  | .while condition body => max condition.varBound body.regBound
  | .read dst => dst + 1
  | .write value => value.varBound
  | .call dsts _ args =>
      max (dsts.foldr (fun dst rest => max (dst + 1) rest) 0)
        (args.foldr (fun arg rest => max arg.varBound rest) 0)

private theorem foldr_max_le_iff {α : Type} (f : α → Nat) (xs : List α) (bound : Nat) :
    xs.foldr (fun x rest => max (f x) rest) 0 ≤ bound ↔
      ∀ x ∈ xs, f x ≤ bound := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, Nat.max_le, ih, List.forall_mem_cons]

/-- Any allowance covering the inferred bound covers every local operand.
Function existence, arity and dynamic safety remain separate obligations. -/
theorem wellFormed_of_regBound_le {stmt : Stmt} {locals : Nat}
    (bound : stmt.regBound ≤ locals) : stmt.WellFormed locals := by
  induction stmt with
  | skip => trivial
  | assign dst value =>
      have parts := Nat.max_le.mp bound
      exact ⟨Nat.lt_of_succ_le parts.1, value.bounded_varBound.mono parts.2⟩
  | store address value =>
      have parts := Nat.max_le.mp bound
      exact ⟨address.bounded_varBound.mono parts.1, value.bounded_varBound.mono parts.2⟩
  | seq first second ihFirst ihSecond =>
      have parts := Nat.max_le.mp bound
      exact ⟨ihFirst parts.1, ihSecond parts.2⟩
  | ite condition yes no ihYes ihNo =>
      have parts := Nat.max_le.mp bound
      have branches := Nat.max_le.mp parts.2
      exact ⟨condition.bounded_varBound.mono parts.1, ihYes branches.1, ihNo branches.2⟩
  | «while» condition body ih =>
      have parts := Nat.max_le.mp bound
      exact ⟨condition.bounded_varBound.mono parts.1, ih parts.2⟩
  | read dst => exact Nat.lt_of_succ_le bound
  | write value => exact value.bounded_varBound.mono bound
  | call dsts fn args =>
      have parts := Nat.max_le.mp bound
      have destinations := (foldr_max_le_iff (fun dst => dst + 1) dsts locals).mp parts.1
      have arguments := (foldr_max_le_iff Expr.varBound args locals).mp parts.2
      exact ⟨fun dst member => Nat.lt_of_succ_le (destinations dst member),
        fun arg member => arg.bounded_varBound.mono (arguments arg member)⟩

/-- The inferred bound is sufficient for the statement that produced it. -/
theorem wellFormed_regBound (stmt : Stmt) : stmt.WellFormed stmt.regBound :=
  wellFormed_of_regBound_le (Nat.le_refl _)

end Ram.Stmt
