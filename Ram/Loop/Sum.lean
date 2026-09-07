/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Ram.Loop

/-!
# Finite-sum budgets for variable-cost loop iterations

An iteration at variant value `k` may have its own proved body bound `B k`.
The finite sum reserves the guard, body bound, and back-edge for every possible
positive variant value, plus the final guard. A strictly decreasing variant
may skip values: nonnegativity of natural sums makes those unused reservations
harmless, so no monotonicity assumption on `B` is needed.

These are total-correctness contracts for the existing measured semantics.
The summands are bounds proved for real compiled execution, not source ticks
or an alternative cost semantics. Mathlib supplies finite-sum monotonicity and
the range-successor identity used in the potential argument.
-/

namespace Ram.Source.Contract

open scoped BigOperators

/-- The last guard plus the possible iterations at variant values `1, …, k`.
`bodyBudget` must be justified by the body contracts in `while_sum`. -/
def sumBudget (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat) (k : Nat) : Nat :=
  guardCost control condition +
    ∑ i ∈ Finset.range k, (guardCost control condition + bodyBudget (i + 1) + 1)

@[simp] theorem sumBudget_zero (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat) :
    sumBudget control condition bodyBudget 0 = guardCost control condition := by
  simp [sumBudget]

/-- Adding one possible variant value reserves one more actual iteration. -/
theorem sumBudget_succ (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat) (k : Nat) :
    sumBudget control condition bodyBudget (k + 1) =
      sumBudget control condition bodyBudget k + guardCost control condition +
        bodyBudget (k + 1) + 1 := by
  simp only [sumBudget, Finset.sum_range_succ, Nat.add_assoc]

/-- Separate total body work from the `k + 1` guard evaluations and `k`
back-edges, for subsequent algebraic or asymptotic estimates of the sum. -/
theorem sumBudget_eq (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat) (k : Nat) :
    sumBudget control condition bodyBudget k =
      (k + 1) * guardCost control condition +
        (∑ i ∈ Finset.range k, bodyBudget (i + 1)) + k := by
  simp [sumBudget, Finset.sum_add_distrib, Nat.add_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Extending a prefix only adds nonnegative natural summands. -/
theorem sumBudget_mono (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat) :
    Monotone (sumBudget control condition bodyBudget) := by
  intro a b hab
  exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.range_mono hab)) _

/-- Any strict decrease pays for the current iteration, even if it skips
several variant values or the body-bound function itself is not monotone. -/
theorem sumBudget_step_le (control : Nat) (condition : Expr) (bodyBudget : Nat → Nat)
    {before after : Nat} (hdecrease : after < before) :
    guardCost control condition + bodyBudget before + 1 +
        sumBudget control condition bodyBudget after ≤
      sumBudget control condition bodyBudget before := by
  cases before with
  | zero => omega
  | succ k =>
      have hmono := sumBudget_mono control condition bodyBudget
        (Nat.le_of_lt_succ hdecrease)
      rw [sumBudget_succ]
      omega

/-- A natural variant and a body contract at its current value give a
finite-sum time bound automatically. The body and loop retain the same allowed
call depth; all guard and back-edge work is included in the generated bound. -/
theorem while_sum {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant : State w → Nat) (bodyBudget : Nat → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ variant t < variant s) (fun _ => bodyBudget (variant s))) :
    Contract control program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0)
      (fun s => sumBudget control condition bodyBudget (variant s)) := by
  apply while_contract invariant
    (fun s => sumBudget control condition bodyBudget (variant s))
    (fun s => bodyBudget (variant s)) reads
  · intro s _ _
    exact Nat.le_add_right _ _
  · intro s hs hz
    apply (iteration s hs hz).mono_post
    intro t ht
    exact ⟨ht.1, sumBudget_step_le control condition bodyBudget ht.2⟩

/-- Produce the chosen exit postcondition without changing the sum budget. -/
theorem while_sum_post {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} {Q : State w → Prop}
    (invariant : State w → Prop) (variant : State w → Nat) (bodyBudget : Nat → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ variant t < variant s) (fun _ => bodyBudget (variant s)))
    (exitPost : ∀ t, invariant t → t.eval condition = 0 → Q t) :
    Contract control program heapLimit depth (.while condition body) invariant Q
      (fun s => sumBudget control condition bodyBudget (variant s)) :=
  (while_sum invariant variant bodyBudget reads iteration).mono_post
    (fun t ht => exitPost t ht.1 ht.2)

end Ram.Source.Contract
