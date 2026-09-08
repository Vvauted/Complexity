/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Loop.Basic

/-!
# Measured loops following a ghost occurrence list

The invariant relates a remaining logical list to the current machine-visible
source state. One real body execution consumes one occurrence. The same value
may occur many times, and every occurrence contributes its own body bound,
guard, and back-edge jump. Exiting the loop also pays for its final guard.

The list is a proof index, not an executable input representation and not a
function that must be recoverable from the machine state. Callers prove that
their actual body takes `invariant (a :: rest)` to `invariant rest`; these rules
do not read, remove, or process logical list elements for free. Both guard
behavior and the safety of its real reads are explicit premises.

`Traversal.budget` is arithmetic on proved body bounds. The guard cost is fixed
by the existing compiler, and the conclusion uses `LocalMeasuredExec` through
the ordinary total-correctness `Contract`, not a new runner or cost semantics.
-/

namespace Ram.Source

universe u

namespace Traversal

/-- A proved body bound for each occurrence and remaining tail, with all
compiled guard and back-edge instructions included. -/
def budget {α : Type u} (control : Nat) (condition : Expr)
    (bodyBudget : α → List α → Nat) : List α → Nat
  | [] => Contract.guardCost control condition
  | a :: rest => Contract.guardCost control condition + bodyBudget a rest + 1 +
      budget control condition bodyBudget rest

@[simp] theorem budget_nil {α : Type u} (control : Nat) (condition : Expr)
    (bodyBudget : α → List α → Nat) :
    budget control condition bodyBudget [] = Contract.guardCost control condition := rfl

@[simp] theorem budget_cons {α : Type u} (control : Nat) (condition : Expr)
    (bodyBudget : α → List α → Nat) (a : α) (rest : List α) :
    budget control condition bodyBudget (a :: rest) =
      Contract.guardCost control condition + bodyBudget a rest + 1 +
        budget control condition bodyBudget rest := rfl

/-- When a body bound depends only on the occurrence value, the full budget
is a list sum plus one guard/back-edge payment per occurrence and the final
guard. No distinctness assumption or deduplication is involved. -/
theorem budget_eq_map_sum {α : Type u} (control : Nat) (condition : Expr)
    (bodyBudget : α → Nat) (visits : List α) :
    budget control condition (fun a _ => bodyBudget a) visits =
      (visits.map bodyBudget).sum +
        visits.length * (Contract.guardCost control condition + 1) +
          Contract.guardCost control condition := by
  induction visits with
  | nil => simp only [budget_nil, List.map_nil, List.sum_nil, List.length_nil,
      Nat.zero_mul, Nat.zero_add]
  | cons a rest ih =>
      simp only [budget_cons, ih, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

end Traversal

namespace Contract

/-- Follow an arbitrary ghost occurrence list with a real while loop. The
list-indexed invariant need not be the graph of a function from states to
lists. Each body budget may depend on both the current occurrence and its
remaining tail, and is justified by an existing measured body contract. -/
theorem while_list {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (visits : List α)
    (invariant : List α → State w → Prop) (bodyBudget : α → List α → Nat)
    (reads : ∀ remaining s, invariant remaining s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (iteration : ∀ a rest, Contract control program heapLimit depth body
      (invariant (a :: rest)) (invariant rest) (fun _ => bodyBudget a rest)) :
    Contract control program heapLimit depth (.while condition body) (invariant visits)
      (fun t => invariant [] t ∧ t.eval condition = 0)
      (fun _ => Traversal.budget control condition bodyBudget visits) := by
  induction visits with
  | nil =>
      intro s hs
      exact ⟨guardCost control condition, s,
        .whileFalse (reads [] s hs) (nilGuard s hs), ⟨hs, nilGuard s hs⟩, Nat.le_refl _⟩
  | cons a rest ih =>
      intro s hs
      obtain ⟨bodySteps, middle, hbody, hmiddle, hbodyBound⟩ := iteration a rest s hs
      obtain ⟨restSteps, finish, hrest, hpost, hrestBound⟩ := ih middle hmiddle
      refine ⟨_, finish,
        .whileTrue (reads (a :: rest) s hs) (consGuard a rest s hs) hbody hrest,
        hpost, ?_⟩
      change bodySteps ≤ bodyBudget a rest at hbodyBound
      change restSteps ≤ Traversal.budget control condition bodyBudget rest at hrestBound
      change guardCost control condition + bodySteps + 1 + restSteps ≤
        Traversal.budget control condition bodyBudget (a :: rest)
      rw [Traversal.budget_cons]
      omega

/-- Occurrence-wise sum form of `while_list`. Repeated list values are charged
on every visit; the list never becomes a set of distinct values. -/
theorem while_list_sum {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (visits : List α)
    (invariant : List α → State w → Prop) (bodyBudget : α → Nat)
    (reads : ∀ remaining s, invariant remaining s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (iteration : ∀ a rest, Contract control program heapLimit depth body
      (invariant (a :: rest)) (invariant rest) (fun _ => bodyBudget a)) :
    Contract control program heapLimit depth (.while condition body) (invariant visits)
      (fun t => invariant [] t ∧ t.eval condition = 0)
      (fun _ => (visits.map bodyBudget).sum +
        visits.length * (guardCost control condition + 1) + guardCost control condition) := by
  simpa only [Traversal.budget_eq_map_sum] using
    while_list visits invariant (fun a _ => bodyBudget a) reads nilGuard consGuard iteration

end Contract

end Ram.Source
