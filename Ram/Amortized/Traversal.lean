/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Amortized
import Ram.Loop.Traversal

/-!
# Amortized traversal of a ghost occurrence list

Each real body execution consumes one logical occurrence, with a shared
state-dependent potential. Intermediate potential cancels between consecutive
executions; the final potential remains on the left of the aggregate bound,
and the initial potential remains on its right.

The list is only a proof index. It need not be stored by the RAM program or
recoverable as a function of its state. Repeated values are separate visits,
not deduplicated elements. Guard behavior, heap-read safety, and each measured
body execution are explicit proof obligations.

Charges use the same `Traversal.budget` arithmetic as ordinary traversal,
including every compiled guard, back-edge jump, and the final guard. They are
not replacement instruction prices: the conclusion retains the existing
`AmortizedContract` and its actual `LocalMeasuredExec` witness. In particular,
the accumulated charge alone is not claimed to bound time when the initial
potential is nonzero.
-/

namespace Ram.Source.AmortizedContract

universe u

/-- Follow a ghost list using measured amortized body contracts. The list
may contain repeated occurrences, and the charge for an occurrence may depend
on its remaining tail. Both endpoint potentials are retained. -/
theorem while_list {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (visits : List α)
    (invariant : List α → State w → Prop) (potential : State w → Nat)
    (bodyCharge : α → List α → Nat)
    (reads : ∀ remaining s, invariant remaining s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (iteration : ∀ a rest, AmortizedContract control program heapLimit depth body
      (invariant (a :: rest)) (fun _ t => invariant rest t) potential
      (fun _ => bodyCharge a rest)) :
    AmortizedContract control program heapLimit depth (.while condition body)
      (invariant visits) (fun _ t => invariant [] t ∧ t.eval condition = 0)
      potential (fun _ => Traversal.budget control condition bodyCharge visits) := by
  induction visits with
  | nil =>
      intro s hs
      exact ⟨Contract.guardCost control condition, s,
        .whileFalse (reads [] s hs) (nilGuard s hs), ⟨hs, nilGuard s hs⟩, Nat.le_refl _⟩
  | cons a rest ih =>
      intro s hs
      obtain ⟨bodySteps, middle, hbody, hmiddle, hbodyCharge⟩ := iteration a rest s hs
      obtain ⟨restSteps, finish, hrest, hpost, hrestCharge⟩ := ih middle hmiddle
      refine ⟨_, finish,
        .whileTrue (reads (a :: rest) s hs) (consGuard a rest s hs) hbody hrest,
        hpost, ?_⟩
      change bodySteps + potential middle ≤ bodyCharge a rest + potential s at hbodyCharge
      change restSteps + potential finish ≤
        Traversal.budget control condition bodyCharge rest + potential middle at hrestCharge
      change Contract.guardCost control condition + bodySteps + 1 + restSteps +
        potential finish ≤ Traversal.budget control condition bodyCharge (a :: rest) + potential s
      rw [Traversal.budget_cons]
      omega

/-- Tail-independent charges sum over all occurrences. The exact same
aggregate still keeps final potential available for later compositions. -/
theorem while_list_sum {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (visits : List α)
    (invariant : List α → State w → Prop) (potential : State w → Nat)
    (bodyCharge : α → Nat)
    (reads : ∀ remaining s, invariant remaining s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (iteration : ∀ a rest, AmortizedContract control program heapLimit depth body
      (invariant (a :: rest)) (fun _ t => invariant rest t) potential
      (fun _ => bodyCharge a)) :
    AmortizedContract control program heapLimit depth (.while condition body)
      (invariant visits) (fun _ t => invariant [] t ∧ t.eval condition = 0) potential
      (fun _ => (visits.map bodyCharge).sum +
        visits.length * (Contract.guardCost control condition + 1) +
          Contract.guardCost control condition) := by
  simpa only [Traversal.budget_eq_map_sum] using
    while_list visits invariant potential (fun a _ => bodyCharge a)
      reads nilGuard consGuard iteration

end Ram.Source.AmortizedContract
