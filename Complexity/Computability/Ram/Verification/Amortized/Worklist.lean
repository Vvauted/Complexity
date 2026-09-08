/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Amortized.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Dynamic ghost worklists with actual amortized execution

The worklist is an invariant index, not a new machine data structure or runner.
An iteration can replace it with any next list, including a longer list. Neither
the list nor its remaining budget must be recoverable from the machine state.
The supplied body contract still witnesses the existing `LocalMeasuredExec`.

Termination follows from strict decrease of `remaining work state + potential
state`. The remaining budget pays for every compiled guard, body charge, and
back-edge, including the final guard. The conclusion retains the final potential
and includes the initial potential in its accounting; charges do not define
machine costs or justify unproved body executions.

The spawn corollary uses a sum over occurrences and a state-dependent reserve
for not-yet-generated work. A permutation can reorder the resulting queue but
cannot silently remove duplicates. No monotonicity of worklist length is needed.
-/

namespace Ram.Source

universe u

namespace AmortizedContract

/-- Execute a dynamically changing ghost worklist. Each measured body returns
a next invariant index and pays its guard, amortized body charge, back-edge,
and the next remaining budget. The worklist itself need not get shorter. -/
theorem while_worklist {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (work : List α)
    (invariant : List α → State w → Prop) (remaining : List α → State w → Nat)
    (potential : State w → Nat) (charge : List α → State w → Nat)
    (reads : ∀ pending s, invariant pending s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (exitBudget : ∀ s, invariant [] s →
      Contract.guardCost control condition ≤ remaining [] s)
    (iteration : ∀ a rest, AmortizedContract control program heapLimit depth body
      (invariant (a :: rest))
      (fun entry final => ∃ next, invariant next final ∧
        Contract.guardCost control condition + charge (a :: rest) entry + 1 +
          remaining next final ≤ remaining (a :: rest) entry)
      potential (charge (a :: rest))) :
    AmortizedContract control program heapLimit depth (.while condition body)
      (invariant work) (fun _ final => invariant [] final ∧ final.eval condition = 0)
      potential (remaining work) := by
  have loop : ∀ k pending s, remaining pending s + potential s = k → invariant pending s →
      ∃ steps final, LocalMeasuredExec control program heapLimit depth
        (.while condition body) steps s final ∧
        (invariant [] final ∧ final.eval condition = 0) ∧
          steps + potential final ≤ remaining pending s + potential s := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro pending s hk hs
        cases pending with
        | nil =>
            exact ⟨Contract.guardCost control condition, s,
              .whileFalse (reads [] s hs) (nilGuard s hs), ⟨hs, nilGuard s hs⟩,
              Nat.add_le_add_right (exitBudget s hs) _⟩
        | cons a rest =>
            obtain ⟨bodySteps, middle, bodyRun, ⟨next, hmiddle, progress⟩, bodyBudget⟩ :=
              iteration a rest s hs
            change bodySteps + potential middle ≤ charge (a :: rest) s + potential s at bodyBudget
            change Contract.guardCost control condition + charge (a :: rest) s + 1 +
              remaining next middle ≤ remaining (a :: rest) s at progress
            have decreases : remaining next middle + potential middle < k := by omega
            obtain ⟨restSteps, final, restRun, post, restBudget⟩ :=
              ih (remaining next middle + potential middle) decreases next middle rfl hmiddle
            refine ⟨_, final,
              .whileTrue (reads (a :: rest) s hs) (consGuard a rest s hs) bodyRun restRun,
              post, ?_⟩
            change Contract.guardCost control condition + bodySteps + 1 + restSteps +
              potential final ≤ remaining (a :: rest) s + potential s
            omega
  intro s hs
  exact loop (remaining work s + potential s) work s rfl hs

/-- A consumed occurrence can spawn and reorder work. Its weight plus the
entry reserve pays for this iteration, the generated occurrences' weights,
and the final reserve. A state-dependent reserve allows new work without
requiring every old occurrence to carry all future work in its own weight. -/
theorem while_worklist_spawn {α : Type u} {control heapLimit depth : Nat}
    {program : Program} {condition : Expr} {body : Stmt} (work : List α)
    (invariant : List α → State w → Prop) (weight : α → Nat)
    (reserve potential : State w → Nat) (charge : List α → State w → Nat)
    (reads : ∀ pending s, invariant pending s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (iteration : ∀ a rest, AmortizedContract control program heapLimit depth body
      (invariant (a :: rest))
      (fun entry final => ∃ generated next, next.Perm (generated ++ rest) ∧
        invariant next final ∧
        Contract.guardCost control condition + charge (a :: rest) entry + 1 +
          (generated.map weight).sum + reserve final ≤ weight a + reserve entry)
      potential (charge (a :: rest))) :
    AmortizedContract control program heapLimit depth (.while condition body)
      (invariant work) (fun _ final => invariant [] final ∧ final.eval condition = 0)
      potential (fun s => (work.map weight).sum + reserve s +
        Contract.guardCost control condition) := by
  apply while_worklist work invariant
    (fun pending s => (pending.map weight).sum + reserve s + Contract.guardCost control condition)
    potential charge reads nilGuard consGuard
  · intro s _
    simp only [List.map_nil, List.sum_nil, Nat.zero_add]
    omega
  · intro a rest
    apply (iteration a rest).mono_post
    intro entry final _ post
    obtain ⟨generated, next, permutation, hnext, progress⟩ := post
    refine ⟨next, hnext, ?_⟩
    have sum_eq := (permutation.map weight).sum_eq
    simp only [List.map_append, List.sum_append] at sum_eq
    change Contract.guardCost control condition + charge (a :: rest) entry + 1 +
      ((next.map weight).sum + reserve final + Contract.guardCost control condition) ≤
        ((a :: rest).map weight).sum + reserve entry + Contract.guardCost control condition
    rw [sum_eq, List.map_cons, List.sum_cons]
    omega

end AmortizedContract

namespace Contract

/-- Ordinary measured body contracts give the same dynamic-worklist rule with
zero potential. The relational body postcondition remembers its entry state;
`RelContract.iff_entry` can supply it from ordinary ghost-entry contracts. -/
theorem while_worklist {α : Type u} {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (work : List α)
    (invariant : List α → State w → Prop) (remaining : List α → State w → Nat)
    (charge : List α → State w → Nat)
    (reads : ∀ pending s, invariant pending s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (nilGuard : ∀ s, invariant [] s → s.eval condition = 0)
    (consGuard : ∀ a rest s, invariant (a :: rest) s → s.eval condition ≠ 0)
    (exitBudget : ∀ s, invariant [] s → guardCost control condition ≤ remaining [] s)
    (iteration : ∀ a rest, RelContract control program heapLimit depth body
      (invariant (a :: rest))
      (fun entry final => ∃ next, invariant next final ∧
        guardCost control condition + charge (a :: rest) entry + 1 +
          remaining next final ≤ remaining (a :: rest) entry)
      (charge (a :: rest))) :
    Contract control program heapLimit depth (.while condition body)
      (invariant work) (fun final => invariant [] final ∧ final.eval condition = 0)
      (remaining work) := by
  have loop := AmortizedContract.while_worklist work invariant remaining (fun _ => 0) charge
    reads nilGuard consGuard exitBudget (fun a rest =>
      AmortizedContract.of_relContract (iteration a rest) (by
        intro entry final _ _
        exact Nat.le_refl _))
  simpa only [Nat.add_zero] using loop.toContract (fun _ _ _ post => post)

end Contract
end Ram.Source
