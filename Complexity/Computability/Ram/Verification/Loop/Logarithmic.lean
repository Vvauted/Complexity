/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Loop.Basic
import Complexity.Data.Nat.Log

/-!
# Logarithmic budgets for dividing loop variants

When each iteration divides a nonnegative measure by a fixed base greater than
one, mathlib's `Nat.clog base (measure + 1)` bounds the number of iterations.
The shift handles zero and the final positive iteration uniformly. Clients
prove the decrease of their actual program state; the loop rule supplies
termination and the full guard/body/back-edge budget.
-/

namespace Ram.Source.Contract

/-- A constant-cost body that divides a positive measure gets a logarithmic
total-correctness budget. The measure may decrease faster than division, and
the code may use any verified implementation of that decrease. -/
theorem while_div {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} (base : Nat) (hb : 1 < base)
    (invariant : State w → Prop) (measure : State w → Nat) (bodyBudget : Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (positive : ∀ s, invariant s → s.eval condition ≠ 0 → 0 < measure s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ measure t ≤ measure s / base) (fun _ => bodyBudget)) :
    Contract control program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0)
      (fun s => Nat.clog base (measure s + 1) *
        (guardCost control condition + bodyBudget + 1) + guardCost control condition) := by
  apply while_linear invariant (fun s => Nat.clog base (measure s + 1)) bodyBudget reads
  intro s hs hz
  apply (iteration s hs hz).mono_post
  intro t ht
  exact ⟨ht.1, lt_of_le_of_lt
    (Nat.clog_mono_right base (Nat.add_le_add_right ht.2 1))
    (Nat.clog_div_succ_lt hb (positive s hs hz))⟩

/-- The same logarithmic rule with the desired exit postcondition exposed. -/
theorem while_div_post {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} {Q : State w → Prop}
    (base : Nat) (hb : 1 < base) (invariant : State w → Prop)
    (measure : State w → Nat) (bodyBudget : Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (positive : ∀ s, invariant s → s.eval condition ≠ 0 → 0 < measure s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ measure t ≤ measure s / base) (fun _ => bodyBudget))
    (exitPost : ∀ t, invariant t → t.eval condition = 0 → Q t) :
    Contract control program heapLimit depth (.while condition body) invariant Q
      (fun s => Nat.clog base (measure s + 1) *
        (guardCost control condition + bodyBudget + 1) + guardCost control condition) :=
  (while_div base hb invariant measure bodyBudget reads positive iteration).mono_post
    (fun t ht => exitPost t ht.1 ht.2)

end Ram.Source.Contract
