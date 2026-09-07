/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Nat.Log
import Ram.Loop

/-!
# Logarithmic budgets for dividing loop variants

When each iteration divides a nonnegative measure by a fixed base greater than
one, mathlib's `Nat.clog base (measure + 1)` bounds the number of iterations.
The shift handles zero and the final positive iteration uniformly. Clients
prove the decrease of their actual program state; the loop rule supplies
termination and the full guard/body/back-edge budget.
-/

namespace Ram.Source.Contract

/-- Dividing a positive natural by a base greater than one strictly decreases
its shifted ceiling logarithm. Both logarithms are mathlib's `Nat.clog`. -/
theorem clog_div_succ_lt {base n : Nat} (hb : 1 < base) (hn : 0 < n) :
    Nat.clog base (n / base + 1) < Nat.clog base (n + 1) := by
  have hk : 0 < Nat.clog base (n + 1) := Nat.clog_pos hb (by omega)
  apply lt_of_le_of_lt
    ((Nat.clog_le_iff_le_pow hb).mpr (show n / base + 1 ≤
      base ^ (Nat.clog base (n + 1) - 1) from ?_))
    (Nat.sub_lt hk (by decide : 0 < 1))
  apply Nat.succ_le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < base)).mpr
  calc
    n < base ^ Nat.clog base (n + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_pow_clog hb (n + 1))
    _ = base ^ (Nat.clog base (n + 1) - 1) * base := by
      rw [← Nat.pow_succ]
      congr 1
      omega

/-- Exact division consumes exactly one digit of a positive number. This
identity also lets a digit-counting loop state its functional result using
the same mathlib logarithm as its runtime bound. -/
theorem clog_div_succ_add_one {base n : Nat} (hb : 1 < base) (hn : 0 < n) :
    Nat.clog base (n / base + 1) + 1 = Nat.clog base (n + 1) := by
  apply Nat.le_antisymm (Nat.succ_le_of_lt (clog_div_succ_lt hb hn))
  apply (Nat.clog_le_iff_le_pow hb).mpr
  have hnext : n + 1 ≤ (n / base + 1) * base :=
    Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega : 0 < base)).mp
      (Nat.lt_succ_self (n / base)))
  calc
    n + 1 ≤ (n / base + 1) * base := hnext
    _ ≤ base ^ Nat.clog base (n / base + 1) * base :=
      Nat.mul_le_mul_right base (Nat.le_pow_clog hb (n / base + 1))
    _ = base ^ (Nat.clog base (n / base + 1) + 1) := (Nat.pow_succ _ _).symm

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
    (clog_div_succ_lt hb (positive s hs hz))⟩

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
