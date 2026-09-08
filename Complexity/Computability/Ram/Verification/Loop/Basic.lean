/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Contract

/-!
# Linear loop budgets from a decreasing natural variant

These rules package the elementary potential calculation on top of the
existing total-correctness loop contract. The body budget remains a bound to
prove for actual execution, not an annotation that changes operation costs.
Guard and back-edge costs come from the generated machine instructions.
-/

namespace Ram.Source.Contract

/-- Evaluating the compiled guard and executing its conditional branch. -/
def guardCost (control : Nat) (condition : Expr) : Nat :=
  (condition.compile (ABI.scratch control)).length + 1

/-- A strictly decreasing natural variant bounds the number of iterations.
The common body bound `bodyBudget` pays for its measured execution; every
iteration additionally pays for the guard and one back-edge jump, and exit
pays for the final guard. Call-depth capacity stays unchanged throughout. -/
theorem while_linear {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant : State w → Nat) (bodyBudget : Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ variant t < variant s) (fun _ => bodyBudget)) :
    Contract control program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0)
      (fun s => variant s * (guardCost control condition + bodyBudget + 1) +
        guardCost control condition) := by
  apply while_contract invariant
    (fun s => variant s * (guardCost control condition + bodyBudget + 1) +
      guardCost control condition) (fun _ => bodyBudget) reads
  · intro s _ _
    change guardCost control condition ≤
      variant s * (guardCost control condition + bodyBudget + 1) + guardCost control condition
    omega
  · intro s hs hz
    apply (iteration s hs hz).mono_post
    intro t ht
    refine ⟨ht.1, ?_⟩
    have hmul := Nat.mul_le_mul_right (guardCost control condition + bodyBudget + 1)
      (Nat.succ_le_of_lt ht.2)
    rw [Nat.succ_mul] at hmul
    change guardCost control condition + bodyBudget + 1 +
        (variant t * (guardCost control condition + bodyBudget + 1) +
          guardCost control condition) ≤
      variant s * (guardCost control condition + bodyBudget + 1) + guardCost control condition
    omega

/-- State the desired postcondition directly once the invariant and false
guard imply it; the linear budget and termination proof are unchanged. -/
theorem while_linear_post {control heapLimit depth : Nat} {program : Program}
    {condition : Expr} {body : Stmt} {Q : State w → Prop}
    (invariant : State w → Prop) (variant : State w → Nat) (bodyBudget : Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract control program heapLimit depth body (fun entry => entry = s)
        (fun t => invariant t ∧ variant t < variant s) (fun _ => bodyBudget))
    (exitPost : ∀ t, invariant t → t.eval condition = 0 → Q t) :
    Contract control program heapLimit depth (.while condition body) invariant Q
      (fun s => variant s * (guardCost control condition + bodyBudget + 1) +
        guardCost control condition) :=
  (while_linear invariant variant bodyBudget reads iteration).mono_post
    (fun t ht => exitPost t ht.1 ht.2)

end Ram.Source.Contract
