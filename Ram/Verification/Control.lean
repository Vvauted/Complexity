/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Refinement

/-!
# Control flow over ordinary mathematical models

Branch and loop proofs can keep their invariants, transition functions and
termination relations on ordinary Lean values rather than concrete RAM states.
Clients establish how the real guard and body represent those operations;
the rules below compose the existing safe executions. No abstract transition
is added to the instruction set, and the loop is one fixed source statement,
not a finite syntax unrolling selected by the mathematical input.

The loop result may be any existing mathematical function satisfying the
supplied step and exit equations. This avoids introducing another pure-loop
evaluator merely to state the refinement. Well-foundedness proves termination;
the separate `TimeBound` interface still measures the actual implementation.
-/

namespace Ram.Source.Refines

variable {α β : Type*} {program : Program} {heapLimit depth : Nat}

/-- Refine a source branch by the ordinary conditional on its mathematical
input. Each implementation is required only on its reachable branch domain. -/
theorem ite {condition : Expr} {yes no : Stmt}
    {inputRep : α → State w → Prop} {outputRep : β → State w → Prop}
    (choose : α → Prop) [DecidablePred choose] {f g : α → β}
    (reads : ∀ x s, inputRep x s → condition.ReadsBelow heapLimit s.regs s.mem)
    (guard : ∀ x s, inputRep x s → (s.eval condition ≠ 0 ↔ choose x))
    (first : Refines program heapLimit depth yes
      (fun x s => inputRep x s ∧ choose x) outputRep f)
    (second : Refines program heapLimit depth no
      (fun x s => inputRep x s ∧ ¬ choose x) outputRep g) :
    Refines program heapLimit depth (.ite condition yes no) inputRep outputRep
      (fun x => if choose x then f x else g x) := by
  intro x s represented
  by_cases hc : choose x
  · obtain ⟨t, execution, post⟩ := first x s ⟨represented, hc⟩
    exact ⟨t, .iteTrue (reads x s represented) ((guard x s represented).mpr hc) execution,
      by simpa only [if_pos hc] using post⟩
  · obtain ⟨t, execution, post⟩ := second x s ⟨represented, hc⟩
    have hz : s.eval condition = 0 := by
      by_contra hn
      exact hc ((guard x s represented).mp hn)
    exact ⟨t, .iteFalse (reads x s represented) hz execution,
      by simpa only [if_neg hc] using post⟩

/-- Prove a fixed RAM loop using an invariant and well-founded descent on
the ordinary mathematical model. Only the guard/body representation and exit
observation mention RAM states; invariant preservation, descent and the result
equation are ordinary Lean/mathlib propositions.

The representation need not be injective or supply a unique ghost state.
Every represented input must satisfy the explicit invariant, and each actual
body execution returns the stated next model before induction is reused. -/
theorem while_wellFounded {condition : Expr} {body : Stmt}
    {rep : α → State w → Prop} {outputRep : β → State w → Prop}
    (invariant continuing : α → Prop) (step : α → α) (result : α → β)
    {r : α → α → Prop} (wf : WellFounded r)
    (reads : ∀ x s, rep x s → invariant x →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (guard : ∀ x s, rep x s → invariant x →
      (s.eval condition ≠ 0 ↔ continuing x))
    (iteration : ∀ x, invariant x → continuing x →
      TotalContract program heapLimit depth body (rep x) (rep (step x)))
    (preserves : ∀ x, invariant x → continuing x → invariant (step x))
    (decreases : ∀ x, invariant x → continuing x → r (step x) x)
    (result_step : ∀ x, invariant x → continuing x → result (step x) = result x)
    (exit : ∀ x s, rep x s → invariant x → ¬ continuing x → outputRep (result x) s) :
    Refines program heapLimit depth (.while condition body)
      (fun x s => rep x s ∧ invariant x) outputRep result := by
  intro x
  induction x using wf.induction with
  | h x ih =>
      intro s ⟨represented, hinv⟩
      by_cases hc : continuing x
      · obtain ⟨middle, execution, next⟩ := iteration x hinv hc s represented
        obtain ⟨t, rest, post⟩ := ih (step x) (decreases x hinv hc)
          middle ⟨next, preserves x hinv hc⟩
        exact ⟨t, .whileTrue (reads x s represented hinv)
          ((guard x s represented hinv).mpr hc) execution rest,
          by simpa only [result_step x hinv hc] using post⟩
      · have hz : s.eval condition = 0 := by
          by_contra hn
          exact hc ((guard x s represented hinv).mp hn)
        exact ⟨s, .whileFalse (reads x s represented hinv) hz,
          exit x s represented hinv hc⟩

end Ram.Source.Refines
