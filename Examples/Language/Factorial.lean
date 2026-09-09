/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Ordinary induction for a recursive source factorial

The source function makes a real self-call and multiplies its returned value.
Its generated one-step equation and ordinary natural-number induction prove
the mathematical factorial result, retaining every initial shared heap.

This is the high-level counterpart of the factorial use case in
`Examples.Ram.FactorialFunction`. It proves independent source behavior, not
word-RAM realizability for arbitrary natural inputs or an execution-time bound.
-/

namespace Complexity.Language.Examples.Factorial

source_program Implementation where
  def factorial (n : Nat) : Nat := do
    if n == 0 then
      return 1
    else
      let previous ← factorial (n - 1)
      return n * previous

/-- Ordinary induction proves the actual recursive source action. The equation
with `pure` includes termination and preservation of every initial heap. -/
theorem factorial_eval (n : Nat) :
    Implementation.factorial n =
      (pure (Nat.factorial n) : ExceptT Fault (StateT Heap Part) Nat) := by
  induction n with
  | zero =>
      rw [Implementation.factorial_eq]
      simp only [decide_eq_true_eq, if_true, Nat.factorial_zero]
  | succ n ih =>
      rw [Implementation.factorial_eq]
      simp only [decide_eq_true_eq, if_neg (Nat.succ_ne_zero n), Nat.factorial_succ]
      change (Implementation.factorial n >>= fun previous => pure ((n + 1) * previous)) =
        (pure ((n + 1) * Nat.factorial n) : ExceptT Fault (StateT Heap Part) Nat)
      rw [ih, pure_bind]

/-- The observed result is factorial and the complete shared heap is unchanged,
without selecting an empty heap or any other special starting state. -/
theorem factorial_eval_heap (n : Nat) (heap : Heap) :
    Implementation.factorial n heap = Part.some (.ok (Nat.factorial n), heap) :=
  congrFun (factorial_eval n) heap

/-- Generated argument conversion reuses the same mathematical proof as a
total source contract; no separate execution-tree proof is needed. -/
theorem factorial_total :
    FunctionTotal Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args heap value finish => value = Nat.factorial (Env.head args) ∧ finish = heap) := by
  apply (Implementation.factorial_total_iff (fun _ _ => True)
    (fun n heap value finish => value = Nat.factorial n ∧ finish = heap)).mpr
  intro n heap _
  exact ⟨Nat.factorial n, heap, factorial_eval_heap n heap, rfl, rfl⟩

end Complexity.Language.Examples.Factorial
