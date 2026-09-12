/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Complexity.Language.Eval.Locals.Range
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Ordinary proofs for recursive and iterative source factorials

The source function makes a real self-call and multiplies its returned value.
Its native Lean definition and ordinary natural-number induction prove the
mathematical factorial result. Generated correspondence transfers that result
to the same source program, retaining every initial shared heap.

The iterative declaration uses a finite source `for` and a mutable accumulator.
Its native proof reduces the same iteration to an ordinary list fold, then
reuses mathlib's factorial product formula. Generated correspondence supplies
source correctness without an author-written loop invariant or heap adapter.

This is the high-level counterpart of the factorial use case in
`Examples.Ram.FactorialFunction`. It proves independent source behavior, not
word-RAM realizability for arbitrary natural inputs or an execution-time bound.
-/

namespace Complexity.Language.Examples.Factorial

source_program (pure) Implementation where
  def factorial (n : Nat) : Nat := do
    if n == 0 then
      return 1
    else
      let previous ← factorial (n - 1)
      return n * previous
    termination_by n
    decreasing_by simp_wf; simp_all +zetaDelta; omega

/-- Ordinary induction proves the implementation's mathematical result. -/
theorem factorial_eq (n : Nat) : Implementation.factorial n = Nat.factorial n := by
  induction n with
  | zero =>
      simp [Implementation.factorial, Id.run, Id.instMonad]
  | succ n ih =>
      rw [Implementation.factorial]
      simpa only [Id.run, Id.instMonad, Nat.add_sub_cancel, Nat.factorial_succ,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, Bool.false_eq_true,
        if_false] using congrArg (fun previous => (n + 1) * previous) ih

/-- Generated correspondence transfers the mathematical result to total source
correctness without a second recursive proof or manual heap conversion. -/
theorem factorial_total :
    Implementation.factorial_contract (fun _ _ => True)
      (fun n heap value finish => value = Nat.factorial n ∧ finish = heap) := by
  simpa only [factorial_eq] using Implementation.factorial_total

source_program (pure) Iterative where
  def factorial (n : Nat) : Nat := do
    let mut acc := 1
    for i in [:n] do
      acc := acc * (i + 1)
    return acc

/-- The finite source iteration computes mathlib's factorial. Its proof uses
ordinary fold and product identities, without source execution bookkeeping. -/
theorem iterative_factorial_eq (n : Nat) : Iterative.factorial n = Nat.factorial n := by
  source_pure_simp [Iterative.factorial]
  rw [← List.range_eq_range',
    ← List.foldl_map (f := fun index : Nat => index + 1) (g := (· * ·)),
    ← List.prod_eq_foldl]
  exact Finset.prod_range_add_one_eq_factorial n

/-- The generated pure correspondence transfers the iterative result to the
same source body, with no second termination proof or assumed machine budget. -/
theorem iterative_factorial_total :
    Iterative.factorial_contract (fun _ _ => True)
      (fun n heap value finish => value = Nat.factorial n ∧ finish = heap) := by
  simpa only [iterative_factorial_eq] using Iterative.factorial_total

end Complexity.Language.Examples.Factorial
