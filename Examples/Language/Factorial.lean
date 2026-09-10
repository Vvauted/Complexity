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
Its native Lean definition and ordinary natural-number induction prove the
mathematical factorial result. Generated correspondence transfers that result
to the same source program, retaining every initial shared heap.

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
    FunctionTotal Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args heap value finish => value = Nat.factorial (Env.head args) ∧ finish = heap) := by
  simpa only [factorial_eq] using Implementation.factorial_total

end Complexity.Language.Examples.Factorial
