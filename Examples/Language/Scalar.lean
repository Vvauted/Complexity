/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Verification
import Complexity.Language.Syntax

/-!
# A mathematical proof of an independent source program

The program calls an increment function, compares its actual returned natural
number with a supplied limit, and assigns the smaller value to a local before
returning it. Both function
bodies are typed source syntax. Their mathematical proof uses the generated native
functions and ordinary natural-number facts. Shared evaluation adequacy supplies
the source contracts used by the compiler, without another implementation proof.

This file establishes source behavior only. Realizing these unbounded natural
operations on a word backend requires its separate range, compilation and cost
theorems.
-/

namespace Complexity.Language.Examples.Scalar

source_program (pure) Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if next ≤ limit then
      result := next
    else
      result := limit
    return result

/-- The increment helper and its two-argument caller. -/
abbrev signatures : List Signature := Implementation.signatures

/-- Bind the mathematical sum, then return it from the helper. -/
def increment : Stmt signatures [.nat] .nat :=
  Implementation.incrementBody

/-- Call the real helper, update a local in the selected branch, and observe
that update after the branch. The original limit parameter is unchanged. -/
def boundedIncrement : Stmt signatures [.nat, .nat] .nat :=
  Implementation.boundedIncrementBody

/-- Both actual typed function bodies, with no host-side executable callback. -/
def program : Program signatures := Implementation.program

/-- The actual named helper has the ordinary mathematical increment value. -/
theorem increment_eq (n : Nat) : Implementation.increment n = n + 1 := rfl

/-- The named source function has an ordinary curried mathematical result,
obtained from the same source correctness proof. -/
theorem boundedIncrement_eq (n limit : Nat) :
    Implementation.boundedIncrement n limit = min (n + 1) limit := by
  by_cases small : n + 1 ≤ limit
  · simp [Implementation.boundedIncrement, Id.run, Id.instMonad,
      increment_eq, small]
  · simp [Implementation.boundedIncrement, Id.run, Id.instMonad, increment_eq, small,
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))]

/-- Ordinary addition specifies the actual source helper. -/
theorem increment_total :
    FunctionTotal program (0 : Fin 2) (fun _ _ => True)
      (fun args heap value finish => value = Env.head args + 1 ∧ finish = heap) := by
  simpa only [increment_eq] using Implementation.increment_total

/-- The caller's source proof composes the helper contract and the actual branch. -/
theorem boundedIncrement_total :
    FunctionTotal program (1 : Fin 2) (fun _ _ => True)
      (fun args heap value finish =>
        value = min (Env.head args + 1) (Env.head (Env.tail args)) ∧ finish = heap) := by
  simpa only [boundedIncrement_eq] using Implementation.boundedIncrement_total

/-- A successful invocation exists for every pair of natural inputs, and its
actual returned value is the ordinary mathematical minimum. -/
theorem boundedIncrement_returns (n limit : Nat) (heap : Heap) :
    ∃ finish, Exec program (program.body (1 : Fin 2))
      ⟨Env.cons n (Env.cons limit Env.empty), heap⟩ finish
      (.returned (min (n + 1) limit : Nat)) ∧ finish.heap = heap := by
  obtain ⟨finish, value, execution, result⟩ :=
    boundedIncrement_total (Env.cons n (Env.cons limit Env.empty)) heap trivial
  have equal : value = min (n + 1) limit := result.1
  exact ⟨finish, equal ▸ execution, result.2⟩

/-- Every actual return from the caller has the proved mathematical value. -/
theorem boundedIncrement_result (n limit value : Nat) (heap : Heap)
    {finish : State [.nat, .nat]}
    (execution : Exec program (program.body (1 : Fin 2))
      ⟨Env.cons n (Env.cons limit Env.empty), heap⟩ finish (.returned value)) :
    value = min (n + 1) limit :=
  (boundedIncrement_total.postcondition trivial execution).1

end Complexity.Language.Examples.Scalar
