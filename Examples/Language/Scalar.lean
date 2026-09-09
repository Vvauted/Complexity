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
number with a supplied limit, and returns the smaller value. Both function
bodies are typed source syntax. Their mathematical proof uses generated monadic
equations and ordinary natural-number facts. Shared evaluation adequacy supplies
the source contracts used by the compiler, without another implementation proof.

This file establishes source behavior only. Realizing these unbounded natural
operations on a word backend requires its separate range, compilation and cost
theorems.
-/

namespace Complexity.Language.Examples.Scalar

source_program Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let next ← increment n
    if next ≤ limit then
      return next
    else
      return limit

/-- The increment helper and its two-argument caller. -/
abbrev signatures : List Signature := Implementation.signatures

/-- Bind the mathematical sum, then return it from the helper. -/
def increment : Stmt signatures [.nat] .nat :=
  Implementation.incrementBody

/-- Call the real helper, bind its Boolean comparison, then return from the
selected branch. The caller's second argument remains the original limit. -/
def boundedIncrement : Stmt signatures [.nat, .nat] .nat :=
  Implementation.boundedIncrementBody

/-- Both actual typed function bodies, with no host-side executable callback. -/
def program : Program signatures := Implementation.program

/-- The actual named helper has the ordinary mathematical increment value. -/
theorem increment_eval (n : Nat) :
    Implementation.increment n = (pure (n + 1) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [Implementation.increment_eq]

/-- The named source function has an ordinary curried mathematical result,
obtained from the same source correctness proof. -/
theorem boundedIncrement_eval (n limit : Nat) :
    Implementation.boundedIncrement n limit =
      (pure (min (n + 1) limit) : ExceptT Fault (StateT Heap Part) Nat) := by
  have helper : Implementation.increment n =
      (pure (n + 1) : ExceptT Fault (StateT Heap Part) Nat) := increment_eval n
  rw [Implementation.boundedIncrement_eq, helper, pure_bind]
  by_cases small : n + 1 ≤ limit
  · simp only [decide_eq_true_eq, if_pos small, Nat.min_eq_left small]
  · simp only [decide_eq_true_eq, if_neg small,
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))]

/-- Ordinary addition specifies the actual source helper. -/
theorem increment_total :
    FunctionTotal program (0 : Fin 2) (fun _ _ => True)
      (fun args heap value finish => value = Env.head args + 1 ∧ finish = heap) := by
  apply (Implementation.increment_total_iff (fun _ _ => True)
    (fun n heap value finish => value = n + 1 ∧ finish = heap)).mpr
  intro n heap _
  exact ⟨n + 1, heap, congrFun (increment_eval n) heap, rfl, rfl⟩

/-- The caller's source proof composes the helper contract and the actual branch. -/
theorem boundedIncrement_total :
    FunctionTotal program (1 : Fin 2) (fun _ _ => True)
      (fun args heap value finish =>
        value = min (Env.head args + 1) (Env.head (Env.tail args)) ∧ finish = heap) := by
  apply (Implementation.boundedIncrement_total_iff (fun _ _ _ => True)
    (fun n limit heap value finish => value = min (n + 1) limit ∧ finish = heap)).mpr
  intro n limit heap _
  exact ⟨(min (n + 1) limit : Nat), heap,
    congrFun (boundedIncrement_eval n limit) heap, rfl, rfl⟩

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
