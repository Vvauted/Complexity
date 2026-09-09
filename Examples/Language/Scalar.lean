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
    Implementation.increment n = Part.some (.ok (n + 1)) := by
  rw [Implementation.increment_eq]
  rfl

/-- The named source function has an ordinary curried mathematical result,
obtained from the same source correctness proof. -/
theorem boundedIncrement_eval (n limit : Nat) :
    Implementation.boundedIncrement n limit = Part.some (.ok (min (n + 1) limit)) := by
  have helper : Implementation.increment n =
      (pure (n + 1) : ExceptT Fault Part Nat) := increment_eval n
  rw [Implementation.boundedIncrement_eq, helper, pure_bind]
  by_cases small : n + 1 ≤ limit
  · simp only [decide_eq_true_eq, if_pos small, Nat.min_eq_left small]
    rfl
  · simp only [decide_eq_true_eq, if_neg small,
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))]
    rfl

/-- Ordinary addition specifies the actual source helper. -/
theorem increment_total :
    FunctionTotal program (0 : Fin 2) (fun _ => True)
      (fun args value => value = Env.head args + 1) := by
  rw [FunctionTotal.iff_eval]
  refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
  intro n
  refine (Env.forall_nil _).mpr ?_
  intro _
  exact ⟨n + 1, increment_eval n, rfl⟩

/-- The caller's source proof composes the helper contract and the actual branch. -/
theorem boundedIncrement_total :
    FunctionTotal program (1 : Fin 2) (fun _ => True)
      (fun args value => value = min (Env.head args + 1) (Env.head (Env.tail args))) := by
  rw [FunctionTotal.iff_eval]
  refine (Env.forall_cons (τ := .nat) (Γ := [.nat]) _).mpr ?_
  intro n
  refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
  intro limit
  refine (Env.forall_nil _).mpr ?_
  intro _
  exact ⟨(min (n + 1) limit : Nat), boundedIncrement_eval n limit, rfl⟩

/-- A successful invocation exists for every pair of natural inputs, and its
actual returned value is the ordinary mathematical minimum. -/
theorem boundedIncrement_returns (n limit : Nat) :
    ∃ finish, Exec program (program.body (1 : Fin 2))
      (Env.cons n (Env.cons limit Env.empty)) finish (.returned (min (n + 1) limit : Nat)) := by
  obtain ⟨finish, value, execution, result⟩ :=
    boundedIncrement_total (Env.cons n (Env.cons limit Env.empty)) trivial
  have equal : value = min (n + 1) limit := result
  exact ⟨finish, equal ▸ execution⟩

/-- Every actual return from the caller has the proved mathematical value. -/
theorem boundedIncrement_result (n limit value : Nat)
    {finish : Env [.nat, .nat]}
    (execution : Exec program (program.body (1 : Fin 2))
      (Env.cons n (Env.cons limit Env.empty)) finish (.returned value)) :
    value = min (n + 1) limit :=
  boundedIncrement_total.postcondition trivial execution

end Complexity.Language.Examples.Scalar
