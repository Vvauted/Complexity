/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Verification
import Complexity.Language.Syntax

/-!
# A mathematical proof of an independent source program

The program calls an increment function, compares its actual returned natural
number with a supplied limit, and returns the smaller value. Both function
bodies are typed source syntax. Their proof uses the source WP rules and ordinary
natural-number mathematics, not a reference algorithm or a register program.

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

/-- Ordinary addition specifies the actual source helper. -/
theorem increment_total :
    FunctionTotal program (0 : Fin 2) (fun _ => True)
      (fun args value => value = Env.head args + 1) := by
  apply FunctionTotal.of_wp
  intro args _
  change TotalWP program increment (fun _ => False)
    (fun value _ => value = Env.head args + 1) args
  simp [increment, Implementation.incrementBody, Env.head]

/-- The caller's source proof composes the helper contract and the actual branch. -/
theorem boundedIncrement_total :
    FunctionTotal program (1 : Fin 2) (fun _ => True)
      (fun args value => value = min (Env.head args + 1) (Env.head (Env.tail args))) := by
  apply FunctionTotal.of_wp
  intro args _
  change TotalWP program boundedIncrement (fun _ => False)
    (fun value _ => value = min (Env.head args + 1) (Env.head (Env.tail args))) args
  unfold boundedIncrement Implementation.boundedIncrementBody
  apply TotalWP.call increment_total trivial
  intro value returned
  have value_eq : value = Env.head args + 1 := returned
  subst value
  simp only [TotalWP.letPrim_iff, TotalWP.ite_iff, TotalWP.ret_iff,
    Prim.eval, Atom.eval, Env.cons_here, Env.cons_there]
  by_cases small : Env.head args + 1 ≤ Env.head (Env.tail args)
  · simp only [Env.head, Env.get_tail] at small ⊢
    simp [small]
  · simp only [Env.head, Env.get_tail] at small ⊢
    simp [small, Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))]

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

/-- The named source function has an ordinary curried mathematical result,
obtained from the same source correctness proof. -/
theorem boundedIncrement_eval (n limit : Nat) :
    Implementation.boundedIncrement n limit = Part.some (.ok (min (n + 1) limit)) :=
  Program.eval_eq_ok_iff.mpr (boundedIncrement_returns n limit)

end Complexity.Language.Examples.Scalar
