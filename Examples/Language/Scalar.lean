/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Verification
import Complexity.Language.Syntax
import Mathlib.Algebra.BigOperators.Group.List.Defs

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
    if limit ≥ next then
      result := next
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
    Implementation.increment_contract (fun _ _ => True)
      (fun n heap value finish => value = n + 1 ∧ finish = heap) := by
  simpa only [increment_eq] using Implementation.increment_total

/-- The caller's source proof composes the helper contract and the actual branch. -/
theorem boundedIncrement_total :
    Implementation.boundedIncrement_contract (fun _ _ _ => True)
      (fun n limit heap value finish => value = min (n + 1) limit ∧ finish = heap) := by
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

/-- Ordinary mathematical inputs to the existing bounded increment operation. -/
structure BoundedInput where
  value : Nat
  limit : Nat

source_type BoundedInput

source_program (pure) Structured importing Implementation where
  def update (input : BoundedInput) : BoundedInput := do
    let value ← Implementation.boundedIncrement input.value input.limit
    return BoundedInput.mk value input.limit

  def run (n : Nat) (limit : Nat) : Nat := do
    let input := BoundedInput.mk n limit
    let result ← update input
    return result.value

/-- The native structure view reuses the unchanged scalar helper's mathematics. -/
theorem structured_update_eq (input : BoundedInput) :
    Structured.update input =
      BoundedInput.mk (min (input.value + 1) input.limit) input.limit := by
  simp [Structured.update, Id.run, Id.instMonad, boundedIncrement_eq]

/-- Constructing, passing and projecting an ordinary structure needs no second
algorithm or representation-specific mathematical proof. -/
theorem structured_run_eq (n limit : Nat) :
    Structured.run n limit = min (n + 1) limit := by
  simp [Structured.run, Id.run, Id.instMonad, structured_update_eq]

/-- The frontend's generated correspondence transfers the ordinary mathematical
equation to this same represented source invocation. -/
theorem structured_run_total :
    RepresentedFunction.Total Structured.program Structured.runId Structured.run_representation
      (fun _ => True) (fun input value => value = min (input.1 + 1) input.2) := by
  apply Structured.run_refines.of_math
  intro input _
  exact structured_run_eq input.1 input.2

source_program (pure) Strided where
  def sum (start : Nat) (stop : Nat) (k : Nat) : Nat := do
    let mut acc := 0
    for index in [start:stop:(k + 1)] do
      acc := acc + index
    return acc

/-- A dynamic positive stride enumerates the same ordinary arithmetic progression,
including empty ranges and a last increment that passes the stop. -/
theorem strided_sum_eq (start stop k : Nat) :
    Strided.sum start stop k =
      (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum := by
  source_pure_simp [Strided.sum]
  simpa only [Nat.add_succ_sub_one] using
    (List.sum_eq_foldl (l := List.range' start ((stop - start + k) / (k + 1)) (k + 1))).symm

source_program (pure) StructuredRange where
  def add (input : BoundedInput) (amount : Nat) : BoundedInput := do
    return BoundedInput.mk (input.value + amount) input.limit

  def sum (initial : BoundedInput) (start : Nat) (stop : Nat) (k : Nat) : BoundedInput := do
    let first ← add initial 0
    let mut acc := first
    for index in [start:stop:(k + 1)] do
      let next ← add acc index
      acc := next
    return acc

/-- The structure-valued helper retains the original limit and adds one amount. -/
theorem structured_range_add_eq (input : BoundedInput) (amount : Nat) :
    StructuredRange.add input amount = BoundedInput.mk (input.value + amount) input.limit := rfl

/-- A native structure remains the loop accumulator across actual source calls.
Ordinary fold transport proves its mathematical sum and unchanged second field. -/
theorem structured_range_sum_eq (initial : BoundedInput) (start stop k : Nat) :
    StructuredRange.sum initial start stop k =
      BoundedInput.mk (initial.value +
        (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum) initial.limit := by
  source_pure_simp [StructuredRange.sum, StructuredRange.add]
  simpa only [Nat.add_zero, Nat.add_succ_sub_one, ← List.sum_eq_foldl] using
    (List.foldl_hom (fun value : Nat => BoundedInput.mk (initial.value + value) initial.limit)
      (g₁ := (· + ·))
      (g₂ := fun acc index => BoundedInput.mk (acc.value + index) acc.limit)
      (l := List.range' start ((stop - start + k) / (k + 1)) (k + 1)) (init := 0)
      (by intro value index; simp only [Nat.add_assoc]))

/-- The mathematical structure equation transfers to the same terminating source
function through generated correspondence, without a second loop proof. -/
theorem structured_range_sum_total :
    RepresentedFunction.Total StructuredRange.program StructuredRange.sumId
      StructuredRange.sum_representation (fun _ => True)
      (fun input value => value = BoundedInput.mk (input.1.value +
        (List.range' input.2.1
          ((input.2.2.1 - input.2.1 + input.2.2.2) / (input.2.2.2 + 1))
          (input.2.2.2 + 1)).sum) input.1.limit) := by
  apply StructuredRange.sum_refines.of_math
  intro input _
  exact structured_range_sum_eq input.1 input.2.1 input.2.2.1 input.2.2.2

end Complexity.Language.Examples.Scalar
