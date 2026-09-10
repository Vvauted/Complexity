/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Factorial
import Examples.Language.TraversalComposition

/-!
# Named source calls across independently declared programs

The client imports the existing recursive factorial and effectful traversal
libraries. Its source calls refer to their qualified names; the generated
function table contains the relocated library implementations and their internal
call graphs, not host callbacks or specifications standing in for code.

The generated one-step equations expose the original library observations.
Existing mathematical proofs therefore establish the client's factorial result
and two-buffer frame without reopening recursion or either traversal loop.
A second client imports the first, retaining this transitive source call graph.
These are source correctness claims, not inherited compiled instruction bounds.
-/

namespace Complexity.Language.Examples.Imports

source_program Implementation importing Factorial.Implementation, Traversal.Implementation where
  def factorial (n : Nat) : Nat := do
    let result ← Factorial.Implementation.factorial n
    return result

  def boundedMapPair (xs : Buffer Nat) (ys : Buffer Nat) (limit : Nat) : Unit := do
    Traversal.Implementation.boundedMap xs limit
    Traversal.Implementation.boundedMap ys limit
    return

/-- The client makes a real library call and returns its actual result. -/
theorem factorial_eq_original (n : Nat) :
    Implementation.factorial n = Factorial.Implementation.factorial_action n := by
  rw [Implementation.factorial_eq, bind_pure]

/-- The existing recursive proof supplies the client's mathematical result. -/
theorem factorial_eval (n : Nat) :
    Implementation.factorial n =
      (pure (Nat.factorial n) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [factorial_eq_original, Factorial.Implementation.factorial_action_eq_pure,
    Factorial.factorial_eq]

/-- The imported recursive call terminates and preserves every initial shared heap. -/
theorem factorial_eval_heap (n : Nat) (heap : Heap) :
    Implementation.factorial n heap = Part.some (.ok (Nat.factorial n), heap) :=
  congrFun (factorial_eval n) heap

/-- The client's two imported calls have the same source action as the existing
two-buffer composition; neither callee's implementation is unfolded. -/
theorem boundedMapPair_eq_original (xs ys : Buffer .nat) (limit : Nat) :
    Implementation.boundedMapPair xs ys limit =
      Traversal.Implementation.boundedMapPair xs ys limit := by
  rw [Implementation.boundedMapPair_eq, Traversal.Implementation.boundedMapPair_eq]

/-- The existing composition proof gives both mapped arrays and preservation
outside both views at the same actual final heap, without a new frame argument. -/
theorem boundedMapPair_eval (xs ys : Buffer .nat) (limit : Nat)
    {leftContents rightContents : Array Nat} {heap : Heap}
    (observedLeft : xs.Contents heap leftContents)
    (observedRight : ys.Contents heap rightContents) (separated : xs.Disjoint ys) :
    ∃ finish, Implementation.boundedMapPair xs ys limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (leftContents.map fun x => min (x + 1) limit) ∧
      ys.Contents finish (rightContents.map fun x => min (x + 1) limit) ∧
      ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
        xs.Disjoint other → ys.Disjoint other →
          other.Contents heap contents → other.Contents finish contents := by
  rw [boundedMapPair_eq_original]
  exact Traversal.boundedMapPair_eval xs ys limit observedLeft observedRight separated

source_program Second importing Implementation where
  def factorial (n : Nat) : Nat := do
    let result ← Implementation.factorial n
    return result

/-- Importing a client retains its call into the original recursive library. -/
theorem second_factorial_eval (n : Nat) :
    Second.factorial n =
      (pure (Nat.factorial n) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [Second.factorial_eq, bind_pure]
  exact factorial_eval n

/-- The second import layer likewise preserves any initial heap. -/
theorem second_factorial_eval_heap (n : Nat) (heap : Heap) :
    Second.factorial n heap = Part.some (.ok (Nat.factorial n), heap) :=
  congrFun (second_factorial_eval n) heap

end Complexity.Language.Examples.Imports
