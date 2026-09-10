/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Eval
import Examples.Language.Factorial
import Examples.Language.Traversal

/-!
# Reusing source proofs after linking independent programs

The existing traversal table is linked before the existing factorial table.
Factorial's actual recursive calls are therefore relocated past the traversal
functions, while traversal retains its real helper calls and heap writes.
Neither implementation is copied or replaced by a host function.

The shared embedding theorem equates the linked observations with their original
source actions. The existing factorial and array-map proofs then apply directly,
including preservation of arbitrary initial heaps and disjoint borrowed views.
This is source-semantic linking; it makes no claim about compiled instruction
costs or calls newly added between the two previously closed tables.
-/

namespace Complexity.Language.Examples.Linking

/-- The two independently declared source tables, with every internal call renamed. -/
def program : Program
    (Traversal.Implementation.signatures ++ Factorial.Implementation.signatures) :=
  Traversal.Implementation.program.link Factorial.Implementation.program

/-- The traversal functions keep their original signatures in the combined table. -/
def traversalMap : SignatureMap Traversal.Implementation.signatures
    (Traversal.Implementation.signatures ++ Factorial.Implementation.signatures) :=
  SignatureMap.appendLeft _ _

/-- The recursive factorial function follows the complete traversal table. -/
def factorialMap : SignatureMap Factorial.Implementation.signatures
    (Traversal.Implementation.signatures ++ Factorial.Implementation.signatures) :=
  SignatureMap.appendRight _ _

/-- The factorial function is relocated by the actual left-hand table length. -/
theorem factorial_index :
    (factorialMap.toFun Factorial.Implementation.factorialId).val =
      Traversal.Implementation.signatures.length + Factorial.Implementation.factorialId.val :=
  rfl

/-- Observe the relocated factorial with ordinary parameters and its actual shared heap. -/
noncomputable def factorial (n : Nat) : ExceptT Fault (StateT Heap Part) Nat :=
  factorialMap.eval program Factorial.Implementation.factorialId
    (Env.cons (τ := .nat) n Env.empty)

/-- Linking preserves the whole recursive action, not only an assumed result specification. -/
theorem factorial_eq_original (n : Nat) :
    factorial n = Factorial.Implementation.factorial_action n :=
  (Program.embeds_link_right Traversal.Implementation.program
    Factorial.Implementation.program).eval_eq _ _

/-- The original ordinary induction proof applies to the relocated recursive program. -/
theorem factorial_eval (n : Nat) :
    factorial n = (pure (Nat.factorial n) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [factorial_eq_original, Factorial.Implementation.factorial_action_eq_pure,
    Factorial.factorial_eq]

/-- The linked recursion terminates with factorial and preserves any initial heap. -/
theorem factorial_eval_heap (n : Nat) (heap : Heap) :
    factorial n heap = Part.some (.ok (Nat.factorial n), heap) :=
  congrFun (factorial_eval n) heap

/-- Observe the linked traversal; its mutable buffer remains in the current shared heap. -/
noncomputable def boundedMap (xs : Buffer .nat) (limit : Nat) :
    ExceptT Fault (StateT Heap Part) Unit :=
  traversalMap.eval program Traversal.Implementation.boundedMapId
    (Env.cons (τ := .buffer .nat) xs (Env.cons (τ := .nat) limit Env.empty))

/-- Linking preserves the effectful traversal action, including its helper calls. -/
theorem boundedMap_eq_original (xs : Buffer .nat) (limit : Nat) :
    boundedMap xs limit = Traversal.Implementation.boundedMap xs limit :=
  (Program.embeds_link_left Traversal.Implementation.program
    Factorial.Implementation.program).eval_eq _ _

/-- The existing array-map and outside-buffer frame proofs hold at the linked
invocation's same actual final heap, including disjoint slices of one object. -/
theorem boundedMap_eval_frame (xs : Buffer .nat) (limit : Nat)
    {contents : Array Nat} {heap : Heap} (observed : xs.Contents heap contents) :
    ∃ finish, boundedMap xs limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (contents.map fun x => min (x + 1) limit) ∧
      xs.PreservesOutside heap finish := by
  rw [boundedMap_eq_original]
  exact Traversal.boundedMap_eval_frame xs limit observed

end Complexity.Language.Examples.Linking
