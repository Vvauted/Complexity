/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Count

/-!
# Mathematical properties of a callable occurrence counter

These proofs use the existing array-count function and standard list facts.
They do not expand its traversal, registers or call frames. A decoded result
is a mathematical observation of the actual function, not a new executable
implementation. Each array is assumed to be present in memory already.
-/

namespace Ram.Examples.ArrayCount

open Source Source.Array

/-- Counting is insensitive to the order of the represented words. The heaps
and pointers may differ: this equates only returned counts, not shared states
or the work of constructing or permuting either array. -/
theorem eval_eq_of_perm {w heapLimit : Nat} {program : Program}
    {base₁ base₂ target : Word w} {xs ys : List (Word w)}
    {entry₁ entry₂ : Source.State w} (hw : 0 < w) (permutation : xs.Perm ys)
    (fit₁ : base₁.toNat + xs.length < 2 ^ w)
    (fit₂ : base₂.toNat + ys.length < 2 ^ w)
    (array₁ : ArrayAt heapLimit base₁ xs entry₁)
    (array₂ : ArrayAt heapLimit base₂ ys entry₂) :
    (countFunctions.function.count.eval program heapLimit
      (countFunctions.arguments.count base₁ (BitVec.ofNat w xs.length) target) entry₁).map
        (fun result => result.1.toNat) =
    (countFunctions.function.count.eval program heapLimit
      (countFunctions.arguments.count base₂ (BitVec.ofNat w ys.length) target) entry₂).map
        (fun result => result.1.toNat) := by
  rw [count_function_eval_toNat hw fit₁ array₁, count_function_eval_toNat hw fit₂ array₂,
    permutation.count_eq target]

end Ram.Examples.ArrayCount
