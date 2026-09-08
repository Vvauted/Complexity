/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Asymptotics.Logarithm
import Complexity.Computability.Ram.Time.Basic

/-!
# Discrete logarithms, word capacity, and verified logarithmic time

The logarithm used by dividing-loop budgets is `Nat.clog 2 (n + 1)`.
It is exactly mathlib's binary length `Nat.size n`, including at zero.
For positive inputs it is `Nat.log2 n + 1`; that second identity must not
be applied at zero.

Capacity reasoning uses the upstream equivalence `Nat.size_le`:
`Nat.size n ≤ w ↔ n < 2 ^ w`. Thus the identity below also converts between
ceiling-log bounds and exact finite-word capacity without requiring `0 < w`.
`Nat.size_eq_bits_len` connects the same quantity to the length of `Nat.bits`.
These count significant bits; `wordListBitSize` in `Complexity.Computability.Ram.Problem.Encoding`
instead counts all bits in a fixed-width representation, including leading
zeros. No word-width policy or bit-machine runtime is inferred here.

The budget bridge starts from an all-input upper bound. Only its asymptotic
conclusion omits the sizes zero and one: successful execution on those inputs
still follows from the original `UniformTimeBound` premise.
-/

namespace Ram

/-- A decoded word's significant-bit length never exceeds its declared
width. This includes the unique word of width zero. -/
theorem Word.clog_toNat_succ_le (x : Word w) : Nat.clog 2 (x.toNat + 1) ≤ w := by
  rw [Nat.clog_two_succ_eq_size]
  exact Nat.size_le.mpr x.isLt

/-- Transfer a concrete ceiling-log machine budget directly to uniform
logarithmic time for the same fixed code, admissible inputs, and size measure.
The premise still requires successful execution and the postcondition at
every legal size, including zero and one. -/
theorem UniformTimeBound.logarithmic {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {a b : Nat}
    (h : UniformTimeBound code encode admissible size post
      (fun n => a * Nat.clog 2 (n + 1) + b)) :
    UniformBigO code encode admissible size post Nat.log2 :=
  h.bigO_of_isBigO (Asymptotics.isBigO_log2_of_le_clog (fun _ => Nat.le_refl _))

end Ram
