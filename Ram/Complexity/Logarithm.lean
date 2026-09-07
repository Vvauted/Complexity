/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Ram.Complexity

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
These count significant bits; `wordListBitSize` in `Ram.Complexity.Encoding`
instead counts all bits in a fixed-width representation, including leading
zeros. No word-width policy or bit-machine runtime is inferred here.

The budget bridge starts from an all-input upper bound. Only its asymptotic
conclusion omits the sizes zero and one: successful execution on those inputs
still follows from the original `UniformTimeBound` premise.
-/

namespace Nat

/-- The shifted binary ceiling logarithm is exactly the significant-bit
length, with both sides zero at `n = 0`. -/
theorem clog_two_succ_eq_size (n : Nat) : clog 2 (n + 1) = size n := by
  apply eq_of_forall_ge_iff
  intro w
  rw [clog_le_iff_le_pow (by decide : 1 < 2), size_le]
  omega

/-- Positive values have one more significant bit than their floor binary
logarithm. The hypothesis is necessary since `log2 0 = 0`. -/
theorem clog_two_succ_eq_log2 {n : Nat} (hn : n ≠ 0) :
    clog 2 (n + 1) = log2 n + 1 := by
  apply eq_of_forall_ge_iff
  intro w
  simp only [clog_le_iff_le_pow (by decide : 1 < 2), Nat.add_one_le_iff, log2_lt hn]

end Nat

namespace Ram

/-- A decoded word's significant-bit length never exceeds its declared
width. This includes the unique word of width zero. -/
theorem Word.clog_toNat_succ_le (x : Word w) : Nat.clog 2 (x.toNat + 1) ≤ w := by
  rw [Nat.clog_two_succ_eq_size]
  exact Nat.size_le.mpr x.isLt

namespace Complexity

/-- An all-input affine ceiling-log budget gives the standard floor-log
asymptotic bound. Setup and termination costs may be included in `b`; no
condition on their value or on the small-input costs is dropped from `bound`.
This is arithmetic analysis of a proved budget, not an execution theorem. -/
theorem isBigO_log2_of_le_clog {T : Nat → Nat} {a b : Nat}
    (bound : ∀ n, T n ≤ a * Nat.clog 2 (n + 1) + b) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (Nat.log2 n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((2 * a + b : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnonzero : n ≠ 0 := by omega
  have hlog : 1 ≤ Nat.log2 n := (Nat.le_log2 hnonzero).mpr (by simpa using hn)
  have ha : a ≤ a * Nat.log2 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hlog
  have hb : b ≤ b * Nat.log2 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hlog
  have hnat : T n ≤ (2 * a + b) * Nat.log2 n := by
    have h := bound n
    rw [Nat.clog_two_succ_eq_log2 hnonzero, Nat.mul_add, Nat.mul_one] at h
    simp only [Nat.add_mul, Nat.two_mul]
    omega
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr hnat : (T n : ℝ) ≤ (((2 * a + b) * Nat.log2 n : Nat) : ℝ))

end Complexity

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
  h.bigO_of_isBigO (Complexity.isBigO_log2_of_le_clog (fun _ => Nat.le_refl _))

end Ram
