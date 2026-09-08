/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

/-!
# Shifted ceiling logarithms and significant-bit length

These arithmetic identities use mathlib's `Nat.clog`, `Nat.size` and `Nat.log2`.
They apply independently of an execution model, including to bounds for dividing
recurrences and to the significant-bit length of natural numbers.

## Main results

- `Nat.clog_div_succ_add_one`: division consumes one positive shifted-logarithm level.
- `Nat.clog_two_succ_eq_size`: the binary shifted logarithm is significant-bit length.
- `Nat.clog_two_succ_eq_log2`: its floor-logarithm form for a nonzero input.
-/

namespace Nat

/-- Dividing a positive natural by a base greater than one strictly decreases
its shifted ceiling logarithm. Both logarithms are mathlib's `Nat.clog`. -/
theorem clog_div_succ_lt {base n : Nat} (hb : 1 < base) (hn : 0 < n) :
    Nat.clog base (n / base + 1) < Nat.clog base (n + 1) := by
  have hk : 0 < Nat.clog base (n + 1) := Nat.clog_pos hb (by omega)
  apply lt_of_le_of_lt
    ((Nat.clog_le_iff_le_pow hb).mpr (show n / base + 1 ≤
      base ^ (Nat.clog base (n + 1) - 1) from ?_))
    (Nat.sub_lt hk (by decide : 0 < 1))
  apply Nat.succ_le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < base)).mpr
  calc
    n < base ^ Nat.clog base (n + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_pow_clog hb (n + 1))
    _ = base ^ (Nat.clog base (n + 1) - 1) * base := by
      rw [← Nat.pow_succ]
      congr 1
      omega

/-- Exact division consumes exactly one digit of a positive number. This
identity also lets a digit-counting loop state its functional result using
the same mathlib logarithm as its runtime bound. -/
theorem clog_div_succ_add_one {base n : Nat} (hb : 1 < base) (hn : 0 < n) :
    Nat.clog base (n / base + 1) + 1 = Nat.clog base (n + 1) := by
  apply Nat.le_antisymm (Nat.succ_le_of_lt (clog_div_succ_lt hb hn))
  apply (Nat.clog_le_iff_le_pow hb).mpr
  have hnext : n + 1 ≤ (n / base + 1) * base :=
    Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega : 0 < base)).mp
      (Nat.lt_succ_self (n / base)))
  calc
    n + 1 ≤ (n / base + 1) * base := hnext
    _ ≤ base ^ Nat.clog base (n / base + 1) * base :=
      Nat.mul_le_mul_right base (Nat.le_pow_clog hb (n / base + 1))
    _ = base ^ (Nat.clog base (n / base + 1) + 1) := (Nat.pow_succ _ _).symm

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
