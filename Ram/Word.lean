import Init.Data.BitVec.Lemmas

/-!
# Unsigned machine words

This module fixes the *results* of the finite vocabulary of word operations.
It contains no cost function or user-supplied cost annotation. Execution steps
and their cost belong to the machine semantics, not to these arithmetic lemmas.

Words have exactly `w` bits. Addition, subtraction, and multiplication wrap
modulo `2^w`. Division and remainder use Lean's unsigned convention:
`x / 0 = 0` and `x % 0 = x`, not SMT-LIB's all-ones division convention.
Shifts use the full unsigned value of the second operand (no masking of the
shift amount); right shift is logical. Comparisons return the word `0` or `1`.
Their truth-value interpretation requires `0 < w`, since width zero has only
one word. No signed arithmetic, host `Nat` computation, or arbitrary Lean
function can be inserted as an additional word operation.
-/

namespace Ram

/-- A fixed-width unsigned machine word. -/
abbrev Word (w : Nat) := BitVec w

namespace Word

/-- Every machine word denotes a natural number within its fixed width. -/
theorem toNat_lt (x : Word w) : x.toNat < 2 ^ w := x.isLt

/-- Encoding an in-range mathematical value is exact. -/
theorem ofNat_toNat_of_lt {n : Nat} (h : n < 2 ^ w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Decoding and re-encoding at the same width preserves the word. -/
@[simp] theorem ofNat_toNat_self (x : Word w) :
    BitVec.ofNat w x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  exact ofNat_toNat_of_lt x.isLt

/-- Zero tests in the machine agree with zero tests on decoded values. -/
@[simp] theorem toNat_eq_zero_iff (x : Word w) : x.toNat = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h
  · intro h
    rw [h]
    rfl

/-- Positive width is essential for word-valued Booleans. -/
theorem one_ne_zero (hw : 0 < w) : (1 : Word w) ≠ 0 := by
  simp [Nat.ne_of_gt hw]

end Word

/-- The finite vocabulary of unsigned binary word operations. -/
inductive BinOp where
  | add | sub | mul | udiv | umod
  | band | bor | bxor | shl | shr
  | eq | ult | ule
  deriving DecidableEq, Repr

namespace BinOp

/-- Fixed, total word semantics. This definition does not assign execution costs. -/
def eval {w : Nat} (op : BinOp) (x y : Word w) : Word w :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .udiv => x / y
  | .umod => x % y
  | .band => x &&& y
  | .bor => x ||| y
  | .bxor => x ^^^ y
  | .shl => x <<< y.toNat
  | .shr => x >>> y.toNat
  | .eq => if x = y then 1 else 0
  | .ult => if x.toNat < y.toNat then 1 else 0
  | .ule => if x.toNat ≤ y.toNat then 1 else 0

/-- Every operation result remains within the machine word range. -/
theorem eval_toNat_lt (op : BinOp) (x y : Word w) :
    (eval op x y).toNat < 2 ^ w := (eval op x y).isLt

@[simp] theorem eval_add (x y : Word w) : eval .add x y = x + y := rfl
@[simp] theorem eval_sub (x y : Word w) : eval .sub x y = x - y := rfl
@[simp] theorem eval_mul (x y : Word w) : eval .mul x y = x * y := rfl
@[simp] theorem eval_udiv (x y : Word w) : eval .udiv x y = x / y := rfl
@[simp] theorem eval_umod (x y : Word w) : eval .umod x y = x % y := rfl
@[simp] theorem eval_band (x y : Word w) : eval .band x y = x &&& y := rfl
@[simp] theorem eval_bor (x y : Word w) : eval .bor x y = x ||| y := rfl
@[simp] theorem eval_bxor (x y : Word w) : eval .bxor x y = x ^^^ y := rfl
@[simp] theorem eval_shl (x y : Word w) : eval .shl x y = x <<< y.toNat := rfl
@[simp] theorem eval_shr (x y : Word w) : eval .shr x y = x >>> y.toNat := rfl
@[simp] theorem eval_eq (x y : Word w) : eval .eq x y = if x = y then 1 else 0 := rfl
@[simp] theorem eval_ult (x y : Word w) :
    eval .ult x y = if x.toNat < y.toNat then 1 else 0 := rfl
@[simp] theorem eval_ule (x y : Word w) :
    eval .ule x y = if x.toNat ≤ y.toNat then 1 else 0 := rfl

/-- Unsigned addition computes the mathematical sum modulo the word range. -/
theorem eval_add_toNat (x y : Word w) :
    (eval .add x y).toNat = (x.toNat + y.toNat) % 2 ^ w :=
  BitVec.toNat_add x y

/-- An in-range sum is the exact mathematical sum, with no wraparound. -/
theorem eval_add_toNat_of_lt (x y : Word w)
    (h : x.toNat + y.toNat < 2 ^ w) :
    (eval .add x y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_lt h

/-- Subtraction wraps; it is not truncated natural-number subtraction. -/
theorem eval_sub_toNat (x y : Word w) :
    (eval .sub x y).toNat = ((2 ^ w - y.toNat) + x.toNat) % 2 ^ w :=
  BitVec.toNat_sub x y

/-- Subtraction agrees with natural subtraction when there is no underflow. -/
theorem eval_sub_toNat_of_le (x y : Word w) (h : y.toNat ≤ x.toNat) :
    (eval .sub x y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le h

/-- Underflow produces the wrapped difference, not zero. -/
theorem eval_sub_toNat_of_lt (x y : Word w) (h : x.toNat < y.toNat) :
    (eval .sub x y).toNat = 2 ^ w - (y.toNat - x.toNat) :=
  BitVec.toNat_sub_of_lt h

/-- Unsigned multiplication computes the mathematical product modulo the word range. -/
theorem eval_mul_toNat (x y : Word w) :
    (eval .mul x y).toNat = (x.toNat * y.toNat) % 2 ^ w :=
  BitVec.toNat_mul x y

/-- An in-range product is the exact mathematical product, with no wraparound. -/
theorem eval_mul_toNat_of_lt (x y : Word w)
    (h : x.toNat * y.toNat < 2 ^ w) :
    (eval .mul x y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_lt h

/-- Addition of encoded, in-range mathematical inputs has the expected result. -/
theorem eval_add_ofNat_toNat {a b : Nat}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hab : a + b < 2 ^ w) :
    (eval .add (BitVec.ofNat w a) (BitVec.ofNat w b)).toNat = a + b := by
  rw [eval_add_toNat, Word.ofNat_toNat_of_lt ha, Word.ofNat_toNat_of_lt hb,
    Nat.mod_eq_of_lt hab]

/-- Multiplication of encoded, in-range mathematical inputs has the expected result. -/
theorem eval_mul_ofNat_toNat {a b : Nat}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hab : a * b < 2 ^ w) :
    (eval .mul (BitVec.ofNat w a) (BitVec.ofNat w b)).toNat = a * b := by
  rw [eval_mul_toNat, Word.ofNat_toNat_of_lt ha, Word.ofNat_toNat_of_lt hb,
    Nat.mod_eq_of_lt hab]

theorem eval_udiv_toNat (x y : Word w) :
    (eval .udiv x y).toNat = x.toNat / y.toNat := BitVec.toNat_udiv

theorem eval_umod_toNat (x y : Word w) :
    (eval .umod x y).toNat = x.toNat % y.toNat := BitVec.toNat_umod

/-- Division by zero is deliberately total and returns zero. -/
@[simp] theorem eval_udiv_zero (x : Word w) : eval .udiv x 0 = 0 := BitVec.udiv_zero

/-- Remainder by zero is deliberately total and returns the dividend. -/
@[simp] theorem eval_umod_zero (x : Word w) : eval .umod x 0 = x := BitVec.umod_zero

theorem eval_band_toNat (x y : Word w) :
    (eval .band x y).toNat = x.toNat &&& y.toNat := BitVec.toNat_and x y

theorem eval_bor_toNat (x y : Word w) :
    (eval .bor x y).toNat = x.toNat ||| y.toNat := BitVec.toNat_or x y

theorem eval_bxor_toNat (x y : Word w) :
    (eval .bxor x y).toNat = x.toNat ^^^ y.toNat := BitVec.toNat_xor x y

theorem eval_shl_toNat (x y : Word w) :
    (eval .shl x y).toNat = (x.toNat <<< y.toNat) % 2 ^ w :=
  BitVec.toNat_shiftLeft

theorem eval_shr_toNat (x y : Word w) :
    (eval .shr x y).toNat = x.toNat >>> y.toNat :=
  BitVec.toNat_ushiftRight x y.toNat

theorem eval_eq_toNat (hw : 0 < w) (x y : Word w) :
    (eval .eq x y).toNat = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [eval, h, BitVec.toNat_one hw]

theorem eval_ult_toNat (hw : 0 < w) (x y : Word w) :
    (eval .ult x y).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x.toNat < y.toNat <;>
    simp [eval, h, BitVec.toNat_one hw]

theorem eval_ule_toNat (hw : 0 < w) (x y : Word w) :
    (eval .ule x y).toNat = if x.toNat ≤ y.toNat then 1 else 0 := by
  by_cases h : x.toNat ≤ y.toNat <;>
    simp [eval, h, BitVec.toNat_one hw]

/-- The machine's nonzero branch on equality agrees with mathematical equality. -/
theorem eval_eq_ne_zero_iff (hw : 0 < w) (x y : Word w) :
    eval .eq x y ≠ 0 ↔ x = y := by
  by_cases h : x = y <;> simp [eval, h, Nat.ne_of_gt hw]

/-- The machine's nonzero branch on unsigned less-than has its mathematical meaning. -/
theorem eval_ult_ne_zero_iff (hw : 0 < w) (x y : Word w) :
    eval .ult x y ≠ 0 ↔ x.toNat < y.toNat := by
  by_cases h : x.toNat < y.toNat <;> simp [eval, h, Nat.ne_of_gt hw]

/-- The machine's nonzero branch on unsigned less-or-equal has its mathematical meaning. -/
theorem eval_ule_ne_zero_iff (hw : 0 < w) (x y : Word w) :
    eval .ule x y ≠ 0 ↔ x.toNat ≤ y.toNat := by
  by_cases h : x.toNat ≤ y.toNat <;> simp [eval, h, Nat.ne_of_gt hw]

end BinOp
end Ram
