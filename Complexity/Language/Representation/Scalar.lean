/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation
import Init.Data.UInt.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Native scalar views of existing source values

These representations preserve Lean's native `Int`, `Fin`, `BitVec`, `UInt64`
and `ZMod` as the mathematical types. They use only the existing natural,
boolean and product source types. Encoding and decoding are ghost views, not
new primitives or constant-time calls to arbitrary native functions.

The integer layout follows the constructors of `Int`: `(false, n)` represents
`ofNat n`, and `(true, n)` represents `negSucc n`, namely `-(n + 1)`.
Every pair is canonical, including `(true, 0)`, which represents `-1`.

Finite scalar ranges are properties of the represented value. They do not by
themselves establish that arithmetic intermediates fit a selected RAM width.
In particular, implementing modular multiplication with source `Nat.mul`
followed by `Nat.mod` must also represent the product and the modulus.
-/

namespace Complexity.Language.Representation

/-- The constructor layout of native integers, with no redundant negative zero. -/
def intEquiv : Int ≃ Bool × Nat where
  toFun
    | .ofNat n => (false, n)
    | .negSucc n => (true, n)
  invFun
    | (false, n) => .ofNat n
    | (true, n) => .negSucc n
  left_inv := by intro value; cases value <;> rfl
  right_inv := by rintro ⟨sign, magnitude⟩; cases sign <;> rfl

@[simp] theorem intEquiv_ofNat (n : Nat) : intEquiv (.ofNat n) = (false, n) := rfl

@[simp] theorem intEquiv_negSucc (n : Nat) : intEquiv (.negSucc n) = (true, n) := rfl

@[simp] theorem intEquiv_symm_false (n : Nat) :
    intEquiv.symm (false, n) = .ofNat n := rfl

@[simp] theorem intEquiv_symm_true (n : Nat) :
    intEquiv.symm (true, n) = .negSucc n := rfl

/-- Native integers occupy the existing boolean/natural product layout. -/
def int : Representation Int (.prod .bool .nat) := ofEmbedding intEquiv.toEmbedding

@[simp] theorem int_rel (a : Int) (value : Bool × Nat) (heap : Heap) :
    int.Rel a value heap ↔ intEquiv a = value := Iff.rfl

/-- Decoding the actual pair is the inverse of the mathematical encoding. -/
theorem int_rel_iff_decode (a : Int) (value : Bool × Nat) (heap : Heap) :
    int.Rel a value heap ↔ intEquiv.symm value = a := by
  constructor
  · intro represented
    rw [← (int_rel a value heap).mp represented]
    exact intEquiv.symm_apply_apply a
  · intro decoded
    rw [int_rel, ← decoded]
    exact intEquiv.apply_symm_apply value

/-- A native finite number stores its existing natural value. The proof of the
bound is not a runtime field, and `Fin 0` remains empty. -/
def finEmbedding (n : Nat) : Fin n ↪ Nat := ⟨Fin.val, Fin.val_injective⟩

def fin (n : Nat) : Representation (Fin n) .nat := ofEmbedding (finEmbedding n)

@[simp] theorem fin_rel (a : Fin n) (value : Nat) (heap : Heap) :
    (fin n).Rel a value heap ↔ a.val = value := Iff.rfl

theorem fin_range {a : Fin n} {value : Nat} {heap : Heap}
    (represented : (fin n).Rel a value heap) : value < n := by
  rw [← (fin_rel a value heap).mp represented]
  exact a.isLt

/-- Exactly the naturals below the bound encode a native finite number. -/
theorem fin_exists_iff (n value : Nat) (heap : Heap) :
    (∃ a, (fin n).Rel a value heap) ↔ value < n := by
  constructor
  · rintro ⟨a, represented⟩
    exact fin_range represented
  · intro inRange
    exact ⟨⟨value, inRange⟩, rfl⟩

/-- Bitvectors retain their explicitly selected mathematical width. -/
def bitVecEmbedding (width : Nat) : BitVec width ↪ Nat :=
  ⟨BitVec.toNat, fun _ _ same => BitVec.toNat_inj.mp same⟩

def bitVec (width : Nat) : Representation (BitVec width) .nat :=
  ofEmbedding (bitVecEmbedding width)

@[simp] theorem bitVec_rel (a : BitVec width) (value : Nat) (heap : Heap) :
    (bitVec width).Rel a value heap ↔ a.toNat = value := Iff.rfl

theorem bitVec_range {a : BitVec width} {value : Nat} {heap : Heap}
    (represented : (bitVec width).Rel a value heap) : value < 2 ^ width := by
  rw [← (bitVec_rel a value heap).mp represented]
  exact a.isLt

/-- The standard bitvector constructor decodes a valid natural field. -/
theorem bitVec_ofNat_rel {value : Nat} (inRange : value < 2 ^ width) (heap : Heap) :
    (bitVec width).Rel (BitVec.ofNat width value) value heap := by
  change (BitVec.ofNat width value).toNat = value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inRange]

theorem bitVec_exists_iff (width value : Nat) (heap : Heap) :
    (∃ a, (bitVec width).Rel a value heap) ↔ value < 2 ^ width := by
  constructor
  · rintro ⟨a, represented⟩
    exact bitVec_range represented
  · intro inRange
    exact ⟨BitVec.ofNat width value, bitVec_ofNat_rel inRange heap⟩

/-- Native `UInt64` uses its standard natural observation, not a new source type. -/
def uint64Embedding : UInt64 ↪ Nat :=
  ⟨UInt64.toNat, fun _ _ same => UInt64.toNat_inj.mp same⟩

def uint64 : Representation UInt64 .nat := ofEmbedding uint64Embedding

@[simp] theorem uint64_rel (a : UInt64) (value : Nat) (heap : Heap) :
    uint64.Rel a value heap ↔ a.toNat = value := Iff.rfl

theorem uint64_range {a : UInt64} {value : Nat} {heap : Heap}
    (represented : uint64.Rel a value heap) : value < 2 ^ 64 := by
  rw [← (uint64_rel a value heap).mp represented]
  exact a.toNat_lt

theorem uint64_ofNat_rel {value : Nat} (inRange : value < 2 ^ 64) (heap : Heap) :
    uint64.Rel (UInt64.ofNat value) value heap := by
  change (UInt64.ofNat value).toNat = value
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt inRange]

theorem uint64_exists_iff (value : Nat) (heap : Heap) :
    (∃ a, uint64.Rel a value heap) ↔ value < 2 ^ 64 := by
  constructor
  · rintro ⟨a, represented⟩
    exact uint64_range represented
  · intro inRange
    exact ⟨UInt64.ofNat value, uint64_ofNat_rel inRange heap⟩

/-- Positive-modulus `ZMod` has an injective standard least-residue observation.
For modulus zero `ZMod.val` is absolute value and is not injective. -/
def zmodEmbedding (modulus : Nat) [NeZero modulus] : ZMod modulus ↪ Nat :=
  ⟨ZMod.val, ZMod.val_injective modulus⟩

def zmod (modulus : Nat) [NeZero modulus] : Representation (ZMod modulus) .nat :=
  ofEmbedding (zmodEmbedding modulus)

@[simp] theorem zmod_rel [NeZero modulus] (a : ZMod modulus)
    (value : Nat) (heap : Heap) :
    (zmod modulus).Rel a value heap ↔ a.val = value := Iff.rfl

theorem zmod_range [NeZero modulus] {a : ZMod modulus} {value : Nat} {heap : Heap}
    (represented : (zmod modulus).Rel a value heap) : value < modulus := by
  rw [← (zmod_rel a value heap).mp represented]
  exact ZMod.val_lt a

theorem zmod_natCast_rel [NeZero modulus] {value : Nat}
    (inRange : value < modulus) (heap : Heap) :
    (zmod modulus).Rel (value : ZMod modulus) value heap := by
  change (value : ZMod modulus).val = value
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt inRange]

theorem zmod_exists_iff (modulus : Nat) [NeZero modulus] (value : Nat) (heap : Heap) :
    (∃ a, (zmod modulus).Rel a value heap) ↔ value < modulus := by
  constructor
  · rintro ⟨a, represented⟩
    exact zmod_range represented
  · intro inRange
    exact ⟨(value : ZMod modulus), zmod_natCast_rel inRange heap⟩

/-- Zero-modulus integers use their actual native `Int` type and signed layout. -/
def zmodZero : Representation (ZMod 0) (.prod .bool .nat) := int

end Complexity.Language.Representation
