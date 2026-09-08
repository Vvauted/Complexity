/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySum

/-!
# Mathematical properties of executable slice sums

After proving the value equation for `sumSlice`, clients can use ordinary list
identities to reason about the executable function. These results specialize it
to empty and whole slices, and split a sum into two adjacent slices. The proofs
use neither an execution relation nor the implementation of the summation loop.

All applications still require represented memory, legal slice ranges and enough
stack space. The partition theorem compares returned values; it does not compile
the two host-level applications into a single function or assign them a cost.
-/

namespace Ram.Examples.ArraySlice

open Source Source.Array

variable {heapLimit : Nat} {array : ArrayRef 32} {xs : List (Word 32)}
  {entry : Source.State 32}

/-- The executable function returns zero on a zero-length slice at any legal
offset, including the end of the represented array. -/
theorem sumSlice_zero (offset : Word 32)
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (within : offset.toNat ≤ array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    sumSlice array offset 0 heapLimit entry ⟨xs, represented, fit⟩
      (by simpa using within) hstack = 0 := by
  rw [sumSlice_eq offset 0 fit (by simpa using within) hstack represented]
  simp

/-- Slicing the whole array agrees with the existing executable sum function.
Each implementation has its own sufficient stack-capacity premise. -/
theorem sumSlice_whole
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (sumStack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    sumSlice array 0 array.length heapLimit entry ⟨xs, represented, fit⟩
      (by simp) hstack =
      ArraySum.sum array heapLimit entry ⟨xs, represented, fit⟩ sumStack := by
  rw [sumSlice_eq 0 array.length fit (by simp) hstack represented,
    ArraySum.sum_eq fit sumStack represented]
  simp [represented.1]

/-- Two adjacent slices covering the array reproduce its sum modulo the word
range. This is a list decomposition theorem about the actual returned values. -/
theorem sumSlice_partition (left right : Word 32)
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (partition : left.toNat + right.toNat = array.length.toNat)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32)
    (sumStack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    (sumSlice array 0 left heapLimit entry ⟨xs, represented, fit⟩
        (by change 0 + left.toNat ≤ array.length.toNat; omega) hstack +
      sumSlice array left right heapLimit entry ⟨xs, represented, fit⟩
        (by omega) hstack) % 2 ^ 32 =
      ArraySum.sum array heapLimit entry ⟨xs, represented, fit⟩ sumStack := by
  rw [sumSlice_eq 0 left fit
      (by change 0 + left.toNat ≤ array.length.toNat; omega) hstack represented,
    sumSlice_eq left right fit (by omega) hstack represented,
    ArraySum.sum_eq fit sumStack represented]
  have suffix : (xs.drop left.toNat).take right.toNat = xs.drop left.toNat := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    have lengthEq := represented.1
    omega
  change ((((xs.take left.toNat).map BitVec.toNat).sum % 2 ^ 32 +
    (((xs.drop left.toNat).take right.toNat).map BitVec.toNat).sum % 2 ^ 32) % 2 ^ 32) = _
  rw [suffix]
  rw [← Nat.add_mod, ← List.sum_append, ← List.map_append, List.take_append_drop]

end Ram.Examples.ArraySlice
