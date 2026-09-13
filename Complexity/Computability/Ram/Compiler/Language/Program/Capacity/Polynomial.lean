/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Capacity

/-!
# Uniform capacity for input-dependent call depth

A polynomial bound on simultaneously live source calls fits the existing
logarithmic word-width policy after increasing its one global constant. The
polynomial is in the fixed input representation's length and maximum raw word;
it is not a replacement input encoding or a candidate-selected machine scale.

The bound concerns call depth, not execution time. Source execution must still
justify that depth, numerical ranges and allocation capacity. The theorem below
supplies only the actual compiled code and stack fields of `FunctionCapacity`.
-/

namespace Complexity.Program

open Ram.LanguageCompiler

universe u v

variable {α : Type u} {β : Type v} [Input α] [Output β]

/-- One fixed width overhead for a polynomial envelope on live call frames.
Its constant factor includes the selected program's actual code and frame size. -/
def capacityOverheadPow (program : Complexity.Program α β) (coefficient degree : Nat) : Nat :=
  program.capacityOverhead coefficient + degree

variable [RamInput α]

/-- A supplied polynomial depth bound gives actual code and stack capacity at
every admitted width. It does not filter out inputs whose execution needs more
frames; proving the depth bound for those inputs is a separate obligation. -/
theorem capacity_of_depth_le_pow (program : Complexity.Program α β)
    {x : α} {depth coefficient degree overhead w : Nat}
    (bounded : depth + 1 ≤ coefficient *
      ((RamInput.words x).size + ArrayFunction.inputMax (RamInput.words x) + 2) ^ degree)
    (large : program.capacityOverheadPow coefficient degree ≤ overhead)
    (admitted : width overhead x ≤ w) :
    FunctionCapacity program.source program.fn w depth (ArrayFunction.heapLimit w) := by
  let bits := ArrayFunction.inputWordWidth (RamInput.words x)
  let scale := (RamInput.words x).size + ArrayFunction.inputMax (RamInput.words x) + 2
  let constant := program.capacityOverhead coefficient
  let frame := Ram.ABI.frameSize (programControl program.source)
  let required := max (lowerCode program.source program.fn).length ((coefficient + 1) * frame)
  have requiredFits : required < 2 ^ constant := Nat.lt_log2_self (n := required)
  have codeFits : (lowerCode program.source program.fn).length < 2 ^ constant :=
    (Nat.le_max_left _ _).trans_lt requiredFits
  have frameFits : coefficient * frame < 2 ^ constant :=
    (Nat.mul_le_mul_right frame (Nat.le_succ coefficient)).trans_lt
      ((Nat.le_max_right _ _).trans_lt requiredFits)
  have scaleFits : scale < 2 ^ bits := by
    change scale < 2 ^ (1 + Nat.log2 scale)
    simpa only [Nat.add_comm 1] using (Nat.lt_log2_self (n := scale))
  have scalePositive : 0 < scale := by dsimp [scale]; omega
  have stackFits : (depth + 1) * frame < 2 ^ (constant + bits * degree) := by
    calc
      (depth + 1) * frame ≤ (coefficient * scale ^ degree) * frame :=
        Nat.mul_le_mul_right frame bounded
      _ = (coefficient * frame) * scale ^ degree := by ac_rfl
      _ < 2 ^ constant * scale ^ degree :=
        Nat.mul_lt_mul_of_pos_right frameFits (pow_pos scalePositive degree)
      _ ≤ 2 ^ constant * (2 ^ bits) ^ degree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt scaleFits) degree)
      _ = 2 ^ (constant + bits * degree) := by rw [pow_add, pow_mul]
  have exponentFits : constant + bits * degree ≤ w - 1 := by
    have smaller := Nat.mul_le_mul_right (bits + 1)
      (Nat.add_le_add_right large 1)
    change (constant + degree + 1) * (bits + 1) ≤
      (overhead + 1) * (bits + 1) at smaller
    change (overhead + 1) * (bits + 1) ≤ w at admitted
    have strict : constant + bits * degree < w := by nlinarith [smaller.trans admitted]
    omega
  have positive : 0 < w := ArrayFunction.width_pos (width_base admitted)
  have stackBelow : (depth + 1) * frame < ArrayFunction.heapLimit w :=
    stackFits.trans_le (Nat.pow_le_pow_right (by decide) exponentFits)
  have codeBelow : (lowerCode program.source program.fn).length <
      ArrayFunction.heapLimit w :=
    codeFits.trans_le (Nat.pow_le_pow_right (by decide)
      ((Nat.le_add_right constant (bits * degree)).trans exponentFits))
  have halves : ArrayFunction.heapLimit w + ArrayFunction.heapLimit w = 2 ^ w := by
    unfold ArrayFunction.heapLimit
    calc
      2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ (w - 1 + 1) := (Nat.two_pow_succ _).symm
      _ = 2 ^ w := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]
  refine ⟨positive, codeBelow.trans (ArrayFunction.heapLimit_lt_word positive), ?_⟩
  calc
    _ < ArrayFunction.heapLimit w + ArrayFunction.heapLimit w :=
      Nat.add_lt_add_left stackBelow _
    _ = 2 ^ w := halves

end Complexity.Program
