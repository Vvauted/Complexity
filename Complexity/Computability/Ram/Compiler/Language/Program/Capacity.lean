/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program

/-!
# Uniform code and stack capacity from the fixed width policy

For one selected program and one fixed call depth, code length and stack-frame
storage are constants. `capacityOverhead` chooses one logarithmic constant that
puts both below the lower-half heap limit at every admitted width. The remaining
half of the address space then accommodates the stack above that heap limit.

The constant depends on the actual emitted code and frame size, not on an input,
its answer, or an execution witness. This establishes code and stack capacity;
it does not prove source word ranges, allocation capacity or a call-depth bound.
-/

namespace Complexity.Program

open Ram.LanguageCompiler

universe u v

variable {α : Type u} {β : Type v} [Input α] [Output β]

/-- One input-independent width overhead for the selected code and fixed number
of simultaneously live call frames. -/
def capacityOverhead (program : Complexity.Program α β) (depth : Nat) : Nat :=
  Nat.log2 (max (lowerCode program.source program.fn).length
    ((depth + 1) * Ram.ABI.frameSize (programControl program.source))) + 1

variable [RamInput α]

/-- A larger uniform overhead retains code and stack capacity. This permits one
global constant to satisfy both these fixed requirements and separate resource
arguments without choosing a different constant for each input. -/
theorem capacity_of_le (program : Complexity.Program α β) (depth : Nat)
    {overhead w : Nat} {x : α} (large : capacityOverhead program depth ≤ overhead)
    (admitted : width overhead x ≤ w) :
    FunctionCapacity program.source program.fn w depth
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) := by
  have factorBound : overhead + 1 ≤ width overhead x := by
    change overhead + 1 ≤ (overhead + 1) *
      (Ram.LanguageCompiler.ArrayFunction.inputWordWidth (RamInput.words x) + 1)
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have overheadBound : overhead + 1 ≤ w := factorBound.trans admitted
  have positive : 0 < w := by omega
  let required := max (lowerCode program.source program.fn).length
    ((depth + 1) * Ram.ABI.frameSize (programControl program.source))
  have requiredFits : required < Ram.LanguageCompiler.ArrayFunction.heapLimit w := by
    have exponent : Nat.log2 required + 1 ≤ w - 1 := by
      change Nat.log2 required + 1 ≤ overhead at large
      omega
    exact (Nat.lt_log2_self (n := required)).trans_le
      (Nat.pow_le_pow_right (by decide) exponent)
  have codeFits : (lowerCode program.source program.fn).length <
      Ram.LanguageCompiler.ArrayFunction.heapLimit w :=
    (Nat.le_max_left _ _).trans_lt requiredFits
  have stackFits : (depth + 1) * Ram.ABI.frameSize (programControl program.source) <
      Ram.LanguageCompiler.ArrayFunction.heapLimit w :=
    (Nat.le_max_right _ _).trans_lt requiredFits
  have halves : Ram.LanguageCompiler.ArrayFunction.heapLimit w +
      Ram.LanguageCompiler.ArrayFunction.heapLimit w = 2 ^ w := by
    unfold Ram.LanguageCompiler.ArrayFunction.heapLimit
    calc
      2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ (w - 1 + 1) := (Nat.two_pow_succ _).symm
      _ = 2 ^ w := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]
  refine ⟨positive,
    codeFits.trans (Ram.LanguageCompiler.ArrayFunction.heapLimit_lt_word positive), ?_⟩
  calc
    _ < Ram.LanguageCompiler.ArrayFunction.heapLimit w +
        Ram.LanguageCompiler.ArrayFunction.heapLimit w := Nat.add_lt_add_left stackFits _
    _ = 2 ^ w := halves

/-- The named fixed overhead supplies capacity for every input and every width
admitted by the library's original logarithmic policy. -/
theorem capacity (program : Complexity.Program α β) (depth : Nat) {x : α} {w : Nat}
    (admitted : width (capacityOverhead program depth) x ≤ w) :
    FunctionCapacity program.source program.fn w depth
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) :=
  capacity_of_le program depth (Nat.le_refl _) admitted

/-- Code and fixed-depth stack capacity can be discharged by one uniform
implementation constant, with no restriction on mathematical inputs. -/
theorem exists_capacity_overhead (program : Complexity.Program α β) (depth : Nat) :
    ∃ overhead, ∀ (x : α) (w : Nat), width overhead x ≤ w →
      FunctionCapacity program.source program.fn w depth
        (Ram.LanguageCompiler.ArrayFunction.heapLimit w) :=
  ⟨capacityOverhead program depth, fun _ _ admitted => capacity program depth admitted⟩

end Complexity.Program
