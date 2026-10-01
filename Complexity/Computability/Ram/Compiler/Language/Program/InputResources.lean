/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program

/-!
# Scalar ranges from the registered input heap

Any successful read of the fixed input heap has the range already proved by its
registered RAM representation. Callers need not unfold a record's word encoding
or restate bounds on every array cell. The observation must concern that actual
heap; subsequent mutations require their own preservation or realization proof.
-/

namespace Complexity.Program.RamInput

open Language Ram.LanguageCompiler

universe u
variable {α : Type u} [Input α] [RamInput α]

/-- The registered input arena bounds every actually observed scalar read. -/
theorem read_fits (x : α) {overhead w : Nat} (admitted : width overhead x ≤ w)
    {kind : CellTy} {buffer : Buffer kind} {index : Nat} {value : CellValue kind}
    (loaded : (Input.heap x).read buffer index = .ok value) :
    ValueFits w (kind.toValue value) := by
  have bounded := ((RamInput.arena x w (width_base admitted)).heapRep.read loaded).2.2
  cases kind <;> exact bounded

/-- Ordinary defaulted access inherits its selected cell's input range; only
the separately supplied fallback needs a separate bound. -/
theorem getD_fits (x : α) {overhead w : Nat} (admitted : width overhead x ≤ w)
    {kind : CellTy} {buffer : Buffer kind} {values : Array (CellValue kind)}
    (observed : buffer.Contents (Input.heap x) values) (index : Nat)
    (fallback : CellValue kind) (fallbackFits : ValueFits w (kind.toValue fallback)) :
    ValueFits w (kind.toValue (values.getD index fallback)) := by
  by_cases inside : index < values.size
  · simpa only [Array.getD, dif_pos inside] using read_fits x admitted (observed.read inside)
  · simpa only [Array.getD, dif_neg inside] using fallbackFits

end Complexity.Program.RamInput
