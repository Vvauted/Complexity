/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Init.Data.List.OfFn

/-!
# Describing existing scratch storage and shared call memory

A bounded interval of the total RAM memory has mathematical list contents,
even when no particular values are specified for scratch storage. The list
below is a ghost observation using standard `List.ofFn`, not an allocation,
initialization, copying operation or instruction available to a RAM program.

Function entry and return share the same memory, so array assertions transport
without repeating elementwise lookup proofs at every recursive call.
-/

namespace Ram.ArrayRep

/-- Standard finite-function lists describe the current cells of a fitting
interval. No assumption about the cells' values is needed. -/
theorem ofFn {mem : Word w → Word w} {base : Word w} {length : Nat}
    (hfit : base.toNat + length ≤ 2 ^ w) :
    ArrayRep mem base (List.ofFn fun i : Fin length => mem (arrayAddr base i.val)) := by
  refine ⟨by simpa only [List.length_ofFn] using hfit, ?_⟩
  intro i hi
  simp only [List.getElem_ofFn]

end Ram.ArrayRep

namespace Ram.Source.ArrayAt

/-- An allocated extent still has some contents after memory changes. This
forgets values only; it neither extends the interval nor claims preservation. -/
theorem exists_contents {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {before : State w} (h : ArrayAt heapLimit base xs before) (after : State w) :
    ∃ ys, ys.length = xs.length ∧ ArrayAt heapLimit base ys after := by
  refine ⟨List.ofFn (fun i : Fin xs.length => after.mem (arrayAddr base i.val)),
    List.length_ofFn, ArrayRep.ofFn h.1.fits, ?_⟩
  simpa only [List.length_ofFn] using h.2

/-- Callee entry changes registers, not the shared array memory. -/
theorem enter {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) (args : List (Word w)) :
    ArrayAt heapLimit base xs (s.enter args) := h

/-- Return retains the final callee heap while restoring caller registers. -/
theorem leave {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {callee : State w} (h : ArrayAt heapLimit base xs callee)
    (caller : State w) (dsts : List Reg) (results : List Expr) :
    ArrayAt heapLimit base xs (caller.leave callee dsts results) := by
  simpa only [ArrayAt, State.leave_mem] using h

end Ram.Source.ArrayAt
