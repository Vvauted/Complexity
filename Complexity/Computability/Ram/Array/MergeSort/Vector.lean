/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.StateM
import Complexity.Computability.Ram.Verification.StateM.Model
import Complexity.Computability.Ram.Verification.StateM.Subtype
import Mathlib.Data.Vector.Basic

/-!
# Native fixed-length models of the existing merge-sort call

The existing list model preserves length, so it restricts to mathlib's
`List.Vector` without a runtime check. `Equiv.vectorEquivFin` then presents
that same native state transformation as a finite function, for example a
matrix row. Both interfaces use ordinary `modify`; neither introduces a new
RAM program or a host-side sorting primitive.

The callable refinements retain the full original shared-state assertion,
including scratch storage, the two-buffer memory frame and I/O, together with
the zero return value and the caller's non-destination registers. Only the
mathematical representation changes; running-time proofs remain separate.
-/

namespace Ram.Source.Array.MergeSort

/-- Canonical sorting on mathlib's fixed-length lists. -/
def sortedVector {n : Nat} (values : List.Vector (Word w) n) :
    List.Vector (Word w) n :=
  ⟨sorted values.val, (length_sorted values.val).trans values.property⟩

/-- The same canonical result viewed through a finite index, not a new
algorithm or a change to the physical array layout. -/
def sortedFin {n : Nat} (values : Fin n → Word w) : Fin n → Word w :=
  (sortedVector (List.Vector.ofFn values)).get

/-- Ordinary list theorems about the canonical result apply directly to the
finite-function model, including its sorted-permutation specification. -/
@[simp] theorem ofFn_sortedFin {n : Nat} (values : Fin n → Word w) :
    List.ofFn (sortedFin values) = sorted (List.ofFn values) := by
  rw [← List.Vector.toList_ofFn (sortedFin values)]
  change (List.Vector.ofFn ((sortedVector (List.Vector.ofFn values)).get)).toList = _
  rw [List.Vector.ofFn_get]
  change sorted (List.Vector.ofFn values).toList = _
  rw [List.Vector.toList_ofFn]

variable {w heapLimit selfFn : Nat} {functions : Program}

/-- The existing callable list implementation also implements native sorting
of a fixed-length vector. Length preservation is supplied by `length_sorted`;
the input needs no repeated length assertion. -/
theorem call_vector_stateM_refines {base scratch : Word w}
    (length : Nat) (original : State w) (dst : Reg) (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    Refines functions heapLimit (Nat.clog 2 length + 1)
      (.call dst selfFn [.var 0, .var 1, .var 2])
      (fun (values : List.Vector (Word w) length) entry =>
        Pre heapLimit base scratch values.val entry ∧ entry = original)
      (fun (result : PUnit × List.Vector (Word w) length) finish => finish.regs dst = 0 ∧
        SharedStateRep heapLimit base scratch length original result.2.val
          finish.mem finish.input finish.outputRev ∧
        ∀ r, r ≠ dst → finish.regs r = original.regs r)
      (modify sortedVector : StateM (List.Vector (Word w) length) PUnit).run := by
  have restricted := (call_stateM_refines (heapLimit := heapLimit)
    (base := base) (scratch := scratch) length original dst hw lookup).stateM_subtype
      (fun xs => xs.length = length)
      (fun xs hlength => (length_sorted xs).trans hlength)
  rintro values entry ⟨pre, same⟩
  exact restricted values entry ⟨values.property, pre, same⟩

/-- One fixed RAM call implements native sorting of a finite function. This
interface composes directly with finite-indexed arrays and matrix rows while
retaining every shared-state and caller-register guarantee of the list call. -/
theorem call_fin_stateM_refines {base scratch : Word w}
    (length : Nat) (original : State w) (dst : Reg) (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    Refines functions heapLimit (Nat.clog 2 length + 1)
      (.call dst selfFn [.var 0, .var 1, .var 2])
      (fun (values : Fin length → Word w) entry =>
        Pre heapLimit base scratch (List.ofFn values) entry ∧ entry = original)
      (fun (result : PUnit × (Fin length → Word w)) finish => finish.regs dst = 0 ∧
        SharedStateRep heapLimit base scratch length original (List.ofFn result.2)
          finish.mem finish.input finish.outputRev ∧
        ∀ r, r ≠ dst → finish.regs r = original.regs r)
      (modify sortedFin : StateM (Fin length → Word w) PUnit).run := by
  have transported := (call_vector_stateM_refines (heapLimit := heapLimit)
    (base := base) (scratch := scratch) length original dst hw lookup).stateM_equiv
      (Equiv.vectorEquivFin (Word w) length) (Equiv.refl PUnit)
  have inverse (values : Fin length → Word w) :
      ((Equiv.vectorEquivFin (Word w) length).symm values).val = List.ofFn values :=
    List.Vector.toList_ofFn values
  simpa only [inverse] using transported.congr_fun
    (g := (modify sortedFin : StateM (Fin length → Word w) PUnit).run) (fun _ => rfl)

end Ram.Source.Array.MergeSort
