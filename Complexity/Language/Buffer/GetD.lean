/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.RepresentedFunction
import Complexity.Language.Buffer.Copy

/-!
# Array lookup with a default

The source functions check the actual buffer length before reading a cell.
Their mathematical observation is Lean's `Array.getD`, including the out-of-bounds
case. A valid contents observation suffices; the caller supplies no index bound.
Both branches preserve the entire heap and all previously observed arrays.
-/

namespace Complexity.Language.Buffer

source_program% GetD where
  def getNat (source : Buffer Nat) (index : Nat) (fallback : Nat) : Nat := do
    if index < source.length then
      let result ← source.get index
      return result
    else
      return fallback

  def getBool (source : Buffer Bool) (index : Nat) (fallback : Bool) : Bool := do
    if index < source.length then
      let result ← source.get index
      return result
    else
      return fallback

namespace GetD

private theorem readM_getD {kind : CellTy} (values : Array (CellValue kind))
    (index : Nat) (fallback : CellValue kind) (source : Buffer kind) (heap : Heap)
    (observed : source.Contents heap values) :
    (if index < source.length then source.readM index else pure fallback) heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  by_cases bound : index < values.size
  · have available : index < source.length := by simpa only [observed.size_eq] using bound
    simpa [available, Array.getD, bound] using readM_eq_ok (observed.read bound)
  · have unavailable : ¬ index < source.length := by simpa only [observed.size_eq] using bound
    simp only [if_neg unavailable, Array.getD, dif_neg bound]
    rfl

/-- Natural lookup returns the ordinary array element or the supplied default,
without allocation or modification of any observed storage. -/
theorem getNat_eval (values : Array Nat) (index fallback : Nat)
    (source : Buffer .nat) (heap : Heap)
    (observed : (Representation.array .nat).Rel values source heap) :
    getNat source index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getNat_eq] using readM_getD (kind := .nat) values index fallback source heap observed

/-- Boolean lookup uses the same bounds check and actual read as natural lookup. -/
theorem getBool_eval (values : Array Bool) (index : Nat) (fallback : Bool)
    (source : Buffer .bool) (heap : Heap)
    (observed : (Representation.array .bool).Rel values source heap) :
    getBool source index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getBool_eq] using readM_getD (kind := .bool) values index fallback source heap observed

/-- Natural array, index and default observed at the same invocation heap. -/
def natRepresentation :
    FunctionRepresentation (Array Nat × Nat × Nat) (fun _ => Nat) signatures[getNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons (Representation.array .nat)
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single Representation.nat)))
    (fun _ => Representation.nat)

/-- Boolean array, index and default observed at the same invocation heap. -/
def boolRepresentation :
    FunctionRepresentation (Array Bool × Nat × Bool) (fun _ => Bool) signatures[getBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons (Representation.array .bool)
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single Representation.bool)))
    (fun _ => Representation.bool)

/-- Natural lookup refines Lean's total defaulted array access. -/
theorem getNat_refines :
    RepresentedFunction.Refines program getNatId natRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getNat_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getNat_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Boolean lookup refines Lean's total defaulted array access. -/
theorem getBool_refines :
    RepresentedFunction.Refines program getBoolId boolRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getBool_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getBool_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- The natural read preserves all old array observations, including aliases. -/
theorem getNat_eval_exists_preserving (values : Array Nat) (index fallback : Nat)
    (source : Buffer .nat) (heap : Heap)
    (observed : (Representation.array .nat).Rel values source heap) :
    ∃ returned finish, getNat source index fallback heap = Part.some (.ok returned, finish) ∧
      Representation.nat.Rel (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getNat_eval values index fallback source heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The Boolean read preserves all old array observations, including aliases. -/
theorem getBool_eval_exists_preserving (values : Array Bool) (index : Nat) (fallback : Bool)
    (source : Buffer .bool) (heap : Heap)
    (observed : (Representation.array .bool).Rel values source heap) :
    ∃ returned finish, getBool source index fallback heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getBool_eval values index fallback source heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- Natural lookup supplies the standard represented-call shape frame. -/
theorem getNat_eval_exists (values : Array Nat) (index fallback : Nat)
    (source : Buffer .nat) (heap : Heap)
    (observed : (Representation.array .nat).Rel values source heap) :
    ∃ returned finish, getNat source index fallback heap = Part.some (.ok returned, finish) ∧
      Representation.nat.Rel (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getNat_eval values index fallback source heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

/-- Boolean lookup supplies the standard represented-call shape frame. -/
theorem getBool_eval_exists (values : Array Bool) (index : Nat) (fallback : Bool)
    (source : Buffer .bool) (heap : Heap)
    (observed : (Representation.array .bool).Rel values source heap) :
    ∃ returned finish, getBool source index fallback heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getBool_eval values index fallback source heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

end GetD
end Complexity.Language.Buffer
