/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Basic

/-!
# Native observations of linked-list emptiness

`isEmptyEval` calls the existing optional-root tag test. Its ordinary Boolean
result and unchanged heap follow from the same source total-correctness theorem.
The bridge reads no node and introduces no traversal, allocation or host callback.
-/

namespace Complexity.Language.List.IsEmpty

/-- Invoke the existing source entry with the actual optional root. -/
noncomputable def isEmptyEval (kind : CellTy) (root : Option (NodeRef kind)) :
    ExceptT Fault (StateT Heap Part) Bool :=
  (program kind).eval (entry kind) (Env.cons root Env.empty)

/-- The existing tag test returns ordinary list emptiness at exactly the same
heap. The input observation relates the actual root to the mathematical list. -/
theorem eval_exists_heap_eq (kind : CellTy) (values : List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ returned finish,
      isEmptyEval kind root heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel values.isEmpty returned finish ∧ finish = heap := by
  obtain ⟨returned, finish, evaluated, result, unchanged⟩ :=
    (total kind values).eval_spec (args := Env.cons root Env.empty)
      (initialHeap := heap) observed
  exact ⟨returned, finish, evaluated, result.symm, unchanged⟩

/-- The unchanged-heap observation also supplies the shared shape frame used
to preserve other represented values across native calls. -/
theorem eval_exists (kind : CellTy) (values : List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ returned finish,
      isEmptyEval kind root heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel values.isEmpty returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, evaluated, result, unchanged⟩ :=
    eval_exists_heap_eq kind values root heap observed
  subst finish
  exact ⟨returned, heap, evaluated, result, Heap.ShapeExtends.refl heap⟩

end Complexity.Language.List.IsEmpty
