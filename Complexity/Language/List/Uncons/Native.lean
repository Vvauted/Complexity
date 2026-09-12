/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Uncons

/-!
# Native observations of one actual list decomposition

`unconsEval` binds a root argument to the existing `List.Uncons.program` entry.
Its optional head and tail use exactly `List.Uncons.resultRepresentation`.
A present node is read once and returns its stored shared tail; this bridge
does not perform another lookup, traverse the list or allocate a replacement.

The evaluation theorem reuses source total correctness and retains its exact
unchanged-heap frame. A shape-extension consequence composes with the same
native call interfaces as allocating operations.
-/

namespace Complexity.Language.List.Uncons

/-- Invoke the existing source entry with its actual optional node reference. -/
noncomputable def unconsEval (kind : CellTy) (root : Option (NodeRef kind)) :
    ExceptT Fault (StateT Heap Part)
      (Value (.option (.prod kind.toTy (.option (.node kind))))) :=
  (program kind).eval (entry kind) (Env.cons root Env.empty)

/-- The actual decomposition returns the ordinary optional head/tail view at
the unchanged heap, retaining the complete frame of the source contract. -/
theorem eval_exists_heap_eq (kind : CellTy) (values : List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ returned finish,
      unconsEval kind root heap = Part.some (.ok returned, finish) ∧
      (resultRepresentation kind).Rel
        (values.head?.map (fun head => (head, values.tail))) returned finish ∧
      finish = heap := by
  obtain ⟨returned, finish, evaluated, related, unchanged⟩ :=
    (total kind values).eval_spec (args := Env.cons root Env.empty)
      (initialHeap := heap) observed
  exact ⟨returned, finish, evaluated, related, unchanged⟩

/-- The existing evaluation and result observation also supply the shape frame
used to retain other immutable observations across native calls. -/
theorem eval_exists (kind : CellTy) (values : List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ returned finish,
      unconsEval kind root heap = Part.some (.ok returned, finish) ∧
      (resultRepresentation kind).Rel
        (values.head?.map (fun head => (head, values.tail))) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, evaluated, related, unchanged⟩ :=
    eval_exists_heap_eq kind values root heap observed
  subst finish
  exact ⟨returned, heap, evaluated, related, Heap.ShapeExtends.refl heap⟩

end Complexity.Language.List.Uncons
