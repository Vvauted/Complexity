/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation
import Complexity.Language.Heap.Node
import Complexity.Language.Rooted

/-!
# Linked lists as mathematical source values

The default list representation observes an optional typed node reference at
the actual heap. Nil has no node; a cons node stores one head and the actual
shared tail. Distinct roots and heap layouts may represent the same list, so
this relation is deliberately not a pure encoding or an equivalence of types.

The operation rules reuse the existing heap operations and contents proofs.
They do not introduce a second list implementation or an executable decoder.
`Representation.bufferList` remains an explicit mathematical view of contiguous
storage, separate from this linked representation.
-/

namespace Complexity.Language.Representation

/-- Ordinary lists represented by real immutable nodes with shared tails. -/
def list (kind : CellTy) : Representation (List (CellValue kind)) (.option (.node kind)) where
  Rel values root heap := NodeRef.Contents heap root values
  functional first second := first.unique second

@[simp] theorem list_rel (kind : CellTy) (values : List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap) :
    (list kind).Rel values root heap ↔ NodeRef.Contents heap root values := Iff.rfl

/-- The empty list needs no heap object. -/
theorem list_nil (kind : CellTy) (heap : Heap) :
    (list kind).Rel [] none heap := .nil

/-- Every nonempty represented list has an existing root. This does not claim
that every existing object identifier denotes a correctly typed list. -/
theorem list_rooted {kind : CellTy} {values : List (CellValue kind)}
    {root : Option (NodeRef kind)} {heap : Heap}
    (observed : (list kind).Rel values root heap) :
    ValueRooted heap (τ := .option (.node kind)) root := by
  cases root with
  | none => trivial
  | some ref => exact observed.root_lt_size

/-- One actual allocation constructs the mathematical cons and shares its tail. -/
theorem list_cons {kind : CellTy} {values : List (CellValue kind)}
    {tail : Option (NodeRef kind)} {heap : Heap} (head : CellValue kind)
    (observed : (list kind).Rel values tail heap) :
    (list kind).Rel (head :: values) (some (heap.cons head tail).1) (heap.cons head tail).2 :=
  Heap.cons_contents head observed

/-- Actual uncons follows ordinary list cases and returns the identical shared
tail, not a copied suffix or a mathematical value substituted for a runtime read. -/
theorem list_uncons {kind : CellTy} {values : List (CellValue kind)}
    {root : Option (NodeRef kind)} {heap : Heap}
    (observed : (list kind).Rel values root heap) :
    match values with
    | [] => heap.uncons root = .ok none
    | head :: rest => ∃ tail, heap.uncons root = .ok (some (head, tail)) ∧
        (list kind).Rel rest tail heap := by
  cases values <;> exact observed.uncons

/-- Preserving existing immutable nodes preserves every represented list,
including shared tails, even when mutable buffers change. -/
theorem list_mono {kind : CellTy} {values : List (CellValue kind)}
    {root : Option (NodeRef kind)} {initial finish : Heap}
    (observed : (list kind).Rel values root initial)
    (preserved : initial.ShapeExtends finish) :
    (list kind).Rel values root finish := observed.mono preserved

/-- Prefix reclamation keeps a represented list when its root survives and
the actual node links point backwards. The whole tail chain is retained. -/
theorem list_take {kind : CellTy} {values : List (CellValue kind)}
    {root : Option (NodeRef kind)} {heap : Heap} {count : Nat}
    (observed : (list kind).Rel values root heap)
    (backward : Heap.BackwardLinks Heap.nodeReferences heap)
    (retained : ∀ ref, root = some ref → ref.object < count) :
    (list kind).Rel values root (heap.take count) := observed.take backward count retained

end Complexity.Language.Representation
