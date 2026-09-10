/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Tree.Basic
import Complexity.Language.Heap
import Complexity.Language.Heap.Frame

/-!
# Binary trees represented by borrowed field arrays

Mathlib trees carry stable natural node identifiers. Zero denotes an empty
child. Three borrowed arrays contain keys and left/right child identifiers;
the representation records actual source-heap reads, not a copied evaluator.

The key function is a mathematical specification of the immutable labels.
`Rep` establishes the represented reads and nonzero nodes. Unique identifiers
and search-tree ordering are separate properties of the inorder list; they are
not silently assumed by the representation or required for its frame rule.
-/

namespace Complexity.Language.BufferTree

/-- Zero denotes an empty child; a nonempty tree exposes its stable root ID. -/
@[simp] def root : Tree Nat → Nat
  | .nil => 0
  | .node id _ _ => id

/-- Child-field cells belonging to this tree. Keys and unrelated node slots are
outside the permitted update footprint. -/
def linkCells (left right : Buffer .nat) (tree : Tree Nat) : Set (Nat × Nat) :=
  {location | ∃ id ∈ tree.inorder,
    location = (left.object, left.offset + id) ∨
      location = (right.object, right.offset + id)}

/-- A left child field belongs to the footprint of its represented node. -/
theorem left_mem_linkCells {left right : Buffer .nat} {tree : Tree Nat}
    {id : Nat} (member : id ∈ tree.inorder) :
    (left.object, left.offset + id) ∈ linkCells left right tree :=
  ⟨id, member, Or.inl rfl⟩

/-- A right child field belongs to the footprint of its represented node. -/
theorem right_mem_linkCells {left right : Buffer .nat} {tree : Tree Nat}
    {id : Nat} (member : id ∈ tree.inorder) :
    (right.object, right.offset + id) ∈ linkCells left right tree :=
  ⟨id, member, Or.inr rfl⟩

/-- Subtrees use only cells belonging to their enclosing tree. -/
theorem linkCells_mono {left right : Buffer .nat} {tree larger : Tree Nat}
    (included : tree.inorder ⊆ larger.inorder) :
    linkCells left right tree ⊆ linkCells left right larger := by
  rintro location ⟨id, member, field⟩
  exact ⟨id, included member, field⟩

/-- Tree rearrangement preserving inorder also preserves the allowed cells. -/
theorem linkCells_eq_of_inorder_eq {left right : Buffer .nat} {tree other : Tree Nat}
    (same : tree.inorder = other.inorder) :
    linkCells left right tree = linkCells left right other := by
  simp only [linkCells, same]

/-- The mathematical tree is represented by successful current-heap field reads.
Buffer validity and index bounds follow from those successful reads. -/
inductive Rep (key : Nat → Nat) (keys left right : Buffer .nat) (heap : Heap) :
    Tree Nat → Prop where
  | nil : Rep key keys left right heap .nil
  | node {id : Nat} {a b : Tree Nat}
      (nonzero : id ≠ 0)
      (keyRead : heap.read keys id = .ok (key id))
      (leftRead : heap.read left id = .ok (root a))
      (rightRead : heap.read right id = .ok (root b))
      (leftRep : Rep key keys left right heap a)
      (rightRep : Rep key keys left right heap b) :
      Rep key keys left right heap (.node id a b)

namespace Rep

variable {key : Nat → Nat} {keys left right : Buffer .nat} {heap finish : Heap}
variable {tree : Tree Nat}

/-- The representation of a node exposes its ordinary mathematical children
and the three successful current-heap reads. -/
theorem node_iff {id : Nat} {a b : Tree Nat} :
    Rep key keys left right heap (.node id a b) ↔
      id ≠ 0 ∧ heap.read keys id = .ok (key id) ∧
        heap.read left id = .ok (root a) ∧ heap.read right id = .ok (root b) ∧
        Rep key keys left right heap a ∧ Rep key keys left right heap b := by
  constructor
  · intro represented
    cases represented with
    | node nonzero keyRead leftRead rightRead leftRep rightRep =>
        exact ⟨nonzero, keyRead, leftRead, rightRead, leftRep, rightRep⟩
  · rintro ⟨nonzero, keyRead, leftRead, rightRead, leftRep, rightRep⟩
    exact .node nonzero keyRead leftRead rightRead leftRep rightRep

/-- All represented node IDs are nonzero, not only the root. -/
theorem node_ne_zero (represented : Rep key keys left right heap tree)
    {id : Nat} (member : id ∈ tree.inorder) : id ≠ 0 := by
  induction represented with
  | nil => simp at member
  | node nonzero keyRead leftRead rightRead leftRep rightRep ihLeft ihRight =>
      simp only [Tree.inorder, List.mem_append, List.mem_cons] at member
      rcases member with member | same | member
      · exact ihLeft member
      · subst id
        exact nonzero
      · exact ihRight member

/-- Preserving field reads on this tree's footprint preserves its representation.
Cells belonging to other nodes may change, even within the same arrays. -/
theorem congr (represented : Rep key keys left right heap tree)
    (keysEq : ∀ id ∈ tree.inorder, finish.read keys id = heap.read keys id)
    (leftEq : ∀ id ∈ tree.inorder, finish.read left id = heap.read left id)
    (rightEq : ∀ id ∈ tree.inorder, finish.read right id = heap.read right id) :
    Rep key keys left right finish tree := by
  revert keysEq leftEq rightEq
  induction represented with
  | nil => intros; exact .nil
  | @node id a b nonzero keyRead leftRead rightRead leftRep rightRep ihLeft ihRight =>
      intro keysEq leftEq rightEq
      have here : id ∈ (Tree.node id a b).inorder := by simp
      refine .node nonzero ((keysEq id here).trans keyRead)
        ((leftEq id here).trans leftRead) ((rightEq id here).trans rightRead) ?_ ?_
      · exact ihLeft
          (fun node member => keysEq node (by simp [member]))
          (fun node member => leftEq node (by simp [member]))
          (fun node member => rightEq node (by simp [member]))
      · exact ihRight
          (fun node member => keysEq node (by simp [member]))
          (fun node member => leftEq node (by simp [member]))
          (fun node member => rightEq node (by simp [member]))

/-- Every represented node has its specified key in the current heap. -/
theorem read_key (represented : Rep key keys left right heap tree)
    {id : Nat} (member : id ∈ tree.inorder) : heap.read keys id = .ok (key id) := by
  induction represented with
  | nil => simp at member
  | node nonzero keyRead leftRead rightRead leftRep rightRep ihLeft ihRight =>
      simp only [Tree.inorder, List.mem_append, List.mem_cons] at member
      rcases member with member | same | member
      · exact ihLeft member
      · subst id
        exact keyRead
      · exact ihRight member

/-- Every represented identifier is a legal index in all three field arrays.
These are consequences of the representation, not extra access hypotheses. -/
theorem index_lt (represented : Rep key keys left right heap tree)
    {id : Nat} (member : id ∈ tree.inorder) :
    id < keys.length ∧ id < left.length ∧ id < right.length := by
  induction represented with
  | nil => simp at member
  | node nonzero keyRead leftRead rightRead leftRep rightRep ihLeft ihRight =>
      simp only [Tree.inorder, List.mem_append, List.mem_cons] at member
      rcases member with member | same | member
      · exact ihLeft member
      · subst id
        obtain ⟨_, _, _, keyBound, _⟩ := Heap.read_eq_ok_iff.mp keyRead
        obtain ⟨_, _, _, leftBound, _⟩ := Heap.read_eq_ok_iff.mp leftRead
        obtain ⟨_, _, _, rightBound, _⟩ := Heap.read_eq_ok_iff.mp rightRead
        exact ⟨keyBound, leftBound, rightBound⟩
      · exact ihRight member

/-- A valid key slot is outside the child-field update footprint. -/
theorem key_not_mem_linkCells (represented : Rep key keys left right heap tree)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    {id : Nat} (bound : id < keys.length) :
    (keys.object, keys.offset + id) ∉ linkCells left right tree := by
  rintro ⟨node, member, same | same⟩
  · exact keysLeft.location_ne bound (represented.index_lt member).2.1 same
  · exact keysRight.location_ne bound (represented.index_lt member).2.2 same

/-- A left slot of a different node is outside the represented subtree. -/
theorem left_not_mem_linkCells (represented : Rep key keys left right heap tree)
    (separated : left.Disjoint right) {id : Nat} (bound : id < left.length)
    (outside : id ∉ tree.inorder) :
    (left.object, left.offset + id) ∉ linkCells left right tree := by
  rintro ⟨node, member, same | same⟩
  · have ids : id = node := by
      have := congrArg Prod.snd same
      simpa only [Nat.add_left_cancel_iff] using this
    exact outside (ids.symm ▸ member)
  · exact separated.location_ne bound (represented.index_lt member).2.2 same

/-- A right slot of a different node is outside the represented subtree. -/
theorem right_not_mem_linkCells (represented : Rep key keys left right heap tree)
    (separated : left.Disjoint right) {id : Nat} (bound : id < right.length)
    (outside : id ∉ tree.inorder) :
    (right.object, right.offset + id) ∉ linkCells left right tree := by
  rintro ⟨node, member, same | same⟩
  · exact separated.symm.location_ne bound (represented.index_lt member).2.1 same
  · have ids : id = node := by
      have := congrArg Prod.snd same
      simpa only [Nat.add_left_cancel_iff] using this
    exact outside (ids.symm ▸ member)

/-- Updating one subtree preserves the representation of disjoint nodes in the
same arrays. Their keys and child links are transported through the actual heap. -/
theorem frame (represented : Rep key keys left right heap tree) {changed : Tree Nat}
    (changedRep : Rep key keys left right heap changed)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right)
    (nodes : List.Disjoint tree.inorder changed.inorder)
    (preserved : Heap.PreservesOutside (linkCells left right changed) heap finish) :
    Rep key keys left right finish tree := by
  apply represented.congr
  · intro id member
    exact preserved.read_eq keys id
      (changedRep.key_not_mem_linkCells keysLeft keysRight (represented.index_lt member).1)
  · intro id member
    exact preserved.read_eq left id
      (changedRep.left_not_mem_linkCells leftRight (represented.index_lt member).2.1
        (nodes member))
  · intro id member
    exact preserved.read_eq right id
      (changedRep.right_not_mem_linkCells leftRight (represented.index_lt member).2.2
        (nodes member))

end Rep
end Complexity.Language.BufferTree
