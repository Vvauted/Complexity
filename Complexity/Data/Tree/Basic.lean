/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Tree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Inorder views and binary-tree rotations

These mathematical views extend mathlib's `Tree`. A rotation preserves the
complete inorder list, including repeated labels; ordering and uniqueness
properties can therefore be transported without reproving them for each
rotation. The definitions are mathematical tree transformations, not a memory
representation, executable splay implementation or assignment of machine costs.
-/

namespace Tree

variable {α : Type*}

/-- The labels in left-subtree, root, right-subtree order. -/
@[simp] def inorder : Tree α → List α
  | .nil => []
  | .node value left right => left.inorder ++ value :: right.inorder

/-- The root label, with no arbitrary value assigned to an empty tree. -/
@[simp] def root? : Tree α → Option α
  | .nil => none
  | .node value _ _ => some value

/-- Every left-child label occurs in the enclosing tree. -/
theorem inorder_left_subset (id : α) (a b : Tree α) :
    a.inorder ⊆ (node id a b).inorder := by
  intro value member
  exact List.mem_append_left _ member

/-- Every right-child label occurs in the enclosing tree. -/
theorem inorder_right_subset (id : α) (a b : Tree α) :
    b.inorder ⊆ (node id a b).inorder := by
  intro value member
  exact List.mem_append_right _ (List.mem_cons_of_mem id member)

/-- Inorder traversal visits each internal node exactly once. -/
@[simp] theorem length_inorder (tree : Tree α) : tree.inorder.length = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node value left right ihLeft ihRight =>
      simp only [inorder, List.length_append, List.length_cons, ihLeft, ihRight, numNodes]
      omega

/-- Inorder equality preserves the mathematical number of nodes. -/
theorem numNodes_eq_of_inorder_eq {left right : Tree α}
    (same : left.inorder = right.inorder) : left.numNodes = right.numNodes := by
  simpa only [length_inorder] using congrArg List.length same

/-- A tree with unique labels has unique labels in its left child. -/
theorem nodup_inorder_left {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) : a.inorder.Nodup :=
  (List.nodup_append.mp unique).1

/-- A tree with unique labels has unique labels in its right child. -/
theorem nodup_inorder_right {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) : b.inorder.Nodup :=
  (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).2

/-- The root of a uniquely labelled tree does not occur in either child. -/
theorem root_not_mem_inorder_children {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) :
    id ∉ a.inorder ∧ id ∉ b.inorder := by
  have absent := (List.nodup_cons.mp (List.nodup_middle.mp unique)).1
  simpa only [List.mem_append, not_or] using absent

/-- The root is absent from the left child of a uniquely labelled tree. -/
theorem root_not_mem_inorder_left {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) : id ∉ a.inorder :=
  (root_not_mem_inorder_children unique).1

/-- The root is absent from the right child of a uniquely labelled tree. -/
theorem root_not_mem_inorder_right {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) : id ∉ b.inorder :=
  (root_not_mem_inorder_children unique).2

/-- The children of a uniquely labelled tree have disjoint label sets. -/
theorem disjoint_inorder_children {id : α} {a b : Tree α}
    (unique : (node id a b).inorder.Nodup) : List.Disjoint a.inorder b.inorder := by
  intro value inLeft inRight
  exact (List.nodup_append'.mp unique).2.2 inLeft (List.mem_cons_of_mem id inRight)

/-- Rotate a nonempty right child to the root. Without such a child, do nothing. -/
def rotateLeft : Tree α → Tree α
  | .node x a (.node y b c) => .node y (.node x a b) c
  | tree => tree

/-- Rotate a nonempty left child to the root. Without such a child, do nothing. -/
def rotateRight : Tree α → Tree α
  | .node y (.node x a b) c => .node x a (.node y b c)
  | tree => tree

@[simp] theorem rotateLeft_node (x y : α) (a b c : Tree α) :
    (node x a (node y b c)).rotateLeft = node y (node x a b) c := rfl

@[simp] theorem rotateRight_node (x y : α) (a b c : Tree α) :
    (node y (node x a b) c).rotateRight = node x a (node y b c) := rfl

/-- A left rotation retains every label in its original inorder position. -/
@[simp] theorem inorder_rotateLeft (tree : Tree α) :
    tree.rotateLeft.inorder = tree.inorder := by
  cases tree with
  | nil => rfl
  | node x a right =>
      cases right <;> simp [rotateLeft, List.append_assoc]

/-- A right rotation retains every label in its original inorder position. -/
@[simp] theorem inorder_rotateRight (tree : Tree α) :
    tree.rotateRight.inorder = tree.inorder := by
  cases tree with
  | nil => rfl
  | node y left c =>
      cases left <;> simp [rotateRight, List.append_assoc]

@[simp] theorem numNodes_rotateLeft (tree : Tree α) :
    tree.rotateLeft.numNodes = tree.numNodes :=
  numNodes_eq_of_inorder_eq (inorder_rotateLeft tree)

@[simp] theorem numNodes_rotateRight (tree : Tree α) :
    tree.rotateRight.numNodes = tree.numNodes :=
  numNodes_eq_of_inorder_eq (inorder_rotateRight tree)

end Tree
