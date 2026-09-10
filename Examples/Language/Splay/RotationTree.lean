/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Rotation
import Complexity.Language.Heap.Tree.Update
import Mathlib.Data.List.Nodup

/-!
# Splay rotations preserve represented mathematical trees

The operational two-write contracts are lifted to mathlib's tree rotations.
The shared node-update rules supply memory safety and preserve the unchanged
subtrees. Uniqueness of the original inorder list supplies the no-cycle facts;
no different-object assumption is imposed on the three field arrays.

Each theorem retains the actual source evaluation and the cell-local frame of
its original tree. Recursive callers may therefore protect other nodes in the
same arrays without reopening the rotation's implementation.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

/-- A real right rotation has the ordinary tree-rotation result and changes
only links of the original tree. Read success from the representation supplies
every write's index and view-validity condition. -/
theorem rotateRight_rep (key : Nat → Nat) (keys left right : Buffer .nat)
    (x y : Nat) (a b c : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node y (.node x a b) c))
    (unique : (Tree.node y (.node x a b) c).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) :
    ∃ finish,
      Implementation.rotateRight left right y heap = Part.some (.ok x, finish) ∧
      Rep key keys left right finish ((Tree.node y (.node x a b) c).rotateRight) ∧
      Heap.PreservesOutside (linkCells left right (.node y (.node x a b) c)) heap finish := by
  have original := represented
  have yAbsent := Tree.root_not_mem_inorder_children unique
  have rotatedUnique : (Tree.node x a (.node y b c)).inorder.Nodup := by
    simpa only [Tree.rotateRight_node] using
      (Tree.inorder_rotateRight (Tree.node y (.node x a b) c)).symm ▸ unique
  have xAbsent := Tree.root_not_mem_inorder_children rotatedUnique
  have yNotB : y ∉ b.inorder := fun member => yAbsent.1 (by simp [member])
  cases represented with
  | node yNonzero yKey yLeft yRight leftRep cRep =>
      have originalLeft := leftRep
      cases leftRep with
      | node xNonzero xKey xLeft xRight aRep bRep =>
          obtain ⟨between, writeLeft, newRight⟩ :=
            original.write_left_exists bRep yNotB yAbsent.2 keysLeft.symm leftRight
          have retainedLeft := originalLeft.write_left_of_not_mem writeLeft
            yAbsent.1 keysLeft.symm leftRight
          obtain ⟨finish, writeRight, rotated⟩ :=
            retainedLeft.write_right_exists newRight xAbsent.1 xAbsent.2
              keysRight.symm leftRight.symm
          refine ⟨finish, rotateRight_eval_of_accesses left right y x (root b)
            yLeft xRight writeLeft writeRight, rotated, ?_⟩
          exact (Heap.PreservesOutside.write writeLeft
            (left_mem_linkCells (by simp))).trans
              (Heap.PreservesOutside.write writeRight (right_mem_linkCells (by simp)))

/-- The symmetric real left rotation retains its mathematical tree result and
the same precise outside-tree frame, including same-object disjoint columns. -/
theorem rotateLeft_rep (key : Nat → Nat) (keys left right : Buffer .nat)
    (x y : Nat) (a b c : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node x a (.node y b c)))
    (unique : (Tree.node x a (.node y b c)).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) :
    ∃ finish,
      Implementation.rotateLeft left right x heap = Part.some (.ok y, finish) ∧
      Rep key keys left right finish ((Tree.node x a (.node y b c)).rotateLeft) ∧
      Heap.PreservesOutside (linkCells left right (.node x a (.node y b c))) heap finish := by
  have original := represented
  have xAbsent := Tree.root_not_mem_inorder_children unique
  have rotatedUnique : (Tree.node y (.node x a b) c).inorder.Nodup := by
    simpa only [Tree.rotateLeft_node] using
      (Tree.inorder_rotateLeft (Tree.node x a (.node y b c))).symm ▸ unique
  have yAbsent := Tree.root_not_mem_inorder_children rotatedUnique
  have xNotB : x ∉ b.inorder := fun member => xAbsent.2 (by simp [member])
  cases represented with
  | node xNonzero xKey xLeft xRight aRep rightRep =>
      have originalRight := rightRep
      cases rightRep with
      | node yNonzero yKey yLeft yRight bRep cRep =>
          obtain ⟨between, writeRight, newLeft⟩ :=
            original.write_right_exists bRep xAbsent.1 xNotB
              keysRight.symm leftRight.symm
          have retainedRight := originalRight.write_right_of_not_mem writeRight
            xAbsent.2 keysRight.symm leftRight.symm
          obtain ⟨finish, writeLeft, rotated⟩ :=
            retainedRight.write_left_exists newLeft yAbsent.1 yAbsent.2
              keysLeft.symm leftRight
          refine ⟨finish, rotateLeft_eval_of_accesses left right x y (root b)
            xRight yLeft writeRight writeLeft, rotated, ?_⟩
          exact (Heap.PreservesOutside.write writeRight
            (right_mem_linkCells (by simp))).trans
              (Heap.PreservesOutside.write writeLeft (left_mem_linkCells (by simp)))

end Complexity.Language.Examples.Splay
