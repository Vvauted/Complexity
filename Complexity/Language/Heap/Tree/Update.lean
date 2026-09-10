/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Tree
import Complexity.Language.Heap.Frame

/-!
# Updating represented tree links

A link write outside a tree's node identifiers preserves its representation.
Updating a node itself rebuilds its mathematical tree once the new child is
represented and both surviving children exclude that node. These are the real
heap writes used by source programs, not a separate tree evaluator.

Field columns need disjoint views, not distinct heap objects. Successful reads
already contained in the representation supply the access conditions for
writing a node's new child link.
-/

namespace Complexity.Language.BufferTree.Rep

variable {key : Nat → Nat} {keys left right : Buffer .nat} {heap finish : Heap}
variable {tree : Tree Nat} {id value : Nat}

/-- Writing another node's left link preserves this entire represented tree.
Other nodes can occupy the same column arrays. -/
theorem write_left_of_not_mem (represented : Rep key keys left right heap tree)
    (written : heap.write left id value = .ok finish) (absent : id ∉ tree.inorder)
    (keysDisjoint : left.Disjoint keys) (rightDisjoint : left.Disjoint right) :
    Rep key keys left right finish tree := by
  apply represented.congr
  · intro node _
    exact Heap.read_write_of_disjoint written keysDisjoint
  · intro node member
    apply Heap.read_write_of_ne_cell written rfl
    intro sameCell
    have same : id = node := Nat.add_left_cancel sameCell
    exact absent (same.symm ▸ member)
  · intro node _
    exact Heap.read_write_of_disjoint written rightDisjoint

/-- Writing another node's right link preserves this entire represented tree. -/
theorem write_right_of_not_mem (represented : Rep key keys left right heap tree)
    (written : heap.write right id value = .ok finish) (absent : id ∉ tree.inorder)
    (keysDisjoint : right.Disjoint keys) (leftDisjoint : right.Disjoint left) :
    Rep key keys left right finish tree := by
  apply represented.congr
  · intro node _
    exact Heap.read_write_of_disjoint written keysDisjoint
  · intro node _
    exact Heap.read_write_of_disjoint written leftDisjoint
  · intro node member
    apply Heap.read_write_of_ne_cell written rfl
    intro sameCell
    have same : id = node := Nat.add_left_cancel sameCell
    exact absent (same.symm ▸ member)

/-- Replacing a node's left link retains its key and right link, and frames both
surviving subtrees. Excluding the parent from those subtrees prevents cycles. -/
theorem node_write_left {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (written : heap.write left id (root next) = .ok finish)
    (nextRep : Rep key keys left right heap next)
    (nextAbsent : id ∉ next.inorder) (rightAbsent : id ∉ b.inorder)
    (keysDisjoint : left.Disjoint keys) (rightDisjoint : left.Disjoint right) :
    Rep key keys left right finish (.node id next b) := by
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      exact .node nonzero
        ((Heap.read_write_of_disjoint written keysDisjoint).trans keyRead)
        (Heap.read_write written)
        ((Heap.read_write_of_disjoint written rightDisjoint).trans rightRead)
        (nextRep.write_left_of_not_mem written nextAbsent keysDisjoint rightDisjoint)
        (rightRep.write_left_of_not_mem written rightAbsent keysDisjoint rightDisjoint)

/-- Replacing a node's right link retains its key and left link, and frames both
surviving subtrees. -/
theorem node_write_right {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (written : heap.write right id (root next) = .ok finish)
    (nextRep : Rep key keys left right heap next)
    (leftAbsent : id ∉ a.inorder) (nextAbsent : id ∉ next.inorder)
    (keysDisjoint : right.Disjoint keys) (leftDisjoint : right.Disjoint left) :
    Rep key keys left right finish (.node id a next) := by
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      exact .node nonzero
        ((Heap.read_write_of_disjoint written keysDisjoint).trans keyRead)
        ((Heap.read_write_of_disjoint written leftDisjoint).trans leftRead)
        (Heap.read_write written)
        (leftRep.write_right_of_not_mem written leftAbsent keysDisjoint leftDisjoint)
        (nextRep.write_right_of_not_mem written nextAbsent keysDisjoint leftDisjoint)

/-- A represented node admits a real left-link write and a rebuilt tree. The
old link's successful read discharges all write-access conditions. -/
theorem write_left_exists {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (nextRep : Rep key keys left right heap next)
    (nextAbsent : id ∉ next.inorder) (rightAbsent : id ∉ b.inorder)
    (keysDisjoint : left.Disjoint keys) (rightDisjoint : left.Disjoint right) :
    ∃ finish, heap.write left id (root next) = .ok finish ∧
      Rep key keys left right finish (.node id next b) := by
  have readLeft : heap.read left id = .ok (root a) := by
    cases represented with
    | node nonzero keyRead leftRead rightRead leftRep rightRep => exact leftRead
  obtain ⟨finish, written⟩ := Heap.write_exists_of_read readLeft (root next)
  exact ⟨finish, written, represented.node_write_left written nextRep
    nextAbsent rightAbsent keysDisjoint rightDisjoint⟩

/-- A represented node admits the symmetric real right-link write, with no
additional index proof beyond its existing representation. -/
theorem write_right_exists {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (nextRep : Rep key keys left right heap next)
    (leftAbsent : id ∉ a.inorder) (nextAbsent : id ∉ next.inorder)
    (keysDisjoint : right.Disjoint keys) (leftDisjoint : right.Disjoint left) :
    ∃ finish, heap.write right id (root next) = .ok finish ∧
      Rep key keys left right finish (.node id a next) := by
  have readRight : heap.read right id = .ok (root b) := by
    cases represented with
    | node nonzero keyRead leftRead rightRead leftRep rightRep => exact rightRead
  obtain ⟨finish, written⟩ := Heap.write_exists_of_read readRight (root next)
  exact ⟨finish, written, represented.node_write_right written nextRep
    leftAbsent nextAbsent keysDisjoint leftDisjoint⟩

private theorem node_reads_frame {a b changed : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (changedRep : Rep key keys left right heap changed) (absent : id ∉ changed.inorder)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right)
    (preserved : Heap.PreservesOutside (linkCells left right changed) heap finish) :
    finish.read keys id = .ok (key id) ∧
      finish.read left id = .ok (root a) ∧ finish.read right id = .ok (root b) := by
  have bounds := represented.index_lt (id := id) (by simp)
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      exact ⟨(preserved.read_eq keys id
        (changedRep.key_not_mem_linkCells keysLeft keysRight bounds.1)).trans keyRead,
        (preserved.read_eq left id
          (changedRep.left_not_mem_linkCells leftRight bounds.2.1 absent)).trans leftRead,
        (preserved.read_eq right id
          (changedRep.right_not_mem_linkCells leftRight bounds.2.2 absent)).trans rightRead⟩

/-- Reassemble a parent after changes confined to its left subtree when that
subtree retains its root. This performs no additional heap operation. -/
theorem rebuild_left {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (unique : (Tree.node id a b).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (returnedRep : Rep key keys left right finish next)
    (sameRoot : root next = root a)
    (preserved : Heap.PreservesOutside (linkCells left right a) heap finish) :
    Rep key keys left right finish (.node id next b) := by
  have absent := Tree.root_not_mem_inorder_left unique
  have nodes := List.disjoint_comm.mp (Tree.disjoint_inorder_children unique)
  have original := represented
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      have reads := node_reads_frame original leftRep absent keysLeft keysRight leftRight preserved
      exact .node nonzero reads.1 (by simpa only [sameRoot] using reads.2.1) reads.2.2
        returnedRep (rightRep.frame leftRep keysLeft keysRight leftRight nodes preserved)

/-- Reassemble the symmetric parent after a right-subtree update retaining its
root. Only mathematical representation changes; no link is written. -/
theorem rebuild_right {a b next : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (unique : (Tree.node id a b).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (returnedRep : Rep key keys left right finish next)
    (sameRoot : root next = root b)
    (preserved : Heap.PreservesOutside (linkCells left right b) heap finish) :
    Rep key keys left right finish (.node id a next) := by
  have absent := Tree.root_not_mem_inorder_right unique
  have nodes := Tree.disjoint_inorder_children unique
  have original := represented
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      have reads := node_reads_frame original rightRep absent keysLeft keysRight leftRight preserved
      exact .node nonzero reads.1 reads.2.1 (by simpa only [sameRoot] using reads.2.2)
        (leftRep.frame rightRep keysLeft keysRight leftRight nodes preserved) returnedRep

/-- Reconnect a changed left subtree with one actual store. The subtree's
inorder contract supplies non-aliasing, and the complete frame composes through
both its execution and the final parent-link write. -/
theorem replace_left_after {a b next : Tree Nat} {middle : Heap}
    (represented : Rep key keys left right heap (.node id a b))
    (unique : (Tree.node id a b).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (returnedRep : Rep key keys left right middle next)
    (sameInorder : next.inorder = a.inorder)
    (preserved : Heap.PreservesOutside (linkCells left right a) heap middle) :
    ∃ finish, middle.write left id (root next) = .ok finish ∧
      Rep key keys left right finish (.node id next b) ∧
      Heap.PreservesOutside (linkCells left right (.node id a b)) heap finish := by
  have absentLeft := Tree.root_not_mem_inorder_left unique
  have absentRight := Tree.root_not_mem_inorder_right unique
  have absentNext : id ∉ next.inorder := by simpa only [sameInorder] using absentLeft
  have nodes := List.disjoint_comm.mp (Tree.disjoint_inorder_children unique)
  have original := represented
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      have reads := node_reads_frame original leftRep absentLeft
        keysLeft keysRight leftRight preserved
      have retained := rightRep.frame leftRep keysLeft keysRight leftRight nodes preserved
      obtain ⟨finish, written⟩ := Heap.write_exists_of_read reads.2.1 (root next)
      have rebuilt : Rep key keys left right finish (.node id next b) :=
        .node nonzero ((Heap.read_write_of_disjoint written keysLeft.symm).trans reads.1)
          (Heap.read_write written)
          ((Heap.read_write_of_disjoint written leftRight).trans reads.2.2)
          (returnedRep.write_left_of_not_mem written absentNext keysLeft.symm leftRight)
          (retained.write_left_of_not_mem written absentRight keysLeft.symm leftRight)
      have parentFrame :
          Heap.PreservesOutside (linkCells left right (.node id a b)) heap middle :=
        preserved.mono (linkCells_mono (by intro node member; simp [member]))
      have writeFrame :
          Heap.PreservesOutside (linkCells left right (.node id a b)) middle finish :=
        Heap.PreservesOutside.write written (left_mem_linkCells (by simp))
      exact ⟨finish, written, rebuilt, parentFrame.trans writeFrame⟩

/-- Reconnect a changed right subtree with one actual store, retaining the
left subtree and framing every cell outside the original parent tree. -/
theorem replace_right_after {a b next : Tree Nat} {middle : Heap}
    (represented : Rep key keys left right heap (.node id a b))
    (unique : (Tree.node id a b).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (returnedRep : Rep key keys left right middle next)
    (sameInorder : next.inorder = b.inorder)
    (preserved : Heap.PreservesOutside (linkCells left right b) heap middle) :
    ∃ finish, middle.write right id (root next) = .ok finish ∧
      Rep key keys left right finish (.node id a next) ∧
      Heap.PreservesOutside (linkCells left right (.node id a b)) heap finish := by
  have absentLeft := Tree.root_not_mem_inorder_left unique
  have absentRight := Tree.root_not_mem_inorder_right unique
  have absentNext : id ∉ next.inorder := by simpa only [sameInorder] using absentRight
  have nodes := Tree.disjoint_inorder_children unique
  have original := represented
  cases represented with
  | node nonzero keyRead leftRead rightRead leftRep rightRep =>
      have reads := node_reads_frame original rightRep absentRight
        keysLeft keysRight leftRight preserved
      have retained := leftRep.frame rightRep keysLeft keysRight leftRight nodes preserved
      obtain ⟨finish, written⟩ := Heap.write_exists_of_read reads.2.2 (root next)
      have rebuilt : Rep key keys left right finish (.node id a next) :=
        .node nonzero ((Heap.read_write_of_disjoint written keysRight.symm).trans reads.1)
          ((Heap.read_write_of_disjoint written leftRight.symm).trans reads.2.1)
          (Heap.read_write written)
          (retained.write_right_of_not_mem written absentLeft keysRight.symm leftRight.symm)
          (returnedRep.write_right_of_not_mem written absentNext keysRight.symm leftRight.symm)
      have parentFrame :
          Heap.PreservesOutside (linkCells left right (.node id a b)) heap middle :=
        preserved.mono (linkCells_mono (by intro node member; simp [member]))
      have writeFrame :
          Heap.PreservesOutside (linkCells left right (.node id a b)) middle finish :=
        Heap.PreservesOutside.write written (right_mem_linkCells (by simp))
      exact ⟨finish, written, rebuilt, parentFrame.trans writeFrame⟩

end Complexity.Language.BufferTree.Rep
