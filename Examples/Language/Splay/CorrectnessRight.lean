/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.CorrectnessBasic
import Examples.Language.Splay.RotationTree

/-!
# Right-going recursive cases of the actual splay program

The recursive call's represented subtree and precise cell frame are reattached
by the shared parent-link rules. The actual ensuing rotations produce the
mathematical splay trace and preserve every cell outside the original tree.
Empty recursive results take the implementation's single-rotation path.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

namespace AccessResult

variable {query : Nat}

/-- Right-right descent composes the recursive call, its real parent-link
write and one or two left rotations at their actual intermediate heaps. -/
theorem zig_zig_right (key : Nat → Nat) (keys left right : Buffer .nat)
    (z y : Nat) (a b inner : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node z a (.node y b inner)))
    (unique : (Tree.node z a (.node y b inner)).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (rootLt : key z < query)
    (childLt : key y < query)
    (recursive : AccessResult key keys left right query inner heap) :
    AccessResult key keys left right query (.node z a (.node y b inner)) heap := by
  obtain ⟨next, afterRecursive, recEval, nextRep, recTrace, recFrame⟩ := recursive
  have original := represented
  have childUnique : (Tree.node y b inner).inorder.Nodup :=
    Tree.nodup_inorder_right unique
  cases represented with
  | node zNonzero zKey zLeft zRight aRep childRep =>
    have oldChild := childRep
    cases childRep with
    | node yNonzero yKey yLeft yRight bRep innerRep =>
      obtain ⟨afterUpdate, update, newChild, childFrame⟩ :=
        oldChild.replace_right_after childUnique keysLeft keysRight leftRight
          nextRep recTrace.inorder_eq recFrame
      have rebuilt := original.rebuild_right unique keysLeft keysRight leftRight
        newChild rfl childFrame
      have sameInorder : (Tree.node z a (.node y b next)).inorder =
          (Tree.node z a (.node y b inner)).inorder := by
        simp only [Tree.inorder, recTrace.inorder_eq]
      have newUnique : (Tree.node z a (.node y b next)).inorder.Nodup :=
        sameInorder.symm ▸ unique
      have updatedFrame :
          Heap.PreservesOutside (linkCells left right (.node z a (.node y b inner)))
            heap afterUpdate :=
        childFrame.mono (linkCells_mono (by
          intro id member
          exact List.mem_append_right _ (List.mem_cons_of_mem _ member)))
      obtain ⟨afterFirst, firstRotation, firstRep, firstFrame⟩ :=
        rotateLeft_rep key keys left right z y a b next rebuilt newUnique
          keysLeft keysRight leftRight
      have firstFrame' :
          Heap.PreservesOutside (linkCells left right (.node z a (.node y b inner)))
            afterUpdate afterFirst := by
        simpa only [linkCells_eq_of_inorder_eq sameInorder] using firstFrame
      simp only [Tree.rotateLeft_node] at firstRep
      cases next with
      | nil =>
        have empty : inner = .nil := recTrace.eq_nil_iff.mp rfl
        subst inner
        have readRemaining : afterFirst.read right y = .ok 0 := by
          cases firstRep with
          | node _ _ _ readRight _ _ => exact readRight
        refine ⟨.node y (.node z a b) .nil, afterFirst, ?_, firstRep, ?_,
          updatedFrame.trans firstFrame'⟩
        · simp only [root] at recEval update
          rw [Implementation.splay_eq]
          simp [source_eval, zNonzero, zKey, rootLt, Nat.not_lt_of_ge rootLt.le,
            zRight, yNonzero, yKey, childLt, yRight, recEval, update,
            firstRotation, readRemaining]
        · simpa only [searchFocus, searchDepth, if_pos rootLt, if_pos childLt,
            if_neg (Nat.not_lt_of_ge rootLt.le), if_neg (Nat.not_lt_of_ge childLt.le),
            Nat.zero_add] using SplayTrace.zigRight y z a b (.nil : Tree Nat)
      | node x c d =>
        have innerNonempty : inner ≠ .nil := by
          intro empty
          have impossible := recTrace.eq_nil_iff.mpr empty
          cases impossible
        have firstUnique : (Tree.node y (.node z a b) (.node x c d)).inorder.Nodup := by
          simpa only [Tree.rotateLeft_node] using
            (Tree.inorder_rotateLeft (Tree.node z a (.node y b (.node x c d)))).symm ▸ newUnique
        have readRemaining : afterFirst.read right y = .ok x := by
          cases firstRep with
          | node _ _ _ readRight _ _ => exact readRight
        have xNonzero : x ≠ 0 := nextRep.node_ne_zero (by simp)
        obtain ⟨finish, secondRotation, finalRep, finalFrame⟩ :=
          rotateLeft_rep key keys left right y x (.node z a b) c d firstRep firstUnique
            keysLeft keysRight leftRight
        have sameAfterFirst : (Tree.node y (.node z a b) (.node x c d)).inorder =
            (Tree.node z a (.node y b inner)).inorder := by
          exact (Tree.inorder_rotateLeft
            (Tree.node z a (.node y b (.node x c d)))).trans sameInorder
        have finalFrame' :
            Heap.PreservesOutside (linkCells left right (.node z a (.node y b inner)))
              afterFirst finish := by
          simpa only [linkCells_eq_of_inorder_eq sameAfterFirst] using finalFrame
        refine ⟨.node x (.node y (.node z a b) c) d, finish, ?_, finalRep, ?_,
          (updatedFrame.trans firstFrame').trans finalFrame'⟩
        · simp only [root] at recEval update
          rw [Implementation.splay_eq]
          simp [source_eval, zNonzero, zKey, rootLt, Nat.not_lt_of_ge rootLt.le,
            zRight, yNonzero, yKey, childLt, yRight, recEval, update,
            firstRotation, readRemaining, xNonzero, secondRotation]
        · have focused : searchFocus key query (.node z a (.node y b inner)) =
              searchFocus key query inner := by
            rw [searchFocus_right key query z a (.node y b inner) rootLt (by simp),
              searchFocus_right key query y b inner childLt innerNonempty]
          have depth : searchDepth key query (.node z a (.node y b inner)) =
              searchDepth key query inner + 2 := by
            rw [searchDepth_right key query z a (.node y b inner) rootLt (by simp),
              searchDepth_right key query y b inner childLt innerNonempty]
          rw [focused, depth]
          exact .zigZigRight recTrace

/-- Right-left descent reattaches the actual recursive result, rotates the
child only when nonempty, updates the root link and performs the final rotation. -/
theorem zig_zag_right (key : Nat → Nat) (keys left right : Buffer .nat)
    (z y : Nat) (a inner d : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node z a (.node y inner d)))
    (unique : (Tree.node z a (.node y inner d)).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (rootLt : key z < query)
    (queryLtChild : query < key y)
    (recursive : AccessResult key keys left right query inner heap) :
    AccessResult key keys left right query (.node z a (.node y inner d)) heap := by
  obtain ⟨next, afterRecursive, recEval, nextRep, recTrace, recFrame⟩ := recursive
  have original := represented
  have childUnique : (Tree.node y inner d).inorder.Nodup :=
    Tree.nodup_inorder_right unique
  obtain ⟨zNonzero, zKey, zLeft, zRight, aRep, oldChild⟩ := Rep.node_iff.mp represented
  obtain ⟨yNonzero, yKey, yLeft, yRight, innerRep, dRep⟩ := Rep.node_iff.mp oldChild
  obtain ⟨afterUpdate, update, newChild, childFrame⟩ :=
    oldChild.replace_left_after childUnique keysLeft keysRight leftRight
      nextRep recTrace.inorder_eq recFrame
  have sameChild : (Tree.node y next d).inorder = (Tree.node y inner d).inorder := by
    simp only [Tree.inorder, recTrace.inorder_eq]
  have newChildUnique : (Tree.node y next d).inorder.Nodup := sameChild.symm ▸ childUnique
  cases next with
  | nil =>
    have empty : inner = .nil := recTrace.eq_nil_iff.mp rfl
    subst inner
    have rebuilt := original.rebuild_right unique keysLeft keysRight leftRight
      newChild rfl childFrame
    have updatedFrame :
        Heap.PreservesOutside (linkCells left right (.node z a (.node y .nil d)))
          heap afterUpdate :=
      childFrame.mono (linkCells_mono (by
        intro id member
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)))
    obtain ⟨finish, rotated, finalRep, rotationFrame⟩ :=
      rotateLeft_rep key keys left right z y a .nil d rebuilt unique
        keysLeft keysRight leftRight
    refine ⟨.node y (.node z a .nil) d, finish, ?_, finalRep, ?_,
      updatedFrame.trans rotationFrame⟩
    · simp only [root] at recEval update
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, rootLt, Nat.not_lt_of_ge rootLt.le,
        zRight, yNonzero, yKey, queryLtChild, Nat.not_lt_of_ge queryLtChild.le,
        yLeft, recEval, update, rotated]
    · simpa only [searchFocus, searchDepth, if_pos rootLt, if_pos queryLtChild,
        if_neg (Nat.not_lt_of_ge rootLt.le), Nat.zero_add] using
        SplayTrace.zigRight y z a (.nil : Tree Nat) d
  | node x b c =>
    have innerNonempty : inner ≠ .nil := by
      intro empty
      have impossible := recTrace.eq_nil_iff.mpr empty
      cases impossible
    have xNonzero : x ≠ 0 := nextRep.node_ne_zero (by simp)
    obtain ⟨afterChild, childRotation, rotatedChild, rotationFrame⟩ :=
      rotateRight_rep key keys left right x y b c d newChild newChildUnique
        keysLeft keysRight leftRight
    have rotationFrame' :
        Heap.PreservesOutside (linkCells left right (.node y inner d))
          afterUpdate afterChild := by
      simpa only [linkCells_eq_of_inorder_eq sameChild] using rotationFrame
    have rotatedSame : (Tree.node x b (.node y c d)).inorder =
        (Tree.node y inner d).inorder :=
      (Tree.inorder_rotateRight (Tree.node y (.node x b c) d)).trans sameChild
    obtain ⟨afterRootUpdate, rootUpdate, rebuilt, rootFrame⟩ :=
      original.replace_right_after unique keysLeft keysRight leftRight
        rotatedChild rotatedSame (childFrame.trans rotationFrame')
    have sameWhole : (Tree.node z a (.node x b (.node y c d))).inorder =
        (Tree.node z a (.node y inner d)).inorder := by
      simpa only [Tree.inorder] using
        congrArg (fun values => a.inorder ++ z :: values) rotatedSame
    have rebuiltUnique : (Tree.node z a (.node x b (.node y c d))).inorder.Nodup :=
      sameWhole.symm ▸ unique
    obtain ⟨finish, rootRotation, finalRep, rotationFrame⟩ :=
      rotateLeft_rep key keys left right z x a b (.node y c d) rebuilt rebuiltUnique
        keysLeft keysRight leftRight
    have rotationFrame' :
        Heap.PreservesOutside (linkCells left right (.node z a (.node y inner d)))
          afterRootUpdate finish := by
      simpa only [linkCells_eq_of_inorder_eq sameWhole] using rotationFrame
    refine ⟨.node x (.node z a b) (.node y c d), finish, ?_, finalRep, ?_,
      rootFrame.trans rotationFrame'⟩
    · simp only [Tree.rotateRight_node, root] at recEval update rootUpdate
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, rootLt, Nat.not_lt_of_ge rootLt.le,
        zRight, yNonzero, yKey, queryLtChild, Nat.not_lt_of_ge queryLtChild.le,
        yLeft, recEval, update, xNonzero, childRotation, rootUpdate, rootRotation]
    · have focused : searchFocus key query (.node z a (.node y inner d)) =
          searchFocus key query inner := by
        rw [searchFocus_right key query z a (.node y inner d) rootLt (by simp),
          searchFocus_left key query y inner d queryLtChild innerNonempty]
      have depth : searchDepth key query (.node z a (.node y inner d)) =
          searchDepth key query inner + 2 := by
        rw [searchDepth_right key query z a (.node y inner d) rootLt (by simp),
          searchDepth_left key query y inner d queryLtChild innerNonempty]
      rw [focused, depth]
      exact .zigZagRight recTrace

end AccessResult
end Complexity.Language.Examples.Splay
