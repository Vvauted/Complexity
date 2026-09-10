/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.CorrectnessBasic

/-!
# Left-going recursive cases of the actual splay program

The recursive subtree contract composes through shared parent-link and rotation
rules. Each source store and call retains its actual intermediate heap. The
mathematical certificate records a single zig for an empty grandchild and the
appropriate double rotation otherwise, without changing the executed program.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

namespace AccessResult

variable {query : Nat}

/-- Left-left descent reattaches its recursive result and performs the actual
one- or two-rotation branch selected by the returned subtree. -/
theorem zig_zig_left (key : Nat → Nat) (keys left right : Buffer .nat)
    (z y : Nat) (inner c d : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node z (.node y inner c) d))
    (unique : (Tree.node z (.node y inner c) d).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (queryLtRoot : query < key z)
    (queryLtChild : query < key y)
    (recursive : AccessResult key keys left right query inner heap) :
    AccessResult key keys left right query (.node z (.node y inner c) d) heap := by
  obtain ⟨next, afterRecursive, recEval, nextRep, recTrace, recFrame⟩ := recursive
  have childUnique := Tree.nodup_inorder_left unique
  obtain ⟨zNonzero, zKey, zLeft, _, oldChild, _⟩ := Rep.node_iff.mp represented
  obtain ⟨yNonzero, yKey, yLeft, _, _, _⟩ := Rep.node_iff.mp oldChild
  obtain ⟨afterUpdate, update, newChild, childFrame⟩ :=
    oldChild.replace_left_after childUnique keysLeft keysRight leftRight
      nextRep recTrace.inorder_eq recFrame
  have rebuilt := represented.rebuild_left unique keysLeft keysRight leftRight
    newChild rfl childFrame
  have sameInorder : (Tree.node z (.node y next c) d).inorder =
      (Tree.node z (.node y inner c) d).inorder := by
    simp only [Tree.inorder, recTrace.inorder_eq]
  have newUnique : (Tree.node z (.node y next c) d).inorder.Nodup :=
    sameInorder.symm ▸ unique
  have updatedFrame :
      Heap.PreservesOutside (linkCells left right (.node z (.node y inner c) d))
        heap afterUpdate :=
    childFrame.mono (linkCells_mono (fun _ member => List.mem_append_left _ member))
  obtain ⟨afterFirst, firstRotation, firstRep, firstFrame⟩ :=
    rotateRight_rep key keys left right y z next c d rebuilt newUnique
      keysLeft keysRight leftRight
  have firstFrame' :
      Heap.PreservesOutside (linkCells left right (.node z (.node y inner c) d))
        afterUpdate afterFirst := by
    simpa only [linkCells_eq_of_inorder_eq sameInorder] using firstFrame
  simp only [Tree.rotateRight_node] at firstRep
  cases next with
  | nil =>
    have empty : inner = .nil := recTrace.eq_nil_iff.mp rfl
    subst inner
    have readRemaining : afterFirst.read left y = .ok 0 :=
      (Rep.node_iff.mp firstRep).2.2.1
    refine ⟨.node y .nil (.node z c d), afterFirst, ?_, firstRep, ?_,
      updatedFrame.trans firstFrame'⟩
    · simp only [root] at recEval update
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, queryLtRoot, zLeft, yNonzero, yKey,
        queryLtChild, yLeft, recEval, update, firstRotation, readRemaining]
    · rw [searchFocus_left key query z (.node y .nil c) d queryLtRoot (by simp),
        searchFocus_left_nil key query y c queryLtChild,
        searchDepth_left key query z (.node y .nil c) d queryLtRoot (by simp),
        searchDepth_left_nil key query y c queryLtChild]
      exact .zigLeft y z .nil c d
  | node x a b =>
    have innerNonempty : inner ≠ .nil := by
      intro empty
      have impossible := recTrace.eq_nil_iff.mpr empty
      cases impossible
    have firstUnique : (Tree.node y (.node x a b) (.node z c d)).inorder.Nodup := by
      exact (Tree.inorder_rotateRight (Tree.node z (.node y (.node x a b) c) d)).symm ▸
        newUnique
    have readRemaining : afterFirst.read left y = .ok x :=
      (Rep.node_iff.mp firstRep).2.2.1
    have xNonzero : x ≠ 0 := nextRep.node_ne_zero (by simp)
    obtain ⟨finish, secondRotation, finalRep, finalFrame⟩ :=
      rotateRight_rep key keys left right x y a b (.node z c d) firstRep firstUnique
        keysLeft keysRight leftRight
    have sameAfterFirst : (Tree.node y (.node x a b) (.node z c d)).inorder =
        (Tree.node z (.node y inner c) d).inorder :=
      (Tree.inorder_rotateRight (Tree.node z (.node y (.node x a b) c) d)).trans sameInorder
    have finalFrame' :
        Heap.PreservesOutside (linkCells left right (.node z (.node y inner c) d))
          afterFirst finish := by
      simpa only [linkCells_eq_of_inorder_eq sameAfterFirst] using finalFrame
    refine ⟨.node x a (.node y b (.node z c d)), finish, ?_, finalRep, ?_,
      (updatedFrame.trans firstFrame').trans finalFrame'⟩
    · simp only [root] at recEval update
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, queryLtRoot, zLeft, yNonzero, yKey,
        queryLtChild, yLeft, recEval, update, firstRotation, readRemaining,
        xNonzero, secondRotation]
    · have focused : searchFocus key query (.node z (.node y inner c) d) =
          searchFocus key query inner := by
        rw [searchFocus_left key query z (.node y inner c) d queryLtRoot (by simp),
          searchFocus_left key query y inner c queryLtChild innerNonempty]
      have depth : searchDepth key query (.node z (.node y inner c) d) =
          searchDepth key query inner + 2 := by
        rw [searchDepth_left key query z (.node y inner c) d queryLtRoot (by simp),
          searchDepth_left key query y inner c queryLtChild innerNonempty]
      rw [focused, depth]
      exact .zigZigLeft recTrace

/-- Left-right descent rotates the returned child when nonempty and reconnects
it before the final root rotation; every write is a source-program write. -/
theorem zig_zag_left (key : Nat → Nat) (keys left right : Buffer .nat)
    (z y : Nat) (a inner d : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap (.node z (.node y a inner) d))
    (unique : (Tree.node z (.node y a inner) d).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (queryLtRoot : query < key z)
    (childLtQuery : key y < query)
    (recursive : AccessResult key keys left right query inner heap) :
    AccessResult key keys left right query (.node z (.node y a inner) d) heap := by
  obtain ⟨next, afterRecursive, recEval, nextRep, recTrace, recFrame⟩ := recursive
  have childUnique := Tree.nodup_inorder_left unique
  obtain ⟨zNonzero, zKey, zLeft, _, oldChild, _⟩ := Rep.node_iff.mp represented
  obtain ⟨yNonzero, yKey, _, yRight, _, _⟩ := Rep.node_iff.mp oldChild
  obtain ⟨afterUpdate, update, newChild, childFrame⟩ :=
    oldChild.replace_right_after childUnique keysLeft keysRight leftRight
      nextRep recTrace.inorder_eq recFrame
  have sameChild : (Tree.node y a next).inorder = (Tree.node y a inner).inorder := by
    simp only [Tree.inorder, recTrace.inorder_eq]
  have newChildUnique : (Tree.node y a next).inorder.Nodup := sameChild.symm ▸ childUnique
  cases next with
  | nil =>
    have empty : inner = .nil := recTrace.eq_nil_iff.mp rfl
    subst inner
    have rebuilt := represented.rebuild_left unique keysLeft keysRight leftRight
      newChild rfl childFrame
    have updatedFrame :
        Heap.PreservesOutside (linkCells left right (.node z (.node y a .nil) d))
          heap afterUpdate :=
      childFrame.mono (linkCells_mono (fun _ member => List.mem_append_left _ member))
    obtain ⟨finish, rotated, finalRep, rotationFrame⟩ :=
      rotateRight_rep key keys left right y z a .nil d rebuilt unique
        keysLeft keysRight leftRight
    refine ⟨.node y a (.node z .nil d), finish, ?_, finalRep, ?_,
      updatedFrame.trans rotationFrame⟩
    · simp only [root] at recEval update
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, queryLtRoot, zLeft, yNonzero, yKey,
        childLtQuery, Nat.not_lt_of_ge childLtQuery.le, yRight, recEval, update, rotated]
    · rw [searchFocus_left key query z (.node y a .nil) d queryLtRoot (by simp),
        searchFocus_right_nil key query y a childLtQuery,
        searchDepth_left key query z (.node y a .nil) d queryLtRoot (by simp),
        searchDepth_right_nil key query y a childLtQuery]
      exact .zigLeft y z a .nil d
  | node x b c =>
    have innerNonempty : inner ≠ .nil := by
      intro empty
      have impossible := recTrace.eq_nil_iff.mpr empty
      cases impossible
    have xNonzero : x ≠ 0 := nextRep.node_ne_zero (by simp)
    obtain ⟨afterChild, childRotation, rotatedChild, rotationFrame⟩ :=
      rotateLeft_rep key keys left right y x a b c newChild newChildUnique
        keysLeft keysRight leftRight
    have rotationFrame' :
        Heap.PreservesOutside (linkCells left right (.node y a inner))
          afterUpdate afterChild := by
      simpa only [linkCells_eq_of_inorder_eq sameChild] using rotationFrame
    have rotatedSame : (Tree.node x (.node y a b) c).inorder =
        (Tree.node y a inner).inorder :=
      (Tree.inorder_rotateLeft (Tree.node y a (.node x b c))).trans sameChild
    obtain ⟨afterRootUpdate, rootUpdate, rebuilt, rootFrame⟩ :=
      represented.replace_left_after unique keysLeft keysRight leftRight
        rotatedChild rotatedSame (childFrame.trans rotationFrame')
    have sameWhole : (Tree.node z (.node x (.node y a b) c) d).inorder =
        (Tree.node z (.node y a inner) d).inorder := by
      exact congrArg (fun values => values ++ z :: d.inorder) rotatedSame
    have rebuiltUnique : (Tree.node z (.node x (.node y a b) c) d).inorder.Nodup :=
      sameWhole.symm ▸ unique
    obtain ⟨finish, rootRotation, finalRep, rotationFrame⟩ :=
      rotateRight_rep key keys left right x z (.node y a b) c d rebuilt rebuiltUnique
        keysLeft keysRight leftRight
    have rotationFrame' :
        Heap.PreservesOutside (linkCells left right (.node z (.node y a inner) d))
          afterRootUpdate finish := by
      simpa only [linkCells_eq_of_inorder_eq sameWhole] using rotationFrame
    refine ⟨.node x (.node y a b) (.node z c d), finish, ?_, finalRep, ?_,
      rootFrame.trans rotationFrame'⟩
    · simp only [Tree.rotateLeft_node, root] at recEval update rootUpdate
      rw [Implementation.splay_eq]
      simp [source_eval, zNonzero, zKey, queryLtRoot, zLeft, yNonzero, yKey,
        childLtQuery, Nat.not_lt_of_ge childLtQuery.le, yRight, recEval, update,
        xNonzero, childRotation, rootUpdate, rootRotation]
    · have focused : searchFocus key query (.node z (.node y a inner) d) =
          searchFocus key query inner := by
        rw [searchFocus_left key query z (.node y a inner) d queryLtRoot (by simp),
          searchFocus_right key query y a inner childLtQuery innerNonempty]
      have depth : searchDepth key query (.node z (.node y a inner) d) =
          searchDepth key query inner + 2 := by
        rw [searchDepth_left key query z (.node y a inner) d queryLtRoot (by simp),
          searchDepth_right key query y a inner childLtQuery innerNonempty]
      rw [focused, depth]
      exact .zigZagLeft recTrace

end AccessResult
end Complexity.Language.Examples.Splay
