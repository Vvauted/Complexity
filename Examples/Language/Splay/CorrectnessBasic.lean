/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Simp
import Examples.Language.Splay.RotationTree
import Examples.Language.Splay.Search
import Examples.Language.Splay.Trace
import Complexity.Language.Heap.Tree.Update

/-!
# Mathematical postconditions for the actual splay access

`AccessResult` packages successful execution of the sole source declaration,
its represented output tree and the exact cell-local frame. The mathematical
rotation certificate uses the depth of ordinary search in the original tree;
it is not a separate runtime evaluator or a resource premise for termination.

The elementary cases below stop at the current root or lift its matching child.
Recursive cases compose the same postcondition at smaller mathematical trees.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

/-- Successful source execution, mathematical splay certificate and actual heap
frame. No word-width, capacity or time-budget premise occurs here. -/
def AccessResult (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat)
    (tree : Tree Nat) (heap : Heap) : Prop :=
  ∃ final finish,
    Implementation.splay keys left right (root tree) query heap =
      Part.some (.ok (root final), finish) ∧
    Rep key keys left right finish final ∧
    SplayTrace (searchFocus key query tree) tree final (searchDepth key query tree) ∧
    Heap.PreservesOutside (linkCells left right tree) heap finish

namespace AccessResult

variable {key : Nat → Nat} {keys left right : Buffer .nat} {query : Nat}
variable {heap : Heap} {tree : Tree Nat}

/-- A terminal access keeps both its mathematical tree and its actual heap. -/
theorem of_unchanged (represented : Rep key keys left right heap tree)
    (executed : Implementation.splay keys left right (root tree) query heap =
      Part.some (.ok (root tree), heap))
    (focus : searchFocus key query tree = tree)
    (depth : searchDepth key query tree = 0) :
    AccessResult key keys left right query tree heap := by
  refine ⟨tree, heap, executed, represented, ?_, .refl _ _⟩
  simpa only [focus, depth] using SplayTrace.refl tree

/-- The empty input terminates without reading any buffer. -/
theorem nil : AccessResult key keys left right query .nil heap := by
  apply of_unchanged .nil (focus := rfl) (depth := rfl)
  rw [Implementation.splay_eq]
  simp [source_eval]

/-- A matching root needs no rotation. -/
theorem of_eq {id : Nat} {a b : Tree Nat}
    (represented : Rep key keys left right heap (.node id a b))
    (same : key id = query) :
    AccessResult key keys left right query (.node id a b) heap := by
  obtain ⟨nonzero, readKey, _, _, _, _⟩ := Rep.node_iff.mp represented
  apply of_unchanged represented
  · rw [Implementation.splay_eq]
    simp [source_eval, nonzero, readKey, same]
  · exact searchFocus_of_eq key query id a b same
  · exact searchDepth_of_eq key query id a b same

/-- A missing left child makes the current root the last visited node. -/
theorem left_nil {id : Nat} {b : Tree Nat}
    (represented : Rep key keys left right heap (.node id .nil b))
    (direction : query < key id) :
    AccessResult key keys left right query (.node id .nil b) heap := by
  obtain ⟨nonzero, readKey, readLeft, _, _, _⟩ := Rep.node_iff.mp represented
  apply of_unchanged represented
    (focus := searchFocus_left_nil key query id b direction)
    (depth := searchDepth_left_nil key query id b direction)
  rw [Implementation.splay_eq]
  simp [source_eval, nonzero, readKey, direction, readLeft]

/-- The symmetric missing-child branch also retains the current root. -/
theorem right_nil {id : Nat} {a : Tree Nat}
    (represented : Rep key keys left right heap (.node id a .nil))
    (direction : key id < query) :
    AccessResult key keys left right query (.node id a .nil) heap := by
  obtain ⟨nonzero, readKey, _, readRight, _, _⟩ := Rep.node_iff.mp represented
  apply of_unchanged represented
    (focus := searchFocus_right_nil key query id a direction)
    (depth := searchDepth_right_nil key query id a direction)
  rw [Implementation.splay_eq]
  simp [source_eval, nonzero, readKey, direction, Nat.not_lt_of_ge direction.le, readRight]

/-- A matching left child becomes the root through the actual right rotation. -/
theorem left_eq {x y : Nat} {a b c : Tree Nat}
    (represented : Rep key keys left right heap (.node y (.node x a b) c))
    (unique : (Tree.node y (.node x a b) c).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (direction : query < key y)
    (same : key x = query) :
    AccessResult key keys left right query (.node y (.node x a b) c) heap := by
  obtain ⟨nonzero, readKey, readChild, _, childRep, _⟩ := Rep.node_iff.mp represented
  obtain ⟨childNonzero, readChildKey, _, _, _, _⟩ := Rep.node_iff.mp childRep
  obtain ⟨finish, rotated, finalRep, preserved⟩ :=
    rotateRight_rep key keys left right x y a b c represented unique
      keysLeft keysRight leftRight
  refine ⟨.node x a (.node y b c), finish, ?_, finalRep, ?_, preserved⟩
  · rw [Implementation.splay_eq]
    simp [source_eval, nonzero, readKey, direction, readChild, childNonzero,
      readChildKey, same, rotated]
  · rw [searchFocus_left key query y (.node x a b) c direction (by simp),
      searchFocus_of_eq key query x a b same,
      searchDepth_left key query y (.node x a b) c direction (by simp),
      searchDepth_of_eq key query x a b same]
    exact SplayTrace.zigLeft x y a b c

/-- The symmetric immediate-child case uses the actual left rotation. -/
theorem right_eq {x y : Nat} {a b c : Tree Nat}
    (represented : Rep key keys left right heap (.node x a (.node y b c)))
    (unique : (Tree.node x a (.node y b c)).inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) (direction : key x < query)
    (same : key y = query) :
    AccessResult key keys left right query (.node x a (.node y b c)) heap := by
  obtain ⟨nonzero, readKey, _, readChild, _, childRep⟩ := Rep.node_iff.mp represented
  obtain ⟨childNonzero, readChildKey, _, _, _, _⟩ := Rep.node_iff.mp childRep
  obtain ⟨finish, rotated, finalRep, preserved⟩ :=
    rotateLeft_rep key keys left right x y a b c represented unique
      keysLeft keysRight leftRight
  refine ⟨.node y (.node x a b) c, finish, ?_, finalRep, ?_, preserved⟩
  · rw [Implementation.splay_eq]
    simp [source_eval, nonzero, readKey, direction, Nat.not_lt_of_ge direction.le,
      readChild, childNonzero, readChildKey, same, rotated]
  · rw [searchFocus_right key query x a (.node y b c) direction (by simp),
      searchFocus_of_eq key query y b c same,
      searchDepth_right key query x a (.node y b c) direction (by simp),
      searchDepth_of_eq key query y b c same]
    exact SplayTrace.zigRight y x a b c

end AccessResult

end Complexity.Language.Examples.Splay
