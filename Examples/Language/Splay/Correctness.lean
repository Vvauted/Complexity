/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.CorrectnessLeft
import Examples.Language.Splay.CorrectnessRight

/-!
# Correctness and successful termination of the in-place splay access

One induction on the original mathematical tree verifies the actual recursive
source program. The representation supplies all successful buffer accesses;
shared subtree frames reconnect each recursive result without extra stores.
No proposed running-time bound or backend capacity is needed for this proof.

The output keeps its exact inorder node sequence, hence also uniqueness and BST
order, and its root is the matching or last-visited node of ordinary search.
The rotation certificate refers to that same execution and is available for
the separate compiler-cost and amortized proofs.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

/-- Every uniquely represented finite tree admits a successful splay access.
The recursive hypotheses range over strictly smaller original subtrees, not
fuel, available stack space or a proposed cost. -/
theorem splay_eval (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat)
    (tree : Tree Nat) {heap : Heap} (represented : Rep key keys left right heap tree)
    (unique : tree.inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) :
    AccessResult key keys left right query tree heap := by
  induction tree using (measure (fun tree : Tree Nat => tree.numNodes)).wf.induction
      generalizing heap with
  | h tree ih =>
    cases tree with
    | nil => exact .nil
    | node z a b =>
      obtain ⟨_, _, _, _, aRep, bRep⟩ := Rep.node_iff.mp represented
      have aUnique := Tree.nodup_inorder_left unique
      have bUnique := Tree.nodup_inorder_right unique
      by_cases goLeft : query < key z
      · cases a with
        | nil => exact .left_nil represented goLeft
        | node y inner c =>
          obtain ⟨_, _, _, _, innerRep, cRep⟩ := Rep.node_iff.mp aRep
          by_cases childLeft : query < key y
          · apply AccessResult.zig_zig_left key keys left right z y inner c b
              represented unique keysLeft keysRight leftRight goLeft childLeft
            apply ih inner ?_ innerRep (Tree.nodup_inorder_left aUnique)
            change inner.numNodes < (Tree.node z (.node y inner c) b).numNodes
            simp only [Tree.numNodes]
            omega
          · by_cases childRight : key y < query
            · apply AccessResult.zig_zag_left key keys left right z y inner c b
                represented unique keysLeft keysRight leftRight goLeft childRight
              apply ih c ?_ cRep (Tree.nodup_inorder_right aUnique)
              change c.numNodes < (Tree.node z (.node y inner c) b).numNodes
              simp only [Tree.numNodes]
              omega
            · exact .left_eq represented unique keysLeft keysRight leftRight goLeft (by omega)
      · by_cases goRight : key z < query
        · cases b with
          | nil => exact .right_nil represented goRight
          | node y c inner =>
            obtain ⟨_, _, _, _, cRep, innerRep⟩ := Rep.node_iff.mp bRep
            by_cases childRight : key y < query
            · apply AccessResult.zig_zig_right key keys left right z y a c inner
                represented unique keysLeft keysRight leftRight goRight childRight
              apply ih inner ?_ innerRep (Tree.nodup_inorder_right bUnique)
              change inner.numNodes < (Tree.node z a (.node y c inner)).numNodes
              simp only [Tree.numNodes]
              omega
            · by_cases childLeft : query < key y
              · apply AccessResult.zig_zag_right key keys left right z y a c inner
                  represented unique keysLeft keysRight leftRight goRight childLeft
                apply ih c ?_ cRep (Tree.nodup_inorder_left bUnique)
                change c.numNodes < (Tree.node z a (.node y c inner)).numNodes
                simp only [Tree.numNodes]
                omega
              · exact .right_eq represented unique keysLeft keysRight leftRight goRight (by omega)
        · exact .of_eq represented (by omega)

/-- The actual result has the ordinary mathematical BST properties and the
same complete key-array contents. The frame also protects unrelated node slots
inside the child buffers and the surrounding heap. -/
theorem splay_correct (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat)
    (tree : Tree Nat) {heap : Heap} (represented : Rep key keys left right heap tree)
    (unique : tree.inorder.Nodup) (ordered : (tree.inorder.map key).Pairwise (· < ·))
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right) :
    ∃ final finish,
      Implementation.splay keys left right (root tree) query heap =
        Part.some (.ok (root final), finish) ∧
      Rep key keys left right finish final ∧
      final.inorder = tree.inorder ∧ final.inorder.Nodup ∧
      (final.inorder.map key).Pairwise (· < ·) ∧
      final.root? = (searchFocus key query tree).root? ∧
      (∀ values, keys.Contents heap values → keys.Contents finish values) ∧
      Heap.PreservesOutside (linkCells left right tree) heap finish := by
  obtain ⟨final, finish, executed, finalRep, trace, preserved⟩ :=
    splay_eval key keys left right query tree represented unique keysLeft keysRight leftRight
  refine ⟨final, finish, executed, finalRep, trace.inorder_eq,
    trace.inorder_eq.symm ▸ unique, ?_, trace.root_eq, ?_, preserved⟩
  · simpa only [trace.inorder_eq] using ordered
  · intro values observed
    exact preserved.contents observed (fun _ bound =>
      represented.key_not_mem_linkCells keysLeft keysRight bound)

/-- The same successful execution is a callable source contract, suitable for
independent realizability and compiler-cost arguments. The generated ordinary-
argument bridge handles environment packing; the proof only reuses `splay_eval`.
Uniqueness is a property of the fixed mathematical input, while the three buffer
views may vary and may occupy disjoint slices of one heap object. -/
theorem splay_total (key : Nat → Nat) (query : Nat) (tree : Tree Nat)
    (unique : tree.inorder.Nodup) :
    FunctionTotal Implementation.program Implementation.splayId
      (fun args heap =>
        args.tail.tail.tail.head = root tree ∧ args.tail.tail.tail.tail.head = query ∧
        Rep key args.head args.tail.head args.tail.tail.head heap tree ∧
        args.head.Disjoint args.tail.head ∧ args.head.Disjoint args.tail.tail.head ∧
        args.tail.head.Disjoint args.tail.tail.head)
      (fun args heap result finish => ∃ final,
        result = root final ∧ Rep key args.head args.tail.head args.tail.tail.head finish final ∧
        SplayTrace (searchFocus key query tree) tree final (searchDepth key query tree) ∧
        Heap.PreservesOutside (linkCells args.tail.head args.tail.tail.head tree) heap finish) := by
  apply (Implementation.splay_total_iff
    (fun keys left right currentRoot currentQuery heap =>
      currentRoot = root tree ∧ currentQuery = query ∧ Rep key keys left right heap tree ∧
        keys.Disjoint left ∧ keys.Disjoint right ∧ left.Disjoint right)
    (fun keys left right _ _ heap result finish => ∃ final,
      result = root final ∧ Rep key keys left right finish final ∧
        SplayTrace (searchFocus key query tree) tree final (searchDepth key query tree) ∧
        Heap.PreservesOutside (linkCells left right tree) heap finish)).mpr
  rintro keys left right currentRoot currentQuery heap
    ⟨rootEq, queryEq, represented, keysLeft, keysRight, leftRight⟩
  subst currentRoot currentQuery
  obtain ⟨final, finish, executed, finalRep, trace, preserved⟩ :=
    splay_eval key keys left right query tree represented unique keysLeft keysRight leftRight
  exact ⟨root final, finish, executed, final, rfl, finalRep, trace, preserved⟩

end Complexity.Language.Examples.Splay
