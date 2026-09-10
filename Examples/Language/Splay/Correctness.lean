/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.CorrectnessLeft
import Examples.Language.Splay.CorrectnessRight
import Examples.Language.Splay.Specification

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
open scoped Std.Do Part.TotalCorrectness

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

/-- The ordinary source contract: a legal represented input terminates without
fault and satisfies the shared mathematical and storage postcondition.
`Post.access` exposes inorder/search correctness; `Access.ordered`, `Access.nodup`
and `Post.keys_contents` give the usual BST, identity and key-array consequences. -/
theorem splay_correct (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat)
    (tree : Tree Nat) (initial : Heap) :
    ⦃fun heap => ⌜heap = initial ∧ Input key keys left right tree heap⌝⦄
      Implementation.splay keys left right (root tree) query
    ⦃⇓ result finish => ⌜Post key keys left right query tree initial result finish⌝⦄ := by
  apply (triple_iff_eval _ _ _).mpr
  rintro heap ⟨same, input⟩
  subst heap
  obtain ⟨final, finish, executed, finalRep, trace, preserved⟩ :=
    splay_eval key keys left right query tree input.represented input.unique
      input.keysLeft input.keysRight input.leftRight
  exact ⟨root final, finish, executed, final, rfl, finalRep, trace, preserved⟩

/-- The same `Input`/`Post` contract is callable by source and compiler rules.
The generated declaration handles argument packing; this proof transports the
native triple without repeating the tree proof or its mathematical predicates. -/
theorem splay_total (key : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    Implementation.splay_contract
    (fun keys left right currentRoot currentQuery heap =>
      currentRoot = root tree ∧ currentQuery = query ∧ Input key keys left right tree heap)
    (fun keys left right _ _ => Post key keys left right query tree) := by
  apply (Implementation.splay_total_iff _ _).mpr
  rintro keys left right currentRoot currentQuery heap ⟨rootEq, queryEq, input⟩
  subst currentRoot currentQuery
  exact (triple_iff_eval _ _ _).mp (splay_correct key keys left right query tree heap)
    heap ⟨rfl, input⟩

end Complexity.Language.Examples.Splay
