/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Search
import Examples.Language.Splay.Trace
import Complexity.Language.Heap.Tree

/-!
# The mathematical and storage contract of a splay access

`Access` describes ordinary trees: the inorder sequence is unchanged and the
matching or last-visited node becomes the root. BST order and distinct labels
are consequences of this relation, not additional implementation obligations.

`Input` records the actual borrowed storage and its legal aliasing. `Post` is
shared by source correctness and the RAM endpoint: it retains the represented
output, rotation certificate and real initial/final heap frame. No execution
semantics, word-capacity assumption or proposed running time is defined here.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree

/-- The mathematical effect of an access, independently of heap encoding. -/
structure Access (key : Nat → Nat) (query : Nat) (initial final : Tree Nat) : Prop where
  /-- All nodes keep their exact inorder positions. -/
  inorder : final.inorder = initial.inorder
  /-- Ordinary search selects the final root, including unsuccessful searches. -/
  root_eq : final.root? = (searchFocus key query initial).root?

namespace Access

variable {key : Nat → Nat} {query : Nat} {initial final : Tree Nat}

/-- The certified rotations establish the ordinary mathematical specification. -/
theorem of_trace {rotations : Nat}
    (trace : SplayTrace (searchFocus key query initial) initial final rotations) :
    Access key query initial final := ⟨trace.inorder_eq, trace.root_eq⟩

/-- Distinct node identities survive an access. -/
theorem nodup (access : Access key query initial final) (unique : initial.inorder.Nodup) :
    final.inorder.Nodup := access.inorder.symm ▸ unique

/-- BST order is an ordinary list property transported by inorder equality. -/
theorem ordered (access : Access key query initial final)
    (ordered : (initial.inorder.map key).Pairwise (· < ·)) :
    (final.inorder.map key).Pairwise (· < ·) := by
  simpa only [access.inorder] using ordered

end Access

/-- Legal source inputs. Buffer columns may be disjoint slices of one object;
BST ordering and finite-machine capacities are not required for source safety. -/
structure Input (key : Nat → Nat) (keys left right : Buffer .nat)
    (tree : Tree Nat) (heap : Heap) : Prop where
  represented : Rep key keys left right heap tree
  unique : tree.inorder.Nodup
  keysLeft : keys.Disjoint left
  keysRight : keys.Disjoint right
  leftRight : left.Disjoint right

/-- The shared source/RAM postcondition. Its existential tree is a mathematical
view of the actual final heap; `result` is the root returned by that execution. -/
def Post (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat)
    (tree : Tree Nat) (initial : Heap) (result : Nat) (finish : Heap) : Prop :=
  ∃ final, result = root final ∧ Rep key keys left right finish final ∧
    SplayTrace (searchFocus key query tree) tree final (searchDepth key query tree) ∧
    Heap.PreservesOutside (linkCells left right tree) initial finish

namespace Post

variable {key : Nat → Nat} {keys left right : Buffer .nat} {query result : Nat}
variable {tree : Tree Nat} {initial finish : Heap}

/-- A caller can forget the rotation certificate and use the ordinary tree
specification together with the actual returned root and represented storage. -/
theorem access (post : Post key keys left right query tree initial result finish) :
    ∃ final, result = root final ∧ Rep key keys left right finish final ∧
      Access key query tree final := by
  obtain ⟨final, returned, represented, trace, _⟩ := post
  exact ⟨final, returned, represented, .of_trace trace⟩

/-- Cells outside the original tree's child links retain their actual values. -/
theorem frame (post : Post key keys left right query tree initial result finish) :
    Heap.PreservesOutside (linkCells left right tree) initial finish := by
  obtain ⟨_, _, _, _, preserved⟩ := post
  exact preserved

/-- The complete key-array contents are unchanged, not only the keys of nodes
that happened to be visited. This consequence is shared by source and RAM users. -/
theorem keys_contents (post : Post key keys left right query tree initial result finish)
    (input : Input key keys left right tree initial) {values : Array Nat}
    (observed : keys.Contents initial values) : keys.Contents finish values :=
  post.frame.contents observed (fun _ bound =>
    input.represented.key_not_mem_linkCells input.keysLeft input.keysRight bound)

end Post
end Complexity.Language.Examples.Splay
