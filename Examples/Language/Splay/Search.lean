/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.Tree.Basic
import Mathlib.Data.List.Pairwise

/-!
# The original subtree selected by a binary-search-tree access

`searchFocus` is ordinary mathematical BST search. It returns the original
subtree rooted at the matching node, or at the last node visited on an
unsuccessful search. It does not rotate a tree, model memory or assign costs.
The splay implementation's correctness theorem can therefore specify its new
root without maintaining a second executable splay algorithm.

Node labels are stable natural-number IDs; `keys` gives their mathematical keys.
Orderedness is exactly mathlib's `List.Pairwise` on the inorder key sequence.
-/

namespace Complexity.Language.Examples.Splay

/-- The original subtree at the matching or last visited node of ordinary BST search. -/
def searchFocus (keys : Nat → Nat) (query : Nat) : Tree Nat → Tree Nat
  | .nil => .nil
  | .node root left right =>
    if query < keys root then
      match left with
      | .nil => .node root left right
      | .node _ _ _ => searchFocus keys query left
    else if keys root < query then
      match right with
      | .nil => .node root left right
      | .node _ _ _ => searchFocus keys query right
    else
      .node root left right

/-- The number of edges to nonempty children traversed by ordinary BST search.
This is a structural path length, not a price assigned to executable operations. -/
def searchDepth (keys : Nat → Nat) (query : Nat) : Tree Nat → Nat
  | .nil => 0
  | .node root left right =>
    if query < keys root then
      match left with
      | .nil => 0
      | .node _ _ _ => searchDepth keys query left + 1
    else if keys root < query then
      match right with
      | .nil => 0
      | .node _ _ _ => searchDepth keys query right + 1
    else
      0

@[simp] theorem searchFocus_nil (keys : Nat → Nat) (query : Nat) :
    searchFocus keys query .nil = .nil := rfl

theorem searchFocus_of_eq (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : keys root = query) :
    searchFocus keys query (.node root left right) = .node root left right := by
  simp [searchFocus, h]

theorem searchFocus_left_nil (keys : Nat → Nat) (query root : Nat) (right : Tree Nat)
    (h : query < keys root) :
    searchFocus keys query (.node root .nil right) = .node root .nil right := by
  simp [searchFocus, h]

theorem searchFocus_right_nil (keys : Nat → Nat) (query root : Nat) (left : Tree Nat)
    (h : keys root < query) :
    searchFocus keys query (.node root left .nil) = .node root left .nil := by
  simp [searchFocus, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

theorem searchFocus_left (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : query < keys root) (hne : left ≠ .nil) :
    searchFocus keys query (.node root left right) = searchFocus keys query left := by
  cases left with
  | nil => exact (hne rfl).elim
  | node => simp only [searchFocus, if_pos h]

theorem searchFocus_right (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : keys root < query) (hne : right ≠ .nil) :
    searchFocus keys query (.node root left right) = searchFocus keys query right := by
  cases right with
  | nil => exact (hne rfl).elim
  | node => simp only [searchFocus, if_pos h, if_neg (Nat.not_lt_of_ge (Nat.le_of_lt h))]

@[simp] theorem searchDepth_nil (keys : Nat → Nat) (query : Nat) :
    searchDepth keys query .nil = 0 := rfl

theorem searchDepth_of_eq (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : keys root = query) : searchDepth keys query (.node root left right) = 0 := by
  simp [searchDepth, h]

theorem searchDepth_left_nil (keys : Nat → Nat) (query root : Nat) (right : Tree Nat)
    (h : query < keys root) : searchDepth keys query (.node root .nil right) = 0 := by
  simp [searchDepth, h]

theorem searchDepth_right_nil (keys : Nat → Nat) (query root : Nat) (left : Tree Nat)
    (h : keys root < query) : searchDepth keys query (.node root left .nil) = 0 := by
  simp [searchDepth, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

theorem searchDepth_left (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : query < keys root) (hne : left ≠ .nil) :
    searchDepth keys query (.node root left right) = searchDepth keys query left + 1 := by
  cases left with
  | nil => exact (hne rfl).elim
  | node => simp only [searchDepth, if_pos h]

theorem searchDepth_right (keys : Nat → Nat) (query root : Nat) (left right : Tree Nat)
    (h : keys root < query) (hne : right ≠ .nil) :
    searchDepth keys query (.node root left right) = searchDepth keys query right + 1 := by
  cases right with
  | nil => exact (hne rfl).elim
  | node => simp only [searchDepth, if_pos h, if_neg (Nat.not_lt_of_ge (Nat.le_of_lt h))]

/-- Ordinary search traverses no more edges than there are original internal nodes. -/
theorem searchDepth_le_numNodes (keys : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    searchDepth keys query tree ≤ tree.numNodes := by
  induction tree with
  | nil => simp
  | node root left right ihLeft ihRight =>
    by_cases hleft : query < keys root
    · cases left with
      | nil =>
        rw [searchDepth_left_nil keys query root right hleft]
        exact Nat.zero_le _
      | node child a b =>
        rw [searchDepth_left keys query root (.node child a b) right hleft (by simp)]
        exact Nat.add_le_add_right (Nat.le_trans ihLeft (Nat.le_add_right _ _)) 1
    · by_cases hright : keys root < query
      · cases right with
        | nil =>
          rw [searchDepth_right_nil keys query root left hright]
          exact Nat.zero_le _
        | node child a b =>
          rw [searchDepth_right keys query root left (.node child a b) hright (by simp)]
          exact Nat.add_le_add_right (Nat.le_trans ihRight (Nat.le_add_left _ _)) 1
      · have heq : keys root = query := by omega
        rw [searchDepth_of_eq keys query root left right heq]
        exact Nat.zero_le _

/-- An original subtree, reached by zero or more child edges without any rotation. -/
inductive IsSubtree : Tree Nat → Tree Nat → Prop
  | refl (tree : Tree Nat) : IsSubtree tree tree
  | left {focus left right : Tree Nat} {root : Nat}
      (sub : IsSubtree focus left) : IsSubtree focus (.node root left right)
  | right {focus left right : Tree Nat} {root : Nat}
      (sub : IsSubtree focus right) : IsSubtree focus (.node root left right)

/-- At the last visited node, the key matches or the requested child is empty. -/
def SearchTerminal (keys : Nat → Nat) (query : Nat) : Tree Nat → Prop
  | .nil => True
  | .node root left right =>
      keys root = query ∨ (query < keys root ∧ left = .nil) ∨
        (keys root < query ∧ right = .nil)

/-- Ordinary search selects an original subtree and stops at precisely a terminal node. -/
theorem searchFocus_spec (keys : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    IsSubtree (searchFocus keys query tree) tree ∧
      (searchFocus keys query tree = .nil ↔ tree = .nil) ∧
      SearchTerminal keys query (searchFocus keys query tree) := by
  induction tree with
  | nil => exact ⟨.refl _, Iff.rfl, trivial⟩
  | node root left right ihLeft ihRight =>
    by_cases hleft : query < keys root
    · cases left with
      | nil =>
        rw [searchFocus_left_nil keys query root right hleft]
        exact ⟨.refl _, Iff.rfl, Or.inr (Or.inl ⟨hleft, rfl⟩)⟩
      | node child a b =>
        rw [searchFocus_left keys query root (.node child a b) right hleft (by simp)]
        exact ⟨.left ihLeft.1, by simpa using ihLeft.2.1, ihLeft.2.2⟩
    · by_cases hright : keys root < query
      · cases right with
        | nil =>
          rw [searchFocus_right_nil keys query root left hright]
          exact ⟨.refl _, Iff.rfl, Or.inr (Or.inr ⟨hright, rfl⟩)⟩
        | node child a b =>
          rw [searchFocus_right keys query root left (.node child a b) hright (by simp)]
          exact ⟨.right ihRight.1, by simpa using ihRight.2.1, ihRight.2.2⟩
      · have heq : keys root = query := by omega
        rw [searchFocus_of_eq keys query root left right heq]
        exact ⟨.refl _, Iff.rfl, Or.inl heq⟩

theorem searchFocus_subtree (keys : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    IsSubtree (searchFocus keys query tree) tree := (searchFocus_spec keys query tree).1

theorem searchFocus_eq_nil_iff (keys : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    searchFocus keys query tree = .nil ↔ tree = .nil := (searchFocus_spec keys query tree).2.1

theorem searchFocus_ne_nil (keys : Nat → Nat) (query : Nat) {tree : Tree Nat}
    (hne : tree ≠ .nil) : searchFocus keys query tree ≠ .nil :=
  mt (searchFocus_eq_nil_iff keys query tree).mp hne

theorem searchFocus_terminal (keys : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    SearchTerminal keys query (searchFocus keys query tree) :=
  (searchFocus_spec keys query tree).2.2

/-- A selected nonempty subtree retains an actual node of the original input. -/
theorem IsSubtree.root_mem {focus tree : Tree Nat} (sub : IsSubtree focus tree)
    {root : Nat} (hroot : focus.root? = some root) : root ∈ tree.inorder := by
  induction sub with
  | refl => cases focus <;> simp_all
  | left sub ih => exact List.mem_append_left _ ih
  | right sub ih => exact List.mem_append_right _ (List.mem_cons_of_mem _ ih)

theorem IsSubtree.numLeaves_le {focus tree : Tree Nat} (sub : IsSubtree focus tree) :
    focus.numLeaves ≤ tree.numLeaves := by
  induction sub <;> (try simp_all only [Tree.numLeaves]) <;> omega

/-- The root returned by mathematical search belongs to the original inorder list. -/
theorem searchFocus_root_mem (keys : Nat → Nat) (query : Nat) (tree : Tree Nat)
    {root : Nat} (hroot : (searchFocus keys query tree).root? = some root) :
    root ∈ tree.inorder := (searchFocus_subtree keys query tree).root_mem hroot

private theorem ordered_node {keys : Nat → Nat} {root : Nat} {left right : Tree Nat}
    (ordered : ((Tree.node root left right).inorder.map keys).Pairwise (· < ·)) :
    (left.inorder.map keys).Pairwise (· < ·) ∧
      (right.inorder.map keys).Pairwise (· < ·) ∧
      (∀ value ∈ left.inorder.map keys, value < keys root) ∧
      (∀ value ∈ right.inorder.map keys, keys root < value) := by
  simp only [Tree.inorder, List.map_append, List.map_cons, List.pairwise_append,
    List.pairwise_cons] at ordered
  rcases ordered with ⟨hl, ⟨hroot, hr⟩, hcross⟩
  exact ⟨hl, hr, fun value hmem => hcross value hmem (keys root) (by simp), hroot⟩

/-- On an ordered tree, any existing query is the key at the selected root. -/
theorem searchFocus_root_of_mem (keys : Nat → Nat) (query : Nat) (tree : Tree Nat)
    (ordered : (tree.inorder.map keys).Pairwise (· < ·))
    (found : query ∈ tree.inorder.map keys) :
    (searchFocus keys query tree).root?.map keys = some query := by
  revert ordered found
  induction tree with
  | nil => intro _ found; simp at found
  | node root left right ihLeft ihRight =>
    intro ordered found
    obtain ⟨hleftOrder, hrightOrder, hleftKeys, hrightKeys⟩ := ordered_node ordered
    have hmem : query ∈ left.inorder.map keys ∨ query = keys root ∨
        query ∈ right.inorder.map keys := by
      simpa only [Tree.inorder, List.map_append, List.map_cons, List.mem_append,
        List.mem_cons] using found
    by_cases hleft : query < keys root
    · have hmemLeft : query ∈ left.inorder.map keys := by
        rcases hmem with h | h | h
        · exact h
        · omega
        · have := hrightKeys query h
          omega
      have hne : left ≠ .nil := by
        intro hnil
        simp [hnil] at hmemLeft
      rw [searchFocus_left keys query root left right hleft hne]
      exact ihLeft hleftOrder hmemLeft
    · by_cases hright : keys root < query
      · have hmemRight : query ∈ right.inorder.map keys := by
          rcases hmem with h | h | h
          · have := hleftKeys query h
            omega
          · omega
          · exact h
        have hne : right ≠ .nil := by
          intro hnil
          simp [hnil] at hmemRight
        rw [searchFocus_right keys query root left right hright hne]
        exact ihRight hrightOrder hmemRight
      · have heq : keys root = query := by omega
        rw [searchFocus_of_eq keys query root left right heq]
        simpa only [Tree.root?, Option.map_some] using congrArg some heq

/-- An unsuccessful search ends at a node whose requested child is empty. -/
theorem searchFocus_missing_child (keys : Nat → Nat) (query : Nat) (tree : Tree Nat)
    (missing : query ∉ tree.inorder.map keys) {root : Nat} {left right : Tree Nat}
    (hfocus : searchFocus keys query tree = .node root left right) :
    (query < keys root ∧ left = .nil) ∨ (keys root < query ∧ right = .nil) := by
  have hterminal := searchFocus_terminal keys query tree
  rw [hfocus] at hterminal
  rcases hterminal with heq | h | h
  · have hroot : root ∈ tree.inorder := searchFocus_root_mem keys query tree (by simp [hfocus])
    have hkey : keys root ∈ tree.inorder.map keys := List.mem_map_of_mem hroot
    exact (missing (heq ▸ hkey)).elim
  · exact Or.inl h
  · exact Or.inr h

end Complexity.Language.Examples.Splay
