/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.TopTree.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Top-tree decompositions and summaries

`Cluster.Decomposition` is the binary edge decomposition of a cluster: its leaves
are individual ambient edges and its internal nodes are legal joins. The leaves
are proved to enumerate the represented edges exactly once. A compositional fold
allows applications to maintain summaries using their leaf and join rules.

`SimpleGraph.TopTree` covers a whole underlying tree, with an empty root for an
edgeless tree. It does not assume a logarithmic height or implement dynamic forest
updates. The proved height bound is only the elementary linear bound that holds
for every full binary decomposition.
-/

namespace SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V} {exposed : Set V}

namespace Cluster

/-- A binary decomposition into single edges, with a valid cluster at every node. -/
inductive Decomposition : Cluster G exposed → Type u
  | edge {a b : V} (hab : G.Adj a b) : Decomposition (Cluster.edge exposed hab)
  | join {A B : Cluster G exposed} {pivot : V} (h : Joinable A B pivot)
      (left : Decomposition A) (right : Decomposition B) :
      Decomposition (Cluster.join A B h)

namespace Decomposition

variable {C : Cluster G exposed}

/-- The two actual child decompositions recovered by one split. -/
structure Children (C : Cluster G exposed) where
  leftCluster : Cluster G exposed
  rightCluster : Cluster G exposed
  pivot : V
  joinable : Joinable leftCluster rightCluster pivot
  left : Decomposition leftCluster
  right : Decomposition rightCluster
  parent_eq : Cluster.join leftCluster rightCluster joinable = C

/-- Remove one join node. A single-edge cluster has no children to split. -/
def split : {C : Cluster G exposed} → Decomposition C → Option (Children C)
  | _, .edge _ => none
  | _, .join (A := A) (B := B) (pivot := pivot) h left right =>
      some ⟨A, B, pivot, h, left, right, rfl⟩

/-- Reassemble the actual children returned by a split. -/
def Children.rejoin (children : Children C) : Decomposition C :=
  children.parent_eq ▸ .join children.joinable children.left children.right

/-- Splitting and immediately rejoining recovers the same decomposition. -/
theorem rejoin_of_split_eq_some (d : Decomposition C) (children : Children C)
    (h : d.split = some children) : children.rejoin = d := by
  cases d with
  | edge hab => simp [split] at h
  | join joinable left right =>
    simp only [split, Option.some.injEq] at h
    subst children
    rfl

/-- Edges in the left-to-right order of the leaves. This is an executable traversal
of the mathematical decomposition, not a constant-time dynamic update operation. -/
def edges : {C : Cluster G exposed} → Decomposition C → List (Sym2 V)
  | _, .edge (a := a) (b := b) _ => [s(a, b)]
  | _, .join _ left right => left.edges ++ right.edges

@[simp]
theorem mem_edges (d : Decomposition C) (e : Sym2 V) :
    e ∈ d.edges ↔ e ∈ C.graph.edgeSet := by
  induction d with
  | edge hab => simp [edges]
  | join h left right ihl ihr => simp [edges, ihl, ihr, Subgraph.edgeSet_sup]

/-- Different leaves never represent the same ambient edge. -/
theorem edges_nodup (d : Decomposition C) : d.edges.Nodup := by
  induction d with
  | edge hab => simp [edges]
  | join h left right ihl ihr =>
    rw [edges, List.nodup_append]
    refine ⟨ihl, ihr, ?_⟩
    intro e he f hf heq
    subst f
    exact Set.disjoint_left.mp h.disjoint_edgeSet
      (left.mem_edges e |>.mp he) (right.mem_edges e |>.mp hf)

/-- Changing the legal decomposition changes only the order of its edge leaves. -/
theorem edges_perm (d d' : Decomposition C) : d.edges.Perm d'.edges :=
  (List.perm_ext_iff_of_nodup d.edges_nodup d'.edges_nodup).2
    (fun e => (d.mem_edges e).trans (d'.mem_edges e).symm)

/-- Number of leaves, equivalently the number of represented edges. -/
def leafCount (d : Decomposition C) : Nat := d.edges.length

theorem leafCount_pos (d : Decomposition C) : 0 < d.leafCount := by
  induction d with
  | edge hab => simp [leafCount, edges]
  | join h left right ihl ihr => simp only [leafCount, edges, List.length_append] at *; omega

/-- The abstract edge count agrees with the actual nonduplicating leaf enumeration. -/
theorem ncard_edgeSet (d : Decomposition C) : C.graph.edgeSet.ncard = d.leafCount := by
  classical
  have hset : C.graph.edgeSet = (↑d.edges.toFinset : Set (Sym2 V)) := by
    ext e
    simp [d.mem_edges e]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup d.edges_nodup]
  rfl

/-- Number of join nodes, excluding single-edge leaves. -/
def joinCount : {C : Cluster G exposed} → Decomposition C → Nat
  | _, .edge _ => 0
  | _, .join _ left right => left.joinCount + right.joinCount + 1

/-- A full binary decomposition with `m` edges has exactly `m - 1` join nodes. -/
theorem joinCount_add_one (d : Decomposition C) : d.joinCount + 1 = d.leafCount := by
  induction d with
  | edge hab => rfl
  | join h left right ihl ihr =>
    simp only [joinCount, leafCount, edges, List.length_append] at *
    omega

/-- Root-to-leaf height, counting join nodes only. -/
def height : {C : Cluster G exposed} → Decomposition C → Nat
  | _, .edge _ => 0
  | _, .join _ left right => max left.height right.height + 1

/-- This linear height bound needs no balance invariant. A logarithmic bound
requires a separately proved construction or maintenance algorithm. -/
theorem height_add_one_le_leafCount (d : Decomposition C) :
    d.height + 1 ≤ d.leafCount := by
  induction d with
  | edge hab => rfl
  | join h left right ihl ihr =>
    have hl := left.leafCount_pos
    have hr := right.leafCount_pos
    simp only [height, leafCount, edges, List.length_append] at *
    omega

/-- Bottom-up application data computed from edge and join operations. -/
def fold {α : Type v} (leaf : Sym2 V → α) (merge : α → α → α) :
    {C : Cluster G exposed} → Decomposition C → α
  | _, .edge (a := a) (b := b) _ => leaf s(a, b)
  | _, .join _ left right => merge (left.fold leaf merge) (right.fold leaf merge)

/-- Application invariants need proofs only for single edges and legal joins;
the decomposition and recursive transport are handled here. -/
theorem fold_spec {α : Type v} (leaf : Sym2 V → α) (merge : α → α → α)
    (P : Cluster G exposed → α → Prop)
    (hleaf : ∀ {a b} (hab : G.Adj a b), P (Cluster.edge exposed hab) (leaf s(a, b)))
    (hjoin : ∀ {A B pivot} (h : Joinable A B pivot) {x y},
      P A x → P B y → P (Cluster.join A B h) (merge x y))
    (d : Decomposition C) : P C (d.fold leaf merge) := by
  induction d with
  | edge hab => exact hleaf hab
  | join h left right ihl ihr => exact hjoin h ihl ihr

/-- For additive summaries the fold counts every represented edge exactly once. -/
theorem fold_add_eq_sum {α : Type v} [AddMonoid α] (weight : Sym2 V → α)
    (d : Decomposition C) : d.fold weight (· + ·) = (d.edges.map weight).sum := by
  induction d with
  | edge hab => simp [fold, edges]
  | join h left right ihl ihr => simp [fold, edges, ihl, ihr, List.sum_append]

/-- A commutative edge aggregate is independent of the legal decomposition's shape
and child order. This is a summary-correctness rule, not a balancing algorithm. -/
theorem fold_add_eq_fold {α : Type v} [AddCommMonoid α] (weight : Sym2 V → α)
    (d d' : Decomposition C) : d.fold weight (· + ·) = d'.fold weight (· + ·) := by
  rw [fold_add_eq_sum, fold_add_eq_sum]
  exact ((d.edges_perm d').map weight).sum_eq

end Decomposition
end Cluster

/-- A complete top tree over one finite underlying tree and at most two exposed
vertices. An edgeless underlying tree has no root cluster. Balance and dynamic
updates are deliberately not fields of this mathematical representation. -/
structure TopTree (G : SimpleGraph V) (exposed : Set V) where
  tree : G.IsTree
  exposed_finite : exposed.Finite
  exposed_le_two : exposed.ncard ≤ 2
  /-- Empty for the single-vertex tree; otherwise the complete root decomposition. -/
  root : Option (Σ C : Cluster G exposed, Cluster.Decomposition C)
  /-- A nonempty root covers vertices as well as edges of the underlying tree. -/
  covers : match root with
    | none => G.edgeSet = ∅
    | some root => root.1.graph = ⊤

namespace TopTree

/-- Complete a nonempty decomposition once its root is known to cover the tree. -/
def ofDecomposition {C : Cluster G exposed} (hG : G.IsTree)
    (d : Cluster.Decomposition C) (hcover : C.graph = ⊤) : TopTree G exposed where
  tree := hG
  exposed_finite := by simpa [Cluster.boundary, hcover] using C.boundary_finite
  exposed_le_two := by simpa [hcover] using C.boundary_le_two
  root := some ⟨C, d⟩
  covers := hcover

/-- The empty top tree for an edgeless connected tree. -/
def empty (hG : G.IsTree) (hedges : G.edgeSet = ∅)
    (hfinite : exposed.Finite) (hbound : exposed.ncard ≤ 2) : TopTree G exposed where
  tree := hG
  exposed_finite := hfinite
  exposed_le_two := hbound
  root := none
  covers := hedges

/-- The leaf enumeration, empty when the underlying tree has no edge. -/
def edges (t : TopTree G exposed) : List (Sym2 V) :=
  match t.root with
  | none => []
  | some root => root.2.edges

@[simp]
theorem mem_edges (t : TopTree G exposed) (e : Sym2 V) :
    e ∈ t.edges ↔ e ∈ G.edgeSet := by
  cases hroot : t.root with
  | none =>
    have hcover : G.edgeSet = ∅ := by simpa [hroot] using t.covers
    simp [edges, hroot, hcover]
  | some root =>
    have hcover : root.1.graph = ⊤ := by simpa [hroot] using t.covers
    simp [edges, hroot, root.2.mem_edges, hcover]

theorem edges_nodup (t : TopTree G exposed) : t.edges.Nodup := by
  cases hroot : t.root with
  | none => simp [edges, hroot]
  | some root => simpa [edges, hroot] using root.2.edges_nodup

end TopTree
end SimpleGraph
