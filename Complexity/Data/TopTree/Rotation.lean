/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.TopTree.Decomposition

/-!
# Legal local top-tree rotations

A right rotation changes `((A B) C)` to `(A (B C))`; a left rotation reverses it.
The original joins do not imply that the new middle cluster has at most two
boundaries. Given joins at `p` and `q`, right rotation needs exactly that `q`
belongs to `B` and that the actual boundary of `B ∪ C` has size at most two.
The remaining intersection and parent-boundary obligations are derived here.
The common points may coincide and may be exposed.

`Reassociation` packages the checked local geometry. Its rotation operations
construct new join nodes around the original three child decompositions, retaining
the same root cluster and the exact edge-leaf order. This is a mathematical local
operation with supplied legality proofs, not an algorithm for locating nodes,
deciding those proofs, balancing a dynamic forest, or compiling updates to RAM.
-/

namespace SimpleGraph
namespace Cluster

universe u v

variable {V : Type u} {G : SimpleGraph V} {exposed : Set V}

/-- The subgraph determines a cluster; its remaining fields are verified properties. -/
@[ext]
theorem ext_graph {A B : Cluster G exposed} (h : A.graph = B.graph) : A = B := by
  cases A
  cases B
  cases h
  rfl

namespace Joinable

variable {A B C : Cluster G exposed} {p q : V}

/-- The new inner join needs only its actual boundary bound and the old outer
intersection vertex in the middle child. Its single-vertex intersection follows. -/
theorem reassociate_inner (hAB : Joinable A B p)
    (hABC : Joinable (join A B hAB) C q) (hq : q ∈ B.graph.verts)
    (hboundary : ((B.graph ⊔ C.graph).clusterBoundary exposed).ncard ≤ 2) :
    Joinable B C q where
  intersection := by
    ext x
    constructor
    · rintro ⟨hxB, hxC⟩
      exact hABC.eq_pivot (Or.inr hxB) hxC
    · rintro rfl
      exact ⟨hq, hABC.pivot_mem_right⟩
  boundary_le_two := hboundary

/-- Once the new inner join is legal, all outer-join conditions follow from the
original joins. In particular, the final parent boundary need not be reproved. -/
theorem reassociate_outer (hAB : Joinable A B p)
    (hABC : Joinable (join A B hAB) C q) (hBC : Joinable B C q) :
    Joinable A (join B C hBC) p where
  intersection := by
    ext x
    constructor
    · rintro ⟨hxA, hxB | hxC⟩
      · exact hAB.eq_pivot hxA hxB
      · have hxq := hABC.eq_pivot (Or.inl hxA) hxC
        exact hAB.eq_pivot hxA (hxq ▸ hBC.pivot_mem_left)
    · rintro rfl
      exact ⟨hAB.pivot_mem_left, Or.inl hAB.pivot_mem_right⟩
  boundary_le_two := by
    simpa only [join_graph, sup_assoc] using hABC.boundary_le_two

/-- These are necessary as well as sufficient conditions for the specified
reassociation: no new connectivity, disjointness or parent-cap premises are needed. -/
theorem exists_reassociate_iff (hAB : Joinable A B p)
    (hABC : Joinable (join A B hAB) C q) :
    (∃ hBC : Joinable B C q, Joinable A (join B C hBC) p) ↔
      q ∈ B.graph.verts ∧ ((B.graph ⊔ C.graph).clusterBoundary exposed).ncard ≤ 2 := by
  constructor
  · rintro ⟨hBC, _⟩
    exact ⟨hBC.pivot_mem_left, hBC.boundary_le_two⟩
  · rintro ⟨hq, hboundary⟩
    let hBC := hAB.reassociate_inner hABC hq hboundary
    exact ⟨hBC, hAB.reassociate_outer hABC hBC⟩

/-- The symmetric inner-join rule used by a left rotation. -/
theorem reassociate_inner_left (hBC : Joinable B C q)
    (hABC : Joinable A (join B C hBC) p) (hp : p ∈ B.graph.verts)
    (hboundary : ((A.graph ⊔ B.graph).clusterBoundary exposed).ncard ≤ 2) :
    Joinable A B p where
  intersection := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      exact hABC.eq_pivot hxA (Or.inl hxB)
    · rintro rfl
      exact ⟨hABC.pivot_mem_left, hp⟩
  boundary_le_two := hboundary

/-- The symmetric parent-join rule used by a left rotation. -/
theorem reassociate_outer_left (hBC : Joinable B C q)
    (hABC : Joinable A (join B C hBC) p) (hAB : Joinable A B p) :
    Joinable (join A B hAB) C q where
  intersection := by
    ext x
    constructor
    · rintro ⟨hxA | hxB, hxC⟩
      · have hxp := hABC.eq_pivot hxA (Or.inr hxC)
        exact hBC.eq_pivot (hxp ▸ hAB.pivot_mem_right) hxC
      · exact hBC.eq_pivot hxB hxC
    · rintro rfl
      exact ⟨Or.inr hBC.pivot_mem_left, hBC.pivot_mem_right⟩
  boundary_le_two := by
    simpa only [join_graph, sup_assoc] using hABC.boundary_le_two

end Joinable

/-- Legal geometry for the two associations of three adjacent child clusters.
Only the new inner join is stored; its parent is derived from the other joins. -/
structure Reassociation (A B C : Cluster G exposed) (p q : V) : Prop where
  leftJoin : Joinable A B p
  leftParent : Joinable (join A B leftJoin) C q
  rightJoin : Joinable B C q

namespace Reassociation

variable {A B C : Cluster G exposed} {p q : V}

/-- Build the local rotation geometry from the left-associated shape. -/
theorem ofLeft (hAB : Joinable A B p) (hABC : Joinable (join A B hAB) C q)
    (hq : q ∈ B.graph.verts)
    (hboundary : ((B.graph ⊔ C.graph).clusterBoundary exposed).ncard ≤ 2) :
    Reassociation A B C p q :=
  ⟨hAB, hABC, hAB.reassociate_inner hABC hq hboundary⟩

/-- Build the local rotation geometry from the right-associated shape. -/
theorem ofRight (hBC : Joinable B C q) (hABC : Joinable A (join B C hBC) p)
    (hp : p ∈ B.graph.verts)
    (hboundary : ((A.graph ⊔ B.graph).clusterBoundary exposed).ncard ≤ 2) :
    Reassociation A B C p q := by
  let hAB := hBC.reassociate_inner_left hABC hp hboundary
  exact ⟨hAB, hBC.reassociate_outer_left hABC hAB, hBC⟩

variable (r : Reassociation A B C p q)

/-- The right-associated parent's legality is shared derived information. -/
theorem rightParent : Joinable A (join B C r.rightJoin) p :=
  r.leftJoin.reassociate_outer r.leftParent r.rightJoin

/-- Root cluster of the left-associated shape. -/
def leftCluster : Cluster G exposed := join (join A B r.leftJoin) C r.leftParent

/-- Root cluster of the right-associated shape. -/
def rightCluster : Cluster G exposed := join A (join B C r.rightJoin) r.rightParent

/-- Reassociation preserves the complete root subgraph, hence its vertices, edges,
exposed boundary and any complete-tree coverage property. -/
theorem cluster_eq : r.leftCluster = r.rightCluster := by
  apply ext_graph
  exact sup_assoc A.graph B.graph C.graph

end Reassociation

namespace Decomposition

/-- Transport a decomposition across an equality of its mathematical root cluster. -/
def cast {C D : Cluster G exposed} (h : C = D) (d : Decomposition C) : Decomposition D :=
  h ▸ d

@[simp]
theorem edges_cast {C D : Cluster G exposed} (h : C = D) (d : Decomposition C) :
    (d.cast h).edges = d.edges := by cases h; rfl

@[simp]
theorem height_cast {C D : Cluster G exposed} (h : C = D) (d : Decomposition C) :
    (d.cast h).height = d.height := by cases h; rfl

end Decomposition

namespace Reassociation

variable {A B C : Cluster G exposed} {p q : V}
variable (r : Reassociation A B C p q)
variable (a : Decomposition A) (b : Decomposition B) (c : Decomposition C)

/-- The original left-associated local decomposition. -/
def left : Decomposition r.leftCluster := .join r.leftParent (.join r.leftJoin a b) c

/-- The original right-associated local decomposition. -/
def right : Decomposition r.rightCluster := .join r.rightParent a (.join r.rightJoin b c)

/-- Right rotation `((A B) C) → (A (B C))`, reusing the three actual children.
The result keeps the old root type, so it can replace the original subtree. -/
def rotateRight : Decomposition r.leftCluster :=
  (r.right a b c).cast r.cluster_eq.symm

/-- Left rotation `(A (B C)) → ((A B) C)`, reusing the three actual children. -/
def rotateLeft : Decomposition r.rightCluster :=
  (r.left a b c).cast r.cluster_eq

/-- Rotation preserves exact left-to-right edge order, not only the edge set. -/
@[simp]
theorem edges_rotateRight : (r.rotateRight a b c).edges = (r.left a b c).edges := by
  simp [rotateRight, right, left, Decomposition.edges, List.append_assoc]

@[simp]
theorem edges_rotateLeft : (r.rotateLeft a b c).edges = (r.right a b c).edges := by
  simp [rotateLeft, right, left, Decomposition.edges, List.append_assoc]

/-- Additive summaries survive rotation without requiring commutativity, because
the stronger exact leaf-order theorem can reuse the existing fold-to-sum rule. -/
theorem fold_add_rotateRight {α : Type v} [AddMonoid α] (weight : Sym2 V → α) :
    (r.rotateRight a b c).fold weight (· + ·) = (r.left a b c).fold weight (· + ·) := by
  simp only [Decomposition.fold_add_eq_sum, edges_rotateRight]

theorem fold_add_rotateLeft {α : Type v} [AddMonoid α] (weight : Sym2 V → α) :
    (r.rotateLeft a b c).fold weight (· + ·) = (r.right a b c).fold weight (· + ·) := by
  simp only [Decomposition.fold_add_eq_sum, edges_rotateLeft]

/-- The actual rotated shape's height. Rotation alone does not imply improvement. -/
theorem height_rotateRight :
    (r.rotateRight a b c).height = max a.height (max b.height c.height + 1) + 1 := by
  simp [rotateRight, right, Decomposition.height]

theorem height_rotateLeft :
    (r.rotateLeft a b c).height = max (max a.height b.height + 1) c.height + 1 := by
  simp [rotateLeft, left, Decomposition.height]

end Reassociation
end Cluster
end SimpleGraph
