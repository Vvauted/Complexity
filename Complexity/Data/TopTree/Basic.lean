/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Top-tree clusters

A cluster is a finite connected subgraph with at least one edge and at most two
boundary vertices. Boundaries are determined by the ambient graph and its exposed
vertices, not supplied as an arbitrary annotation. The graph and connectivity
interfaces are mathlib's `SimpleGraph.Subgraph` and `Subgraph.Connected`.

Clusters can be considered in any ambient graph; in a forest their underlying
graphs are trees. A legal join has a single common vertex and a union with at most
two boundaries. In particular, its common vertex need not become internal.
-/

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace Subgraph

/-- Vertices exposed externally or incident to an ambient edge outside the subgraph. -/
def clusterBoundary (H : G.Subgraph) (exposed : Set V) : Set V :=
  {v | v ∈ H.verts ∧ (v ∈ exposed ∨ ∃ w, G.Adj v w ∧ ¬H.Adj v w)}

@[simp]
theorem mem_clusterBoundary {H : G.Subgraph} {exposed : Set V} {v : V} :
    v ∈ H.clusterBoundary exposed ↔
      v ∈ H.verts ∧ (v ∈ exposed ∨ ∃ w, G.Adj v w ∧ ¬H.Adj v w) := Iff.rfl

theorem clusterBoundary_subset (H : G.Subgraph) (exposed : Set V) :
    H.clusterBoundary exposed ⊆ H.verts := fun _ h => h.1

@[simp]
theorem clusterBoundary_top (exposed : Set V) :
    (⊤ : G.Subgraph).clusterBoundary exposed = exposed := by
  ext v
  simp [clusterBoundary]

/-- Exposing more vertices cannot remove a boundary. -/
theorem clusterBoundary_mono_exposed (H : G.Subgraph) {X Y : Set V} (h : X ⊆ Y) :
    H.clusterBoundary X ⊆ H.clusterBoundary Y := by
  rintro v ⟨hv, hx | houtside⟩
  · exact ⟨hv, Or.inl (h hx)⟩
  · exact ⟨hv, Or.inr houtside⟩

/-- Exposing new vertices changes exactly the vertices of this subgraph that
were not already boundaries. No edge or graph data changes. -/
theorem clusterBoundary_union_exposed (H : G.Subgraph) (X Y : Set V) :
    H.clusterBoundary (X ∪ Y) = H.clusterBoundary X ∪ (H.verts ∩ Y) := by
  ext v
  simp only [mem_clusterBoundary, Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro ⟨hv, (hx | hy) | houtside⟩
    · exact Or.inl ⟨hv, Or.inl hx⟩
    · exact Or.inr ⟨hv, hy⟩
    · exact Or.inl ⟨hv, Or.inr houtside⟩
  · rintro (⟨hv, hx | houtside⟩ | ⟨hv, hy⟩)
    · exact ⟨hv, Or.inl (Or.inl hx)⟩
    · exact ⟨hv, Or.inr houtside⟩
    · exact ⟨hv, Or.inl (Or.inr hy)⟩

/-- The boundaries inherited through an enclosing subgraph agree with the ambient
boundaries. This is expressed on the original vertex type, avoiding subtype transport. -/
theorem mem_clusterBoundary_iff_of_le {A C : G.Subgraph} (hAC : A ≤ C)
    (exposed : Set V) (v : V) :
    v ∈ A.clusterBoundary exposed ↔
      v ∈ A.verts ∧
        (v ∈ C.clusterBoundary exposed ∨ ∃ w, C.Adj v w ∧ ¬A.Adj v w) := by
  classical
  constructor
  · rintro ⟨hv, hx | ⟨w, hvw, hnot⟩⟩
    · exact ⟨hv, Or.inl ⟨hAC.1 hv, Or.inl hx⟩⟩
    · by_cases hC : C.Adj v w
      · exact ⟨hv, Or.inr ⟨w, hC, hnot⟩⟩
      · exact ⟨hv, Or.inl ⟨hAC.1 hv, Or.inr ⟨w, hvw, hC⟩⟩⟩
  · rintro ⟨hv, ⟨_, hx | ⟨w, hvw, hnot⟩⟩ | ⟨w, hvw, hnot⟩⟩
    · exact ⟨hv, Or.inl hx⟩
    · exact ⟨hv, Or.inr ⟨w, hvw, fun hA => hnot (hAC.2 hA)⟩⟩
    · exact ⟨hv, Or.inr ⟨w, C.adj_sub hvw, hnot⟩⟩

/-- A parent's boundaries come from its children; joining introduces none. -/
theorem clusterBoundary_sup_subset (H K : G.Subgraph) (exposed : Set V) :
    (H ⊔ K).clusterBoundary exposed ⊆
      H.clusterBoundary exposed ∪ K.clusterBoundary exposed := by
  rintro v ⟨hv | hv, hx | ⟨w, hadj, hnot⟩⟩
  · exact Or.inl ⟨hv, Or.inl hx⟩
  · exact Or.inl ⟨hv, Or.inr ⟨w, hadj, fun h => hnot (Or.inl h)⟩⟩
  · exact Or.inr ⟨hv, Or.inl hx⟩
  · exact Or.inr ⟨hv, Or.inr ⟨w, hadj, fun h => hnot (Or.inr h)⟩⟩

end Subgraph

/-- A finite, nonempty-edge cluster relative to a chosen exposed vertex set.
For an acyclic ambient graph, `Cluster.isTree` recovers the usual subtree property. -/
structure Cluster (G : SimpleGraph V) (exposed : Set V) where
  /-- The represented connected edge subgraph. -/
  graph : G.Subgraph
  connected : graph.Connected
  edge_nonempty : ∃ u v, graph.Adj u v
  finite_verts : graph.verts.Finite
  boundary_le_two : (graph.clusterBoundary exposed).ncard ≤ 2

namespace Cluster

variable {exposed : Set V}

/-- The exact external interface of a cluster. -/
abbrev boundary (C : Cluster G exposed) : Set V := C.graph.clusterBoundary exposed

theorem boundary_finite (C : Cluster G exposed) : C.boundary.Finite :=
  C.finite_verts.subset (C.graph.clusterBoundary_subset exposed)

/-- Every cluster vertex is an endpoint of a represented edge; isolated extra vertices
cannot be smuggled into a connected nonempty-edge cluster. -/
theorem exists_adj (C : Cluster G exposed) {v : V} (hv : v ∈ C.graph.verts) :
    ∃ w, C.graph.Adj v w := by
  obtain ⟨a, b, hab⟩ := C.edge_nonempty
  letI : Nontrivial C.graph.verts :=
    ⟨⟨⟨a, hab.fst_mem⟩, ⟨b, hab.snd_mem⟩,
      fun h => hab.ne (congrArg Subtype.val h)⟩⟩
  exact C.connected.preconnected.exists_adj_of_nontrivial ⟨v, hv⟩

theorem isTree (C : Cluster G exposed) (hG : G.IsAcyclic) : C.graph.coe.IsTree :=
  ⟨C.connected.coe, hG.subgraph C.graph⟩

/-- The cluster path is uniquely determined by its endpoints in a forest.
The paths themselves are mathlib paths, not a new representation. -/
theorem existsUnique_path (C : Cluster G exposed) (hG : G.IsAcyclic)
    (a b : C.graph.verts) : ∃! _ : C.graph.coe.Path a b, True := by
  obtain ⟨p, hp⟩ := C.connected.coe.exists_isPath a b
  exact ⟨⟨p, hp⟩, trivial, fun q _ => (hG.subgraph C.graph).path_unique q ⟨p, hp⟩⟩

/-- Every ambient edge is a cluster, regardless of which vertices are exposed. -/
def edge (exposed : Set V) {a b : V} (hab : G.Adj a b) : Cluster G exposed where
  graph := G.subgraphOfAdj hab
  connected := Subgraph.subgraphOfAdj_connected hab
  edge_nonempty := ⟨a, b, rfl⟩
  finite_verts := (Set.finite_singleton b).insert a
  boundary_le_two := by
    calc
      _ ≤ (G.subgraphOfAdj hab).verts.ncard :=
        Set.ncard_le_ncard ((G.subgraphOfAdj hab).clusterBoundary_subset exposed)
          ((Set.finite_singleton b).insert a)
      _ = 2 := Set.ncard_pair hab.ne

@[simp]
theorem edge_graph (exposed : Set V) {a b : V} (hab : G.Adj a b) :
    (edge exposed hab).graph = G.subgraphOfAdj hab := rfl

/-- A join is legal only when the children meet in one vertex and the actual union
still has at most two boundaries. No balancing or running-time assertion is included. -/
structure Joinable (A B : Cluster G exposed) (pivot : V) : Prop where
  intersection : A.graph.verts ∩ B.graph.verts = {pivot}
  boundary_le_two : ((A.graph ⊔ B.graph).clusterBoundary exposed).ncard ≤ 2

namespace Joinable

variable {A B : Cluster G exposed} {pivot : V} (h : Joinable A B pivot)

include h

theorem pivot_mem_left : pivot ∈ A.graph.verts := by
  have : pivot ∈ A.graph.verts ∩ B.graph.verts := by rw [h.intersection]; simp
  exact this.1

theorem pivot_mem_right : pivot ∈ B.graph.verts := by
  have : pivot ∈ A.graph.verts ∩ B.graph.verts := by rw [h.intersection]; simp
  exact this.2

theorem eq_pivot {v : V} (hA : v ∈ A.graph.verts) (hB : v ∈ B.graph.verts) :
    v = pivot := by
  have : v ∈ A.graph.verts ∩ B.graph.verts := ⟨hA, hB⟩
  simpa [h.intersection] using this

theorem not_adj_both {u v : V} (hA : A.graph.Adj u v) : ¬B.graph.Adj u v := by
  intro hB
  exact hA.ne ((h.eq_pivot hA.fst_mem hB.fst_mem).trans
    (h.eq_pivot hA.snd_mem hB.snd_mem).symm)

/-- Single-vertex overlap implies edge-disjointness, without another assumption. -/
theorem disjoint_edgeSet : Disjoint A.graph.edgeSet B.graph.edgeSet := by
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | h u v => exact h.not_adj_both

theorem symm : Joinable B A pivot where
  intersection := by rw [Set.inter_comm]; exact h.intersection
  boundary_le_two := by rw [sup_comm]; exact h.boundary_le_two

/-- The common vertex belongs to both child boundaries, even if it disappears
from the parent's boundary. -/
theorem pivot_mem_boundary_left : pivot ∈ A.boundary := by
  obtain ⟨w, hadj⟩ := B.exists_adj h.pivot_mem_right
  exact ⟨h.pivot_mem_left, Or.inr ⟨w, B.graph.adj_sub hadj,
    fun hA => h.not_adj_both hA hadj⟩⟩

theorem pivot_mem_boundary_right : pivot ∈ B.boundary :=
  h.symm.pivot_mem_boundary_left

end Joinable

/-- Join two neighboring clusters using their actual subgraph union. -/
def join (A B : Cluster G exposed) {pivot : V} (h : Joinable A B pivot) :
    Cluster G exposed where
  graph := A.graph ⊔ B.graph
  connected := Subgraph.connected_sup A.connected.preconnected B.connected.preconnected
    ⟨pivot, h.pivot_mem_left, h.pivot_mem_right⟩
  edge_nonempty := by
    obtain ⟨u, v, huv⟩ := A.edge_nonempty
    exact ⟨u, v, Or.inl huv⟩
  finite_verts := A.finite_verts.union B.finite_verts
  boundary_le_two := h.boundary_le_two

@[simp]
theorem join_graph (A B : Cluster G exposed) {pivot : V} (h : Joinable A B pivot) :
    (join A B h).graph = A.graph ⊔ B.graph := rfl

theorem boundary_join_subset {A B : Cluster G exposed} {pivot : V}
    (h : Joinable A B pivot) : (join A B h).boundary ⊆ A.boundary ∪ B.boundary :=
  A.graph.clusterBoundary_sup_subset B.graph exposed

/-- Away from the common vertex a join preserves precisely the child boundaries. -/
theorem mem_boundary_join_iff_of_ne {A B : Cluster G exposed} {pivot v : V}
    (h : Joinable A B pivot) (hne : v ≠ pivot) :
    v ∈ (join A B h).boundary ↔ v ∈ A.boundary ∪ B.boundary := by
  constructor
  · exact fun hv => boundary_join_subset h hv
  · rintro (⟨hv, hx | ⟨w, hadj, hnot⟩⟩ | ⟨hv, hx | ⟨w, hadj, hnot⟩⟩)
    · exact ⟨Or.inl hv, Or.inl hx⟩
    · refine ⟨Or.inl hv, Or.inr ⟨w, hadj, ?_⟩⟩
      rintro (hA | hB)
      · exact hnot hA
      · exact hne (h.eq_pivot hv hB.fst_mem)
    · exact ⟨Or.inr hv, Or.inl hx⟩
    · refine ⟨Or.inr hv, Or.inr ⟨w, hadj, ?_⟩⟩
      rintro (hA | hB)
      · exact hne (h.eq_pivot hA.fst_mem hv)
      · exact hnot hB

/-- At the common vertex, exposure or an edge outside both children decides
whether the parent retains a boundary. -/
theorem pivot_mem_boundary_join_iff {A B : Cluster G exposed} {pivot : V}
    (h : Joinable A B pivot) :
    pivot ∈ (join A B h).boundary ↔
      pivot ∈ exposed ∨ ∃ w, G.Adj pivot w ∧ ¬A.graph.Adj pivot w ∧ ¬B.graph.Adj pivot w := by
  simp [boundary, Subgraph.clusterBoundary, join, h.pivot_mem_left,
    h.pivot_mem_right, not_or]

end Cluster
end SimpleGraph
