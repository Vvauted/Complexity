/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Data.TopTree.Basic

/-!
# Paths through neighboring clusters

The unique path between vertices in opposite children of a legal join passes
through the common vertex. Consequently the ambient graph distance is the sum
of the two child-side distances. These are mathematical composition rules for
top-tree summaries, independent of a particular dynamic-tree representation.
-/

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Every simple path in a forest realizes the graph distance. -/
theorem IsAcyclic.length_eq_dist (hG : G.IsAcyclic) {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) : p.length = G.dist a b := by
  obtain ⟨q, hq, hdist⟩ := p.reachable.exists_path_of_dist
  have heq : p = q := Subtype.mk.inj (hG.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  exact heq ▸ hdist

/-- Viewing a walk in the ambient graph does not add edges outside its subgraph. -/
theorem Subgraph.mem_edgeSet_of_mem_edges_map {H : G.Subgraph} {a b : H.verts}
    (p : H.coe.Walk a b) {e : Sym2 V} (he : e ∈ (p.map H.hom).edges) :
    e ∈ H.edgeSet := by
  rw [Walk.edges_map, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  have hf' := p.edges_subset_edgeSet hf
  simpa only [Subgraph.edgeSet_coe, Set.mem_preimage] using hf'

namespace Cluster
namespace Joinable

variable {exposed : Set V} {A B : Cluster G exposed} {pivot : V}

/-- Child paths meeting at the common vertex concatenate to a genuine simple
ambient path, not a walk with duplicated edges or vertices. -/
theorem isPath_append (h : Joinable A B pivot) (hG : G.IsAcyclic)
    {a b : V} (ha : a ∈ A.graph.verts) (hb : b ∈ B.graph.verts)
    (p : A.graph.coe.Walk ⟨a, ha⟩ ⟨pivot, h.pivot_mem_left⟩)
    (q : B.graph.coe.Walk ⟨pivot, h.pivot_mem_right⟩ ⟨b, hb⟩)
    (hp : p.IsPath) (hq : q.IsPath) :
    ((p.map A.graph.hom).append (q.map B.graph.hom)).IsPath := by
  rw [hG.isPath_iff_isTrail, Walk.isTrail_def, Walk.edges_append]
  refine List.Nodup.append
    (Walk.map_isPath_of_injective A.graph.hom_injective hp).isTrail.edges_nodup
    (Walk.map_isPath_of_injective B.graph.hom_injective hq).isTrail.edges_nodup ?_
  intro e he he'
  exact Set.disjoint_left.mp h.disjoint_edgeSet
    (Subgraph.mem_edgeSet_of_mem_edges_map p he)
    (Subgraph.mem_edgeSet_of_mem_edges_map q he')

/-- The same unique ambient path decomposes at the shared child boundary. -/
theorem dist_eq_add (h : Joinable A B pivot) (hG : G.IsAcyclic)
    {a b : V} (ha : a ∈ A.graph.verts) (hb : b ∈ B.graph.verts) :
    G.dist a b = G.dist a pivot + G.dist pivot b := by
  obtain ⟨p, hp⟩ := A.connected.coe.exists_isPath ⟨a, ha⟩ ⟨pivot, h.pivot_mem_left⟩
  obtain ⟨q, hq⟩ := B.connected.coe.exists_isPath ⟨pivot, h.pivot_mem_right⟩ ⟨b, hb⟩
  have hpath := h.isPath_append hG ha hb p q hp hq
  have hleft := hG.length_eq_dist (Walk.map_isPath_of_injective A.graph.hom_injective hp)
  have hright := hG.length_eq_dist (Walk.map_isPath_of_injective B.graph.hom_injective hq)
  have hwhole := hG.length_eq_dist hpath
  simpa only [Walk.length_append, hleft, hright] using hwhole.symm

end Joinable
end Cluster
end SimpleGraph
