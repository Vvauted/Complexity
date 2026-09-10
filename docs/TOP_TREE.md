# Top trees and clusters

This is a mathematical foundation for a future dynamic-tree implementation,
not a claim that a logarithmic-time RAM implementation already exists.

The definitions follow §2 of Alstrup, Holm, de Lichtenberg and Thorup,
[Maintaining Information in Fully-Dynamic Trees with Top Trees](https://arxiv.org/pdf/cs/0310065).
A cluster is a finite connected nonempty edge subgraph with at most two
boundaries. A vertex is a boundary exactly when it is exposed or incident to
an ambient edge outside the cluster. Leaves represent individual edges;
neighbors meet in one vertex; their parent is their union. The complete root
covers the underlying tree. An edgeless tree has no root cluster.

## Representation and reusable proofs

[Basic](../Complexity/Data/TopTree/Basic.lean) uses mathlib's
`SimpleGraph.Subgraph`, `Connected`, `IsAcyclic`, `Path` and set cardinality.
Its finite-vertex condition ensures that the natural-number boundary cardinality
cannot accidentally accept an infinite set. Connectivity and an actual edge
imply every represented vertex is an edge endpoint; extra isolated vertices are
not permitted.

`Cluster.Joinable` asks for single-vertex overlap and the actual parent's
boundary bound. Edge-disjointness, connectivity and finiteness then follow
through shared proofs. The common vertex belongs to both child boundaries, but
may remain a parent boundary. The exact rules distinguish exposure and edges
outside both children; the shared vertex is never blindly removed.
The nested-boundary theorem lets a subcluster inherit the parent's interface
without restating its relation to the whole ambient graph.

[Decomposition](../Complexity/Data/TopTree/Decomposition.lean) supplies:

- A typed single-edge/valid-join decomposition and `split`/`rejoin` round trip.
- A leaf list proved to cover each represented edge exactly once.
- Exactly one fewer join nodes than leaves, and the unconditional linear
  height bound. Neither is a logarithmic-height theorem.
- `fold_spec`: an application proves its summary invariant for an edge and a
  legal join; the shared rule supplies induction and decomposition transport.
  Additive folds agree with the sum of actual edge weights in leaf order.
- Any two legal decompositions of the same root have permutation-equivalent
  leaf lists. Commutative edge aggregates are therefore independent of the
  decomposition shape and child ordering, without another induction per client.

[Paths](../Complexity/Data/TopTree/Paths.lean) proves child-path concatenation
and the unweighted distance identity through the common vertex. It uses actual
mathlib paths and ambient distances, including endpoints equal to the common
vertex. This supplies a mathematical composition rule for later path summaries.

`SimpleGraph.TopTree` records a complete underlying `IsTree`, the exposed set,
and an optional root. `ofDecomposition` derives the exposed-set conditions from
the proved complete root instead of asking clients to duplicate them.

[Rotation](../Complexity/Data/TopTree/Rotation.lean) constructs legal local
reassociations `((A B) C) ↔ (A (B C))`. For a right rotation, the old outer join
vertex must belong to the middle child, and the new middle cluster must really
have at most two boundaries. These conditions are necessary and sufficient;
the other intersection and final-parent conditions follow from the old joins.
The new decomposition preserves the complete root and exact edge-leaf order,
so even noncommutative additive summaries are retained. The two join vertices
may coincide. A rotation does not by itself lower the height or identify a
node to rotate; the module supplies no dynamic balancing or runtime cost claim.

## What remains

The current objects are immutable mathematical descriptions. Still required:

1. A concrete node representation and maintained summary data, with graph and
   boundary correspondence. Weighted paths and diameter/nearest-marked summaries
   need their own composition laws; a generic fold alone does not prove them.
2. Actual expose, link and cut algorithms, respecting cluster changes and
   lifetime/ownership. Exposing an internal vertex may require splitting a
   cluster: updating a field alone does not preserve the boundary bound.
3. A proved balancing or amortization argument for those operations, including
   the cost of locating affected clusters. A balance assumption in a record
   would not implement or establish dynamic logarithmic complexity.
4. Source-language implementation, heap correspondence and the existing
   verified RAM compilation/resource connection for that same implementation.

These modules intentionally import no RAM semantics and introduce no alternate
graph, cost interpreter or unchecked per-operation annotations.
