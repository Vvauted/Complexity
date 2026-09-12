/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Node.Basic
import Complexity.Language.Eval.Verification
import Complexity.Language.Representation.List

/-!
# Native specifications for shared node actions

The default `@[spec]` rules expose the existing heap operations: cons appends
one actual node, and read uses a successful typed lookup in the current heap.
Neither rule requires a complete linked-list observation or scans a tail.

The separate list conveniences transport these same rules through
`Representation.list`. They supply the ordinary cons contents and shared tail,
preserving old list observations and the actual heap effects. No rule turns a
merely existing identifier into a valid list or assumes its tail is rooted.

These rules describe shared `ExceptT Fault (StateT Heap Part)` heap actions.
They do not add typed statements, frontend syntax, another execution semantics
or machine instruction costs.
-/

namespace Complexity.Language.NodeRef

open scoped Part.TotalCorrectness

/-- Cons always allocates its actual fresh node, without inspecting the tail.
The continuation receives the exact heap operation, node lookup, shape growth
and fresh identity; a dangling input tail is not silently certified as a list. -/
@[spec] theorem consM_spec {kind : CellTy} (head : CellValue kind)
    (tail : Option (NodeRef kind))
    (post : Std.Do.PostCond (NodeRef kind) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (consM head tail)
      (fun heap => ⟨∀ ref finish,
        heap.cons head tail = (ref, finish) →
        finish.node? kind ref.object = some (head, tail) →
        heap.ShapeExtends finish → ref.object = heap.objects.size →
        (post.1 ref finish).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap property
  exact ⟨(.ok (heap.cons head tail).1, (heap.cons head tail).2),
    Part.eq_some_iff.mp (consM_eq_ok head tail heap),
    property _ _ rfl (heap.node?_cons_new head tail)
      (heap.shapeExtends_cons head tail) (heap.cons_object head tail)⟩

/-- A successful typed lookup returns the actual head and identical tail
reference, preserving the complete heap. It need not describe a finite list. -/
@[spec] theorem readM_spec {kind : CellTy} (ref : NodeRef kind)
    (post : Std.Do.PostCond (CellValue kind × Option (NodeRef kind))
      (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple ref.readM
      (fun heap => ⟨∃ head tail, heap.node? kind ref.object = some (head, tail) ∧
        (post.1 (head, tail) heap).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap ⟨head, tail, found, property⟩
  exact ⟨(.ok (head, tail), heap), Part.eq_some_iff.mp (readM_eq_ok found), property⟩

/-- With a represented tail, the same cons action constructs `head :: values`.
Every old represented list survives, including lists sharing that tail; the
actual allocation equation remains available for other heap observations. -/
theorem consM_list_spec {kind : CellTy} (head : CellValue kind)
    (tail : Option (NodeRef kind))
    (post : Std.Do.PostCond (NodeRef kind) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (consM head tail)
      (fun heap => ⟨∃ values : List (CellValue kind),
        (Representation.list kind).Rel values tail heap ∧
        ∀ ref finish, heap.cons head tail = (ref, finish) →
          (Representation.list kind).Rel (head :: values) (some ref) finish →
          (∀ {otherKind : CellTy} {root : Option (NodeRef otherKind)}
              {oldValues : List (CellValue otherKind)},
            (Representation.list otherKind).Rel oldValues root heap →
            (Representation.list otherKind).Rel oldValues root finish) →
          (post.1 ref finish).down⟩) post := by
  have specification := consM_spec head tail post
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp] at specification ⊢
  intro heap ⟨values, observed, property⟩
  apply specification heap
  intro ref finish allocated _ preserved _
  have contents : (Representation.list kind).Rel (head :: values) (some ref) finish := by
    simpa only [allocated] using Representation.list_cons head observed
  exact property ref finish allocated contents
    (fun old => Representation.list_mono old preserved)

/-- A represented nonempty list supplies the actual head and shared tail of
the same heap lookup. The continuation receives the tail's ordinary contents;
no copy, tail traversal or heap mutation occurs. -/
theorem readM_list_spec {kind : CellTy} (ref : NodeRef kind)
    (post : Std.Do.PostCond (CellValue kind × Option (NodeRef kind))
      (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple ref.readM
      (fun heap => ⟨∃ head rest,
        (Representation.list kind).Rel (head :: rest) (some ref) heap ∧
        ∀ tail, heap.node? kind ref.object = some (head, tail) →
          (Representation.list kind).Rel rest tail heap →
          (post.1 (head, tail) heap).down⟩) post := by
  have specification := readM_spec ref post
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp] at specification ⊢
  intro heap ⟨head, rest, observed, property⟩
  change Contents heap (some ref) (head :: rest) at observed
  cases observed with
  | cons found contents =>
      exact specification heap ⟨_, _, found, property _ found contents⟩

end Complexity.Language.NodeRef
