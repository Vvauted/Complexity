/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.Representation.List.Prod
import Complexity.Language.RepresentedFunction
import Complexity.Language.Buffer.Copy
import Complexity.Language.Eval.Simp

/-!
# Actual linked operations for Boolean/natural pairs

Construction appends two immutable nodes and shares both tails. Decomposition
reads their stored fields and returns those same tails, without copying. The
mathematical contracts require synchronized chain observations; they do not
perform a whole-chain validation or grant operations to arbitrary host values.
-/

namespace Complexity.Language.List.Prod

source_program% Operations where
  def consBoolNat (head : Bool × Nat)
      (tail : Option (NodeRef Bool) × Option (NodeRef Nat)) :
      Option (NodeRef Bool) × Option (NodeRef Nat) := do
    let first ← NodeRef.cons head.1 tail.1
    let second ← NodeRef.cons head.2 tail.2
    return (some first, some second)

  def unconsBoolNat (roots : Option (NodeRef Bool) × Option (NodeRef Nat)) :
      Option ((Bool × Nat) × (Option (NodeRef Bool) × Option (NodeRef Nat))) := do
    match roots.1 with
    | none => return none
    | some first =>
      match roots.2 with
      | none => return none
      | some second =>
        let left ← first.read
        let right ← second.read
        return some ((left.1, right.1), (left.2, right.2))

namespace Operations

/-- Construction returns exactly the two fresh references and twice-extended heap. -/
theorem consBoolNat_eval (head : Bool × Nat)
    (tail : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap) :
    consBoolNat head tail heap =
      let first := heap.cons head.1 tail.1
      let second := first.2.cons head.2 tail.2
      Part.some (.ok (some first.1, some second.1), second.2) := by
  simp [consBoolNat_eq, source_eval]

/-- One mathematical pair cons preserves all old nodes and mutable contents.
The same actual final heap supplies the returned-list observation. -/
theorem consBoolNat_eval_exists_preserving (head : Bool × Nat)
    (values : List (Bool × Nat))
    (tail : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap)
    (observed : (Representation.listProd
      (Representation.list .bool) (Representation.list .nat)).Rel values tail heap) :
    ∃ returned finish,
      consBoolNat head tail heap = Part.some (.ok returned, finish) ∧
      (Representation.listProd (Representation.list .bool) (Representation.list .nat)).Rel
        (head :: values) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  refine ⟨_, _, consBoolNat_eval head tail heap,
    Representation.listProd_cons (left := .bool) (right := .nat) head observed,
    (heap.shapeExtends_cons head.1 tail.1).trans
      ((heap.cons head.1 tail.1).2.shapeExtends_cons head.2 tail.2), ?_⟩
  intro kind view contents old
  exact (old.mono_prefix (heap.objects_prefix_cons head.1 tail.1)).mono_prefix
    ((heap.cons head.1 tail.1).2.objects_prefix_cons head.2 tail.2)

/-- Decomposition observes ordinary head/tail at the identical heap.
Malformed roots outside the representation are not covered by this contract. -/
theorem unconsBoolNat_eval_exists (values : List (Bool × Nat))
    (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap)
    (observed : (Representation.listProd
      (Representation.list .bool) (Representation.list .nat)).Rel values roots heap) :
    ∃ returned,
      unconsBoolNat roots heap = Part.some (.ok returned, heap) ∧
      ((Representation.ofEmbedding (τ := .prod .bool .nat)
          (Function.Embedding.refl (Bool × Nat))).prod
        (Representation.listProd (Representation.list .bool) (Representation.list .nat))).option.Rel
        (values.head?.map (fun head => (head, values.tail))) returned heap := by
  rcases roots with ⟨left, right⟩
  rcases observed with ⟨leftContents, rightContents⟩
  cases values with
  | nil =>
      cases leftContents
      cases rightContents
      refine ⟨none, ?_, trivial⟩
      simp [unconsBoolNat_eq, source_eval]
  | cons head rest =>
      cases leftContents with
      | @cons leftRef _ leftTail _ leftFound leftRest =>
        cases rightContents with
        | @cons rightRef _ rightTail _ rightFound rightRest =>
          refine ⟨some (head, (leftTail, rightTail)), ?_, rfl, leftRest, rightRest⟩
          simp [unconsBoolNat_eq, source_eval, leftFound, rightFound]

end Operations

end Complexity.Language.List.Prod
