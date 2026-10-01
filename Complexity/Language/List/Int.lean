/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Prod
import Complexity.Language.Representation.List.Int

/-!
# Integer contracts for actual linked operations

The Boolean/natural operations themselves implement signed lists. These
contracts change only the mathematical observation: construction is ordinary
List.cons, and decomposition returns the ordinary optional head and tail.
No second source body, runtime decoder or uncharged traversal is introduced.
-/

namespace Complexity.Language.List.Prod.Operations

/-- The actual two-node constructor prepends an ordinary integer and preserves
all previous contents, including aliases of unrelated mutable buffers. -/
theorem consInt_eval_exists_preserving (head : Int) (values : List Int)
    (value : Bool × Nat) (tail : Option (NodeRef .bool) × Option (NodeRef .nat))
    (heap : Heap) (headObserved : Representation.int.Rel head value heap)
    (tailObserved : Representation.listInt.Rel values tail heap) :
    ∃ returned finish,
      consBoolNat value tail heap = Part.some (.ok returned, finish) ∧
      Representation.listInt.Rel (head :: values) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  change Representation.intEquiv head = value at headObserved
  rw [← headObserved]
  obtain ⟨returned, finish, executed, related, shape, contents⟩ :=
    consBoolNat_eval_exists_preserving (Representation.intEquiv head)
      (values.map Representation.intEquiv) tail heap tailObserved
  refine ⟨returned, finish, executed, ?_, shape, contents⟩
  simpa only [Representation.listInt_rel, List.map_cons] using related

/-- The source-level constructor contract observes the actual allocated result. -/
theorem consInt_eval_exists (head : Int) (values : List Int)
    (value : Bool × Nat) (tail : Option (NodeRef .bool) × Option (NodeRef .nat))
    (heap : Heap) (headObserved : Representation.int.Rel head value heap)
    (tailObserved : Representation.listInt.Rel values tail heap) :
    ∃ returned finish,
      consBoolNat value tail heap = Part.some (.ok returned, finish) ∧
      Representation.listInt.Rel (head :: values) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, executed, related, shape, _⟩ :=
    consInt_eval_exists_preserving head values value tail heap headObserved tailObserved
  exact ⟨returned, finish, executed, related, shape⟩

/-- Ordinary signed head/tail observations of the real two-node reader.
The entire heap is unchanged; the returned tails share their original nodes. -/
theorem unconsInt_eval_exists_heap_eq (values : List Int)
    (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap)
    (observed : Representation.listInt.Rel values roots heap) :
    ∃ returned,
      unconsBoolNat roots heap = Part.some (.ok returned, heap) ∧
      (Representation.int.prod Representation.listInt).option.Rel
        (values.head?.map (fun head => (head, values.tail))) returned heap := by
  obtain ⟨returned, executed, related⟩ :=
    unconsBoolNat_eval_exists (values.map Representation.intEquiv) roots heap observed
  refine ⟨returned, executed, ?_⟩
  cases values <;> cases returned <;>
    simp_all [Representation.option, Representation.prod, Representation.ofEmbedding,
      Representation.int, Representation.listInt, Representation.comap,
      Equiv.listEquivOfEquiv]

/-- Reading signed nodes leaves all previous mutable contents unchanged. -/
theorem unconsInt_eval_exists_preserving (values : List Int)
    (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap)
    (observed : Representation.listInt.Rel values roots heap) :
    ∃ returned finish,
      unconsBoolNat roots heap = Part.some (.ok returned, finish) ∧
      (Representation.int.prod Representation.listInt).option.Rel
        (values.head?.map (fun head => (head, values.tail))) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  obtain ⟨returned, executed, related⟩ := unconsInt_eval_exists_heap_eq values roots heap observed
  exact ⟨returned, heap, executed, related, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- The ordinary signed reader retains the usual represented-call heap frame. -/
theorem unconsInt_eval_exists (values : List Int)
    (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap)
    (observed : Representation.listInt.Rel values roots heap) :
    ∃ returned finish,
      unconsBoolNat roots heap = Part.some (.ok returned, finish) ∧
      (Representation.int.prod Representation.listInt).option.Rel
        (values.head?.map (fun head => (head, values.tail))) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, executed, related⟩ := unconsInt_eval_exists_heap_eq values roots heap observed
  exact ⟨returned, heap, executed, related, Heap.ShapeExtends.refl heap⟩

/-- The allocating entry's mathematical parameters and actual signed result. -/
def consIntRepresentation :
    FunctionRepresentation (Int × List Int) (fun _ => List Int) signatures[consBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.int
      (ArgumentRepresentation.single Representation.listInt))
    (fun _ => Representation.listInt)

/-- The existing pair constructor refines ordinary signed List.cons. -/
theorem consInt_refines :
    RepresentedFunction.Refines program consBoolNatId consIntRepresentation
      (fun _ => True) (fun input => input.1 :: input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  obtain ⟨returned, finish, executed, related, _⟩ :=
    consInt_eval_exists input.1 input.2 args.head args.tail.head heap observed.1 observed.2
  refine ⟨returned, finish, ?_, related⟩
  rw [consBoolNat_observe]
  exact executed

/-- The reader's signed input and optional ordinary head/tail result. -/
def unconsIntRepresentation :
    FunctionRepresentation (List Int) (fun _ => Option (Int × List Int))
      signatures[unconsBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.single Representation.listInt)
    (fun _ => (Representation.int.prod Representation.listInt).option)

/-- Reading the same actual nodes refines ordinary signed-list decomposition. -/
theorem unconsInt_refines :
    RepresentedFunction.Refines program unconsBoolNatId unconsIntRepresentation
      (fun _ => True) (fun values => values.head?.map (fun head => (head, values.tail))) := by
  intro values _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  obtain ⟨returned, executed, related⟩ :=
    unconsInt_eval_exists_heap_eq values args.head heap observed
  refine ⟨returned, heap, ?_, related⟩
  rw [unconsBoolNat_observe]
  exact executed

end Complexity.Language.List.Prod.Operations
