/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.RepresentedFunction
import Complexity.Language.Representation.Array
import Complexity.Language.Buffer.Copy
import Complexity.Language.Eval.Simp

/-!
# Defaulted reads from scalar-pair arrays

Each source function checks the first column's length before executing two
actual reads. A product-array observation supplies the equal column lengths.
Out-of-bounds access returns the entire supplied pair without reading either
column. All branches preserve the complete heap, including aliased views.

The returned scalar pair uses the ordinary pure identity representation, as
does the fallback argument. Only the array input has a heap-backed column
representation. Fixed input loading and represented frontend selection are
separate from these source functions and their correctness contracts.
-/

namespace Complexity.Language.Buffer.Prod

source_program% GetD where
  def getNatNat (columns : Buffer Nat × Buffer Nat) (index : Nat)
      (fallback : Nat × Nat) : Nat × Nat := do
    let left := columns.1
    if index < left.length then
      let right := columns.2
      let first ← left.get index
      let second ← right.get index
      return (first, second)
    else
      return fallback

  def getNatBool (columns : Buffer Nat × Buffer Bool) (index : Nat)
      (fallback : Nat × Bool) : Nat × Bool := do
    let left := columns.1
    if index < left.length then
      let right := columns.2
      let first ← left.get index
      let second ← right.get index
      return (first, second)
    else
      return fallback

  def getBoolNat (columns : Buffer Bool × Buffer Nat) (index : Nat)
      (fallback : Bool × Nat) : Bool × Nat := do
    let left := columns.1
    if index < left.length then
      let right := columns.2
      let first ← left.get index
      let second ← right.get index
      return (first, second)
    else
      return fallback

  def getBoolBool (columns : Buffer Bool × Buffer Bool) (index : Nat)
      (fallback : Bool × Bool) : Bool × Bool := do
    let left := columns.1
    if index < left.length then
      let right := columns.2
      let first ← left.get index
      let second ← right.get index
      return (first, second)
    else
      return fallback

namespace GetD

private theorem readM_getD {left right : CellTy}
    (values : Array (CellValue left × CellValue right)) (index : Nat)
    (fallback : CellValue left × CellValue right)
    (columns : Buffer left × Buffer right) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array left)
      (Representation.array right)).Rel values columns heap) :
    (if index < columns.1.length then do
      let first ← columns.1.readM index
      let second ← columns.2.readM index
      pure (first, second)
    else pure fallback) heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  have lengths := Representation.arrayProd_lengths observed
  change columns.1.Contents heap (values.map _root_.Prod.fst) ∧
    columns.2.Contents heap (values.map _root_.Prod.snd) at observed
  by_cases bound : index < values.size
  · have available : index < columns.1.length := by
      simpa only [lengths.1] using bound
    have firstRead : heap.read columns.1 index = .ok values[index].1 :=
      (observed.1.read (by simpa using bound)).trans
        (congrArg Except.ok (Array.getElem_map _root_.Prod.fst (by simpa using bound)))
    have secondRead : heap.read columns.2 index = .ok values[index].2 :=
      (observed.2.read (by simpa using bound)).trans
        (congrArg Except.ok (Array.getElem_map _root_.Prod.snd (by simpa using bound)))
    simp only [if_pos available, Array.getD, dif_pos bound]
    simp [source_eval, firstRead, secondRead]
  · have unavailable : ¬ index < columns.1.length := by
      simpa only [lengths.1] using bound
    simp only [if_neg unavailable, Array.getD, dif_neg bound]
    rfl

/-- The actual two-column lookup returns the ordinary pair or its whole default. -/
theorem getNatNat_eval (values : Array (Nat × Nat)) (index : Nat)
    (fallback : Nat × Nat) (columns : Buffer .nat × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .nat)).Rel values columns heap) :
    getNatNat columns index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getNatNat_eq] using
    readM_getD (left := .nat) (right := .nat) values index fallback columns heap observed

/-- Pair-array input with identity-represented index, fallback and returned pair. -/
def natNatRepresentation :
    FunctionRepresentation (Array (Nat × Nat) × Nat × (Nat × Nat))
      (fun _ => Nat × Nat) signatures[getNatNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons
      (Representation.arrayProd (Representation.array .nat) (Representation.array .nat))
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single
          (Representation.ofEmbedding (τ := .prod .nat .nat)
            (Function.Embedding.refl (Nat × Nat))))))
    (fun _ => (Representation.ofEmbedding (τ := .prod .nat .nat)
        (Function.Embedding.refl (Nat × Nat))))

/-- This source entry refines total Lean array access, with no supplied index bound. -/
theorem getNatNat_refines :
    RepresentedFunction.Refines program getNatNatId natNatRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getNatNat_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getNatNat_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Every previously observed buffer retains its contents, including aliases. -/
theorem getNatNat_eval_exists_preserving (values : Array (Nat × Nat)) (index : Nat)
    (fallback : Nat × Nat) (columns : Buffer .nat × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .nat)).Rel values columns heap) :
    ∃ returned finish, getNatNat columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .nat .nat)
        (Function.Embedding.refl (Nat × Nat))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getNatNat_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame for a pure pair returned by a real read. -/
theorem getNatNat_eval_exists (values : Array (Nat × Nat)) (index : Nat)
    (fallback : Nat × Nat) (columns : Buffer .nat × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .nat)).Rel values columns heap) :
    ∃ returned finish, getNatNat columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .nat .nat)
        (Function.Embedding.refl (Nat × Nat))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getNatNat_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

/-- The actual two-column lookup returns the ordinary pair or its whole default. -/
theorem getNatBool_eval (values : Array (Nat × Bool)) (index : Nat)
    (fallback : Nat × Bool) (columns : Buffer .nat × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .bool)).Rel values columns heap) :
    getNatBool columns index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getNatBool_eq] using
    readM_getD (left := .nat) (right := .bool) values index fallback columns heap observed

/-- Pair-array input with identity-represented index, fallback and returned pair. -/
def natBoolRepresentation :
    FunctionRepresentation (Array (Nat × Bool) × Nat × (Nat × Bool))
      (fun _ => Nat × Bool) signatures[getNatBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons
      (Representation.arrayProd (Representation.array .nat) (Representation.array .bool))
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single
          (Representation.ofEmbedding (τ := .prod .nat .bool)
            (Function.Embedding.refl (Nat × Bool))))))
    (fun _ => (Representation.ofEmbedding (τ := .prod .nat .bool)
        (Function.Embedding.refl (Nat × Bool))))

/-- This source entry refines total Lean array access, with no supplied index bound. -/
theorem getNatBool_refines :
    RepresentedFunction.Refines program getNatBoolId natBoolRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getNatBool_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getNatBool_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Every previously observed buffer retains its contents, including aliases. -/
theorem getNatBool_eval_exists_preserving (values : Array (Nat × Bool)) (index : Nat)
    (fallback : Nat × Bool) (columns : Buffer .nat × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .bool)).Rel values columns heap) :
    ∃ returned finish, getNatBool columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .nat .bool)
        (Function.Embedding.refl (Nat × Bool))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getNatBool_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame for a pure pair returned by a real read. -/
theorem getNatBool_eval_exists (values : Array (Nat × Bool)) (index : Nat)
    (fallback : Nat × Bool) (columns : Buffer .nat × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .nat)
      (Representation.array .bool)).Rel values columns heap) :
    ∃ returned finish, getNatBool columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .nat .bool)
        (Function.Embedding.refl (Nat × Bool))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getNatBool_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

/-- The actual two-column lookup returns the ordinary pair or its whole default. -/
theorem getBoolNat_eval (values : Array (Bool × Nat)) (index : Nat)
    (fallback : Bool × Nat) (columns : Buffer .bool × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .nat)).Rel values columns heap) :
    getBoolNat columns index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getBoolNat_eq] using
    readM_getD (left := .bool) (right := .nat) values index fallback columns heap observed

/-- Pair-array input with identity-represented index, fallback and returned pair. -/
def boolNatRepresentation :
    FunctionRepresentation (Array (Bool × Nat) × Nat × (Bool × Nat))
      (fun _ => Bool × Nat) signatures[getBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons
      (Representation.arrayProd (Representation.array .bool) (Representation.array .nat))
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single
          (Representation.ofEmbedding (τ := .prod .bool .nat)
            (Function.Embedding.refl (Bool × Nat))))))
    (fun _ => (Representation.ofEmbedding (τ := .prod .bool .nat)
        (Function.Embedding.refl (Bool × Nat))))

/-- This source entry refines total Lean array access, with no supplied index bound. -/
theorem getBoolNat_refines :
    RepresentedFunction.Refines program getBoolNatId boolNatRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getBoolNat_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getBoolNat_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Every previously observed buffer retains its contents, including aliases. -/
theorem getBoolNat_eval_exists_preserving (values : Array (Bool × Nat)) (index : Nat)
    (fallback : Bool × Nat) (columns : Buffer .bool × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .nat)).Rel values columns heap) :
    ∃ returned finish, getBoolNat columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .bool .nat)
        (Function.Embedding.refl (Bool × Nat))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getBoolNat_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame for a pure pair returned by a real read. -/
theorem getBoolNat_eval_exists (values : Array (Bool × Nat)) (index : Nat)
    (fallback : Bool × Nat) (columns : Buffer .bool × Buffer .nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .nat)).Rel values columns heap) :
    ∃ returned finish, getBoolNat columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .bool .nat)
        (Function.Embedding.refl (Bool × Nat))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getBoolNat_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

/-- The actual two-column lookup returns the ordinary pair or its whole default. -/
theorem getBoolBool_eval (values : Array (Bool × Bool)) (index : Nat)
    (fallback : Bool × Bool) (columns : Buffer .bool × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .bool)).Rel values columns heap) :
    getBoolBool columns index fallback heap =
      Part.some (.ok (values.getD index fallback), heap) := by
  simpa [getBoolBool_eq] using
    readM_getD (left := .bool) (right := .bool) values index fallback columns heap observed

/-- Pair-array input with identity-represented index, fallback and returned pair. -/
def boolBoolRepresentation :
    FunctionRepresentation (Array (Bool × Bool) × Nat × (Bool × Bool))
      (fun _ => Bool × Bool) signatures[getBoolBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons
      (Representation.arrayProd (Representation.array .bool) (Representation.array .bool))
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single
          (Representation.ofEmbedding (τ := .prod .bool .bool)
            (Function.Embedding.refl (Bool × Bool))))))
    (fun _ => (Representation.ofEmbedding (τ := .prod .bool .bool)
        (Function.Embedding.refl (Bool × Bool))))

/-- This source entry refines total Lean array access, with no supplied index bound. -/
theorem getBoolBool_refines :
    RepresentedFunction.Refines program getBoolBoolId boolBoolRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨input.1.getD input.2.1 input.2.2, heap, ?_, rfl⟩
  rw [getBoolBool_observe]
  change input.2.1 = args.tail.head at index
  change input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getBoolBool_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Every previously observed buffer retains its contents, including aliases. -/
theorem getBoolBool_eval_exists_preserving (values : Array (Bool × Bool)) (index : Nat)
    (fallback : Bool × Bool) (columns : Buffer .bool × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .bool)).Rel values columns heap) :
    ∃ returned finish, getBoolBool columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .bool .bool)
        (Function.Embedding.refl (Bool × Bool))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, heap, getBoolBool_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame for a pure pair returned by a real read. -/
theorem getBoolBool_eval_exists (values : Array (Bool × Bool)) (index : Nat)
    (fallback : Bool × Bool) (columns : Buffer .bool × Buffer .bool) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array .bool)
      (Representation.array .bool)).Rel values columns heap) :
    ∃ returned finish, getBoolBool columns index fallback heap = Part.some (.ok returned, finish) ∧
      (Representation.ofEmbedding (τ := .prod .bool .bool)
        (Function.Embedding.refl (Bool × Bool))).Rel
        (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  exact ⟨_, heap, getBoolBool_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap⟩

end GetD
end Complexity.Language.Buffer.Prod
