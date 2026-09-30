/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Replicate
import Complexity.Language.Representation.Array

/-!
# Initialized scalar-pair arrays

Each source entry calls the existing scalar allocator once per column, in order.
Both columns are real fresh objects, even at length zero. The result observes
Array.replicate of the entire scalar pair at the actual final heap; the first
column and every old contents observation survive the second allocation.

The initializer uses the ordinary pure pair identity representation. These
contracts supply neither machine capacity nor a runtime or readiness bound.
-/

namespace Complexity.Language.Buffer.Prod

source_program% Replicate importing Complexity.Language.Buffer.Replicate where
  def replicateNatNat (length : Nat) (initial : Nat × Nat) :
      Buffer Nat × Buffer Nat := do
    let first ← Complexity.Language.Buffer.Replicate.replicateNat length initial.1
    let second ← Complexity.Language.Buffer.Replicate.replicateNat length initial.2
    return (first, second)

  def replicateNatBool (length : Nat) (initial : Nat × Bool) :
      Buffer Nat × Buffer Bool := do
    let first ← Complexity.Language.Buffer.Replicate.replicateNat length initial.1
    let second ← Complexity.Language.Buffer.Replicate.replicateBool length initial.2
    return (first, second)

  def replicateBoolNat (length : Nat) (initial : Bool × Nat) :
      Buffer Bool × Buffer Nat := do
    let first ← Complexity.Language.Buffer.Replicate.replicateBool length initial.1
    let second ← Complexity.Language.Buffer.Replicate.replicateNat length initial.2
    return (first, second)

  def replicateBoolBool (length : Nat) (initial : Bool × Bool) :
      Buffer Bool × Buffer Bool := do
    let first ← Complexity.Language.Buffer.Replicate.replicateBool length initial.1
    let second ← Complexity.Language.Buffer.Replicate.replicateBool length initial.2
    return (first, second)

namespace Replicate

private theorem allocated_pair {left right : CellTy} (length : Nat)
    (initial : CellValue left × CellValue right) (heap : Heap) :
    let first := heap.alloc (τ := left) length initial.1
    let second := first.2.alloc (τ := right) length initial.2
    (Representation.arrayProd (Representation.array left) (Representation.array right)).Rel
        (Array.replicate length initial) (first.1, second.1) second.2 ∧
      heap.ShapeExtends second.2 ∧ PreservesContents heap second.2 := by
  dsimp only
  refine ⟨?_, (heap.shapeExtends_alloc (τ := left) length initial.1).trans
    ((heap.alloc (τ := left) length initial.1).2.shapeExtends_alloc
      (τ := right) length initial.2), ?_⟩
  · rw [Representation.arrayProd_rel]
    constructor
    · simpa only [Array.map_replicate] using
        (heap.alloc_contents (τ := left) length initial.1).alloc
          (τ := right) length initial.2
    · simpa only [Array.map_replicate] using
        (heap.alloc (τ := left) length initial.1).2.alloc_contents
          (τ := right) length initial.2
  · intro kind view values observed
    exact (observed.alloc (τ := left) length initial.1).alloc
      (τ := right) length initial.2

/-- Both scalar calls return precisely their fresh views and actual final heap. -/
theorem replicateNatNat_eval (length : Nat) (initial : Nat × Nat) (heap : Heap) :
    replicateNatNat length initial heap =
      let first := heap.alloc (τ := .nat) length initial.1
      let second := first.2.alloc (τ := .nat) length initial.2
      Part.some (.ok (first.1, second.1), second.2) := by
  simp [replicateNatNat_eq, source_eval,
    Complexity.Language.Buffer.Replicate.replicateNat_eval]

/-- Replication preserves old contents and observes both columns after allocation. -/
theorem replicateNatNat_eval_exists_preserving (length : Nat)
    (initial : Nat × Nat) (heap : Heap) :
    ∃ returned finish,
      replicateNatNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .nat) (Representation.array .nat)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, _, replicateNatNat_eval length initial heap,
    allocated_pair (left := .nat) (right := .nat) length initial heap⟩

/-- The represented-call contract retains the actual result and extended heap. -/
theorem replicateNatNat_eval_exists (length : Nat) (initial : Nat × Nat) (heap : Heap) :
    ∃ returned finish,
      replicateNatNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .nat) (Representation.array .nat)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateNatNat_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- A pure initializer pair and an actual final-heap pair-array result. -/
def natNatRepresentation :
    FunctionRepresentation (Nat × (Nat × Nat)) (fun _ => Array (Nat × Nat))
      signatures[replicateNatNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single
        (Representation.ofEmbedding (τ := .prod .nat .nat)
          (Function.Embedding.refl (Nat × Nat)))))
    (fun _ => Representation.arrayProd (Representation.array .nat) (Representation.array .nat))

/-- The two real initialized allocations refine ordinary pair-array replication. -/
theorem replicateNatNat_refines :
    RepresentedFunction.Refines program replicateNatNatId natNatRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateNatNat_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateNatNat_observe, ← length, ← initial]
  exact execution

/-- Both scalar calls return precisely their fresh views and actual final heap. -/
theorem replicateNatBool_eval (length : Nat) (initial : Nat × Bool) (heap : Heap) :
    replicateNatBool length initial heap =
      let first := heap.alloc (τ := .nat) length initial.1
      let second := first.2.alloc (τ := .bool) length initial.2
      Part.some (.ok (first.1, second.1), second.2) := by
  simp [replicateNatBool_eq, source_eval,
    Complexity.Language.Buffer.Replicate.replicateNat_eval,
    Complexity.Language.Buffer.Replicate.replicateBool_eval]

/-- Replication preserves old contents and observes both columns after allocation. -/
theorem replicateNatBool_eval_exists_preserving (length : Nat)
    (initial : Nat × Bool) (heap : Heap) :
    ∃ returned finish,
      replicateNatBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .nat) (Representation.array .bool)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, _, replicateNatBool_eval length initial heap,
    allocated_pair (left := .nat) (right := .bool) length initial heap⟩

/-- The represented-call contract retains the actual result and extended heap. -/
theorem replicateNatBool_eval_exists (length : Nat) (initial : Nat × Bool) (heap : Heap) :
    ∃ returned finish,
      replicateNatBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .nat) (Representation.array .bool)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateNatBool_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- A pure initializer pair and an actual final-heap pair-array result. -/
def natBoolRepresentation :
    FunctionRepresentation (Nat × (Nat × Bool)) (fun _ => Array (Nat × Bool))
      signatures[replicateNatBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single
        (Representation.ofEmbedding (τ := .prod .nat .bool)
          (Function.Embedding.refl (Nat × Bool)))))
    (fun _ => Representation.arrayProd (Representation.array .nat) (Representation.array .bool))

/-- The two real initialized allocations refine ordinary pair-array replication. -/
theorem replicateNatBool_refines :
    RepresentedFunction.Refines program replicateNatBoolId natBoolRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateNatBool_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateNatBool_observe, ← length, ← initial]
  exact execution

/-- Both scalar calls return precisely their fresh views and actual final heap. -/
theorem replicateBoolNat_eval (length : Nat) (initial : Bool × Nat) (heap : Heap) :
    replicateBoolNat length initial heap =
      let first := heap.alloc (τ := .bool) length initial.1
      let second := first.2.alloc (τ := .nat) length initial.2
      Part.some (.ok (first.1, second.1), second.2) := by
  simp [replicateBoolNat_eq, source_eval,
    Complexity.Language.Buffer.Replicate.replicateBool_eval,
    Complexity.Language.Buffer.Replicate.replicateNat_eval]

/-- Replication preserves old contents and observes both columns after allocation. -/
theorem replicateBoolNat_eval_exists_preserving (length : Nat)
    (initial : Bool × Nat) (heap : Heap) :
    ∃ returned finish,
      replicateBoolNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .bool) (Representation.array .nat)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, _, replicateBoolNat_eval length initial heap,
    allocated_pair (left := .bool) (right := .nat) length initial heap⟩

/-- The represented-call contract retains the actual result and extended heap. -/
theorem replicateBoolNat_eval_exists (length : Nat) (initial : Bool × Nat) (heap : Heap) :
    ∃ returned finish,
      replicateBoolNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .bool) (Representation.array .nat)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateBoolNat_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- A pure initializer pair and an actual final-heap pair-array result. -/
def boolNatRepresentation :
    FunctionRepresentation (Nat × (Bool × Nat)) (fun _ => Array (Bool × Nat))
      signatures[replicateBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single
        (Representation.ofEmbedding (τ := .prod .bool .nat)
          (Function.Embedding.refl (Bool × Nat)))))
    (fun _ => Representation.arrayProd (Representation.array .bool) (Representation.array .nat))

/-- The two real initialized allocations refine ordinary pair-array replication. -/
theorem replicateBoolNat_refines :
    RepresentedFunction.Refines program replicateBoolNatId boolNatRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateBoolNat_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateBoolNat_observe, ← length, ← initial]
  exact execution

/-- Both scalar calls return precisely their fresh views and actual final heap. -/
theorem replicateBoolBool_eval (length : Nat) (initial : Bool × Bool) (heap : Heap) :
    replicateBoolBool length initial heap =
      let first := heap.alloc (τ := .bool) length initial.1
      let second := first.2.alloc (τ := .bool) length initial.2
      Part.some (.ok (first.1, second.1), second.2) := by
  simp [replicateBoolBool_eq, source_eval,
    Complexity.Language.Buffer.Replicate.replicateBool_eval]

/-- Replication preserves old contents and observes both columns after allocation. -/
theorem replicateBoolBool_eval_exists_preserving (length : Nat)
    (initial : Bool × Bool) (heap : Heap) :
    ∃ returned finish,
      replicateBoolBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .bool) (Representation.array .bool)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨_, _, replicateBoolBool_eval length initial heap,
    allocated_pair (left := .bool) (right := .bool) length initial heap⟩

/-- The represented-call contract retains the actual result and extended heap. -/
theorem replicateBoolBool_eval_exists (length : Nat) (initial : Bool × Bool) (heap : Heap) :
    ∃ returned finish,
      replicateBoolBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.arrayProd (Representation.array .bool) (Representation.array .bool)).Rel
        (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateBoolBool_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- A pure initializer pair and an actual final-heap pair-array result. -/
def boolBoolRepresentation :
    FunctionRepresentation (Nat × (Bool × Bool)) (fun _ => Array (Bool × Bool))
      signatures[replicateBoolBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single
        (Representation.ofEmbedding (τ := .prod .bool .bool)
          (Function.Embedding.refl (Bool × Bool)))))
    (fun _ => Representation.arrayProd (Representation.array .bool) (Representation.array .bool))

/-- The two real initialized allocations refine ordinary pair-array replication. -/
theorem replicateBoolBool_refines :
    RepresentedFunction.Refines program replicateBoolBoolId boolBoolRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateBoolBool_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateBoolBool_observe, ← length, ← initial]
  exact execution

end Replicate
end Complexity.Language.Buffer.Prod
