/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.RepresentedFunction
import Complexity.Language.Representation.Preservation
import Complexity.Language.Heap.Allocation
import Complexity.Language.Buffer.Copy
import Complexity.Language.Eval.Simp

/-!
# Initialized scalar arrays

Both source functions allocate and initialize a real buffer. The mathematical
result is Array.replicate at the actual extended heap; even length zero creates
a fresh object. Existing contents, including overlapping views, are preserved.
These source contracts supply neither machine capacity nor a runtime budget.
-/

namespace Complexity.Language.Buffer

source_program% Replicate where
  def replicateNat (length : Nat) (initial : Nat) : Buffer Nat := do
    let result ← Buffer.alloc length initial
    return result

  def replicateBool (length : Nat) (initial : Bool) : Buffer Bool := do
    let result ← Buffer.alloc length initial
    return result

namespace Replicate

/-- Natural replication returns exactly the allocator's fresh view and heap. -/
theorem replicateNat_eval (length initial : Nat) (heap : Heap) :
    replicateNat length initial heap =
      Part.some (.ok (heap.alloc (τ := .nat) length initial).1,
        (heap.alloc (τ := .nat) length initial).2) := by
  simp [replicateNat_eq, source_eval]

/-- Boolean replication uses the same actual initialized allocation. -/
theorem replicateBool_eval (length : Nat) (initial : Bool) (heap : Heap) :
    replicateBool length initial heap =
      Part.some (.ok (heap.alloc (τ := .bool) length initial).1,
        (heap.alloc (τ := .bool) length initial).2) := by
  simp [replicateBool_eq, source_eval]

/-- The fresh natural array has the requested contents and preserves every old
contents observation at its actual final heap, without a separation premise. -/
theorem replicateNat_eval_exists_preserving (length initial : Nat) (heap : Heap) :
    ∃ returned finish,
      replicateNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨(heap.alloc (τ := .nat) length initial).1, (heap.alloc (τ := .nat) length initial).2,
    replicateNat_eval length initial heap, heap.alloc_contents (τ := .nat) length initial,
    heap.shapeExtends_alloc (τ := .nat) length initial,
    fun {_} _ _ observed => observed.alloc (τ := .nat) length initial⟩

/-- Boolean replication retains all existing natural and Boolean views. -/
theorem replicateBool_eval_exists_preserving (length : Nat) (initial : Bool) (heap : Heap) :
    ∃ returned finish,
      replicateBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.array .bool).Rel (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  exact ⟨(heap.alloc (τ := .bool) length initial).1, (heap.alloc (τ := .bool) length initial).2,
    replicateBool_eval length initial heap, heap.alloc_contents (τ := .bool) length initial,
    heap.shapeExtends_alloc (τ := .bool) length initial,
    fun {_} _ _ observed => observed.alloc (τ := .bool) length initial⟩

/-- The standard represented-call contract observes the actual fresh natural buffer. -/
theorem replicateNat_eval_exists (length initial : Nat) (heap : Heap) :
    ∃ returned finish,
      replicateNat length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateNat_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- The standard represented-call contract observes the actual fresh Boolean buffer. -/
theorem replicateBool_eval_exists (length : Nat) (initial : Bool) (heap : Heap) :
    ∃ returned finish,
      replicateBool length initial heap = Part.some (.ok returned, finish) ∧
      (Representation.array .bool).Rel (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicateBool_eval_exists_preserving length initial heap
  exact ⟨returned, finish, execution, related, shape⟩

/-- Natural size and initializer with an actual final-heap array result. -/
def natRepresentation :
    FunctionRepresentation (Nat × Nat) (fun _ => Array Nat) signatures[replicateNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single Representation.nat))
    (fun _ => Representation.array .nat)

/-- Natural size and Boolean initializer with the same allocation convention. -/
def boolRepresentation :
    FunctionRepresentation (Nat × Bool) (fun _ => Array Bool) signatures[replicateBoolId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single Representation.bool))
    (fun _ => Representation.array .bool)

/-- Actual initialized natural allocation refines ordinary Array.replicate. -/
theorem replicateNat_refines :
    RepresentedFunction.Refines program replicateNatId natRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateNat_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateNat_observe, ← length, ← initial]
  exact execution

/-- Boolean replication has the same source-to-mathematical-array contract. -/
theorem replicateBool_refines :
    RepresentedFunction.Refines program replicateBoolId boolRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  change input.2 = args.tail.head at initial
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicateBool_eval_exists input.1 input.2 heap
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateBool_observe, ← length, ← initial]
  exact execution

end Replicate
end Complexity.Language.Buffer
