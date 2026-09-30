/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prod.GetD
import Complexity.Language.Buffer.Prod.Replicate
import Complexity.Language.Representation.Array.Int

/-!
# Integer observations of real column operations

The Boolean/natural pair operations already implement the physical integer
layout. Their existing source bodies and cost certificates are unchanged.
These contracts observe the very same calls using `Int` and `Array Int`,
including negative defaults, empty arrays and actual final-heap contents.
No executable map or host decoder is inserted. Signed syntax and arithmetic
integration are separate from these representation contracts.
-/

namespace Complexity.Language.Buffer.Prod

namespace GetD

/-- The existing column reader returns the canonical integer constructor pair. -/
theorem getInt_eval (values : Array Int) (index : Nat) (fallback : Int)
    (columns : Buffer .bool × Buffer .nat) (heap : Heap)
    (observed : Representation.arrayInt.Rel values columns heap) :
    getBoolNat columns index (Representation.intEquiv fallback) heap =
      Part.some (.ok (Representation.intEquiv (values.getD index fallback)), heap) := by
  simpa only [Array.getD_map] using
    getBoolNat_eval (values.map Representation.intEquiv) index
      (Representation.intEquiv fallback) columns heap observed

/-- Both the default and result use the same canonical signed observation. -/
def intRepresentation :
    FunctionRepresentation (Array Int × Nat × Int) (fun _ => Int)
      signatures[getBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.arrayInt
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single Representation.int)))
    (fun _ => Representation.int)

/-- Integer lookup is ordinary Lean `Array.getD` on every index and default. -/
theorem getInt_refines :
    RepresentedFunction.Refines program getBoolNatId intRepresentation (fun _ => True)
      (fun input => input.1.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  refine ⟨Representation.intEquiv (input.1.getD input.2.1 input.2.2), heap, ?_, rfl⟩
  rw [getBoolNat_observe]
  change input.2.1 = args.tail.head at index
  change Representation.intEquiv input.2.2 = args.tail.tail.head at fallback
  rw [← index, ← fallback]
  exact getInt_eval input.1 input.2.1 input.2.2 args.head heap contents

/-- Reading preserves all contents, including aliases of either integer column. -/
theorem getInt_eval_exists_preserving (values : Array Int) (index : Nat)
    (fallback : Int) (columns : Buffer .bool × Buffer .nat)
    (default : Bool × Nat) (heap : Heap)
    (observed : Representation.arrayInt.Rel values columns heap)
    (defaultObserved : Representation.int.Rel fallback default heap) :
    ∃ returned finish, getBoolNat columns index default heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (values.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  change Representation.intEquiv fallback = default at defaultObserved
  rw [← defaultObserved]
  exact ⟨_, heap, getInt_eval values index fallback columns heap observed, rfl,
    Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

end GetD

namespace Replicate

/-- The two actual allocations observe integer replication and preserve old contents. -/
theorem replicateInt_eval_exists_preserving (length : Nat) (initial : Int)
    (value : Bool × Nat) (heap : Heap)
    (initialObserved : Representation.int.Rel initial value heap) :
    ∃ returned finish,
      replicateBoolNat length value heap = Part.some (.ok returned, finish) ∧
      Representation.arrayInt.Rel (Array.replicate length initial) returned finish ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  change Representation.intEquiv initial = value at initialObserved
  rw [← initialObserved]
  obtain ⟨returned, finish, execution, related, shape, preserved⟩ :=
    replicateBoolNat_eval_exists_preserving length (Representation.intEquiv initial) heap
  refine ⟨returned, finish, execution, ?_, shape, preserved⟩
  simpa only [Representation.arrayInt_rel, Array.map_replicate] using related

/-- A signed initializer and actual final-heap integer-array observation. -/
def intRepresentation :
    FunctionRepresentation (Nat × Int) (fun _ => Array Int)
      signatures[replicateBoolNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single Representation.int))
    (fun _ => Representation.arrayInt)

/-- Integer replication reuses the existing initialized pair allocator itself. -/
theorem replicateInt_refines :
    RepresentedFunction.Refines program replicateBoolNatId intRepresentation (fun _ => True)
      (fun input => Array.replicate input.1 input.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  obtain ⟨returned, finish, execution, related, _, _⟩ :=
    replicateInt_eval_exists_preserving input.1 input.2 args.tail.head heap initial
  refine ⟨returned, finish, ?_, related⟩
  rw [replicateBoolNat_observe, ← length]
  exact execution

end Replicate

end Complexity.Language.Buffer.Prod
