/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.String
import Complexity.Language.Buffer.GetD
import Complexity.Language.Buffer.Replicate

/-!
# String contracts for existing buffer programs

Character-indexed `value.toList.getD index fallback` compiles as one bounds
check and an actual code-point read. The intermediate mathematical list is
not materialized. This fusion does not implement a standalone `String.toList`
conversion, nor does it confuse a character index with a UTF-8 byte position.

`String.ofList (List.replicate length initial)` uses the existing initialized
buffer allocator, including an actual fresh object at length zero. All source
calls keep their existing implementation and RAM costs; these theorems merely
prove their ordinary String observations and the actual final-heap frames.
-/

namespace Complexity.Language.String

/-- The actual code-point lookup implements the complete defaulted character expression. -/
theorem getD_eval (value : String) (index : Nat) (fallback : Char)
    (source : Buffer .nat) (defaultValue : Nat) (heap : Heap)
    (observed : Representation.string.Rel value source heap)
    (defaultObserved : Representation.char.Rel fallback defaultValue heap) :
    Buffer.GetD.getNat source index defaultValue heap =
      Part.some (.ok (value.toList.getD index fallback).toNat, heap) := by
  change fallback.toNat = defaultValue at defaultObserved
  rw [← defaultObserved]
  simpa only [Representation.stringEmbedding_getD] using
    Buffer.GetD.getNat_eval (Representation.stringEmbedding value) index fallback.toNat
      source heap observed

/-- Character lookup preserves every old contents observation, including aliases. -/
theorem getD_eval_exists_preserving (value : String) (index : Nat) (fallback : Char)
    (source : Buffer .nat) (defaultValue : Nat) (heap : Heap)
    (observed : Representation.string.Rel value source heap)
    (defaultObserved : Representation.char.Rel fallback defaultValue heap) :
    ∃ returned finish,
      Buffer.GetD.getNat source index defaultValue heap = Part.some (.ok returned, finish) ∧
      Representation.char.Rel (value.toList.getD index fallback) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  exact ⟨_, heap, getD_eval value index fallback source defaultValue heap observed defaultObserved,
    rfl, Heap.ShapeExtends.refl heap, fun {_} _ _ contents => contents⟩

/-- The standard represented-call frame for the same actual lookup. -/
theorem getD_eval_exists (value : String) (index : Nat) (fallback : Char)
    (source : Buffer .nat) (defaultValue : Nat) (heap : Heap)
    (observed : Representation.string.Rel value source heap)
    (defaultObserved : Representation.char.Rel fallback defaultValue heap) :
    ∃ returned finish,
      Buffer.GetD.getNat source index defaultValue heap = Part.some (.ok returned, finish) ∧
      Representation.char.Rel (value.toList.getD index fallback) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    getD_eval_exists_preserving value index fallback source defaultValue heap observed defaultObserved
  exact ⟨returned, finish, execution, related, shape⟩

/-- Observe a string, character position and fallback through their fixed source fields. -/
def getDRepresentation : FunctionRepresentation (String × Nat × Char) (fun _ => Char)
    Buffer.GetD.signatures[Buffer.GetD.getNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.string
      (ArgumentRepresentation.cons Representation.nat
        (ArgumentRepresentation.single Representation.char)))
    (fun _ => Representation.char)

/-- The original buffer program refines the ordinary Lean character expression. -/
theorem getD_refines : RepresentedFunction.Refines Buffer.GetD.program Buffer.GetD.getNatId
    getDRepresentation (fun _ => True) (fun input => input.1.toList.getD input.2.1 input.2.2) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨contents, index, fallback⟩
  change input.2.1 = args.tail.head at index
  refine ⟨_, heap, ?_, rfl⟩
  rw [Buffer.GetD.getNat_observe, ← index]
  exact getD_eval input.1 input.2.1 input.2.2 args.head args.tail.tail.head heap contents fallback

/-- Repeated-character construction retains fresh storage and all prior contents. -/
theorem replicate_eval_exists_preserving (length : Nat) (initial : Char)
    (initialValue : Nat) (heap : Heap)
    (observed : Representation.char.Rel initial initialValue heap) :
    ∃ returned finish,
      Buffer.Replicate.replicateNat length initialValue heap = Part.some (.ok returned, finish) ∧
      Representation.string.Rel (String.ofList (List.replicate length initial)) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  change initial.toNat = initialValue at observed
  obtain ⟨returned, finish, execution, related, shape, contents⟩ :=
    Buffer.Replicate.replicateNat_eval_exists_preserving length initialValue heap
  refine ⟨returned, finish, execution, ?_, shape, contents⟩
  change returned.Contents finish (Representation.stringEmbedding _)
  simpa only [Representation.stringEmbedding_replicate, observed] using related

/-- The standard represented-call frame for actual repeated-character allocation. -/
theorem replicate_eval_exists (length : Nat) (initial : Char)
    (initialValue : Nat) (heap : Heap)
    (observed : Representation.char.Rel initial initialValue heap) :
    ∃ returned finish,
      Buffer.Replicate.replicateNat length initialValue heap = Part.some (.ok returned, finish) ∧
      Representation.string.Rel (String.ofList (List.replicate length initial)) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, execution, related, shape, _⟩ :=
    replicate_eval_exists_preserving length initial initialValue heap observed
  exact ⟨returned, finish, execution, related, shape⟩

/-- Natural length and a character initializer with the actual final string observation. -/
def replicateRepresentation : FunctionRepresentation (Nat × Char) (fun _ => String)
    Buffer.Replicate.signatures[Buffer.Replicate.replicateNatId] :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons Representation.nat
      (ArgumentRepresentation.single Representation.char))
    (fun _ => Representation.string)

/-- The same allocator refines the ordinary list-to-string construction. -/
theorem replicate_refines :
    RepresentedFunction.Refines Buffer.Replicate.program Buffer.Replicate.replicateNatId
      replicateRepresentation (fun _ => True)
      (fun input => String.ofList (List.replicate input.1 input.2)) := by
  intro input _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  rcases observed with ⟨length, initial⟩
  change input.1 = args.head at length
  obtain ⟨returned, finish, execution, related, _⟩ :=
    replicate_eval_exists input.1 input.2 args.tail.head heap initial
  refine ⟨returned, finish, ?_, related⟩
  rw [Buffer.Replicate.replicateNat_observe, ← length]
  exact execution

end Complexity.Language.String
