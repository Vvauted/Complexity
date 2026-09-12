/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Language.RepresentedFunction
import Init.Data.Vector.Lemmas

/-!
# Native collection contracts for the same copying implementation

The checked `Copy.copy` and `Copy.append` source functions implement the ordinary
array, list and vector operations below. The representation contracts retain
fresh output storage and every old contents observation at the actual return
heap. No loop, allocation or source-to-RAM argument is repeated here.

These are three mathematical views of the existing contiguous natural-number
buffer runtime. They do not introduce linked-list storage, polymorphic runtime
cells, free input conversion or permanent immutability of returned handles.
`RepresentedFunction.Refines.of_math` lets callers attach ordinary mathematical
results, as illustrated by the reusable list-length contract at the end.
-/

namespace Complexity.Language.Buffer

universe u v w

/-- Observe a fresh returned natural buffer while retaining every old view.
The mathematical result is still an observation in the actual final heap. -/
def freshResultRepresentation {α : Type u} {β : α → Type v} {Γ : List Ty}
    (input : ArgumentRepresentation α Γ)
    (result : (x : α) → Representation (β x) (.buffer .nat)) :
    FunctionRepresentation α β ⟨Γ, .buffer .nat⟩ where
  input := input
  post x _ initial value finish output :=
    (result x).Rel output value finish ∧ value.object = initial.objects.size ∧
      PreservesContents initial finish
  post_functional first second := (result _).functional first.1 second.1

/-- One collection argument and a fresh copy in the same mathematical view. -/
def copyRepresentation {α : Type u} (value : Representation α (.buffer .nat)) :
    FunctionRepresentation α (fun _ => α) Copy.signatures[Copy.copyId] :=
  freshResultRepresentation (ArgumentRepresentation.single value) (fun _ => value)

/-- Two collection arguments and a fresh appended result. The argument
representations share the initial heap and impose no disjointness between inputs. -/
def appendRepresentation {α : Type u} {β : Type v} {γ : Type w}
    (left : Representation α (.buffer .nat)) (right : Representation β (.buffer .nat))
    (result : Representation γ (.buffer .nat)) :
    FunctionRepresentation (α × β) (fun _ => γ) Copy.signatures[Copy.appendId] :=
  freshResultRepresentation
    (ArgumentRepresentation.cons left (ArgumentRepresentation.single right)) (fun _ => result)

/-- Reuse the source copying theorem for any faithful native-array observation.
This transports a proved implementation contract, not just an extensional equation. -/
theorem copy_refines {α : Type u} (representation : Representation α (.buffer .nat))
    (view : α → Array Nat)
    (observes : ∀ value buffer heap,
      representation.Rel value buffer heap ↔ buffer.Contents heap (view value)) :
    RepresentedFunction.Refines Copy.program Copy.copyId (copyRepresentation representation)
      (fun _ => True) id := by
  intro input _
  apply (copy_total (view input)).consequence
  · intro args heap represented
    exact (observes input args.head heap).mp represented
  · intro args initial value finish _ copiedValue
    exact ⟨(observes input value finish).mpr copiedValue.1, copiedValue.2⟩

/-- Ordinary append mathematics transports the already proved two-copy source
contract. Neither source loop nor input-separation reasoning is repeated. -/
theorem append_refines {α : Type u} {β : Type v} {γ : Type w}
    (left : Representation α (.buffer .nat)) (right : Representation β (.buffer .nat))
    (result : Representation γ (.buffer .nat)) (leftView : α → Array Nat)
    (rightView : β → Array Nat) (operation : α → β → γ)
    (leftObserves : ∀ value buffer heap,
      left.Rel value buffer heap ↔ buffer.Contents heap (leftView value))
    (rightObserves : ∀ value buffer heap,
      right.Rel value buffer heap ↔ buffer.Contents heap (rightView value))
    (resultObserves : ∀ first second buffer heap,
      result.Rel (operation first second) buffer heap ↔
        buffer.Contents heap (leftView first ++ rightView second)) :
    RepresentedFunction.Refines Copy.program Copy.appendId
      (appendRepresentation left right result) (fun _ => True)
      (fun input => operation input.1 input.2) := by
  intro input _
  apply (append_total (leftView input.1) (rightView input.2)).consequence
  · intro args heap represented
    exact ⟨(leftObserves input.1 args.head heap).mp represented.1,
      (rightObserves input.2 args.tail.head heap).mp represented.2⟩
  · intro args initial value finish _ appended
    exact ⟨(resultObserves input.1 input.2 value finish).mpr appended.1, appended.2⟩

/-- Native array copying is the identity on contents, with real fresh allocation. -/
theorem copy_array_refines :
    RepresentedFunction.Refines Copy.program Copy.copyId
      (copyRepresentation (Representation.array .nat)) (fun _ => True) id :=
  copy_refines (Representation.array .nat) id (fun _ _ _ => Iff.rfl)

/-- Native lists reuse the same copying program through their array observation. -/
theorem copy_list_refines :
    RepresentedFunction.Refines Copy.program Copy.copyId
      (copyRepresentation (Representation.bufferList .nat)) (fun _ => True) id :=
  copy_refines (Representation.bufferList .nat) List.toArray (fun _ _ _ => Iff.rfl)

/-- Copying a native vector preserves its mathematical length index. -/
theorem copy_vector_refines (length : Nat) :
    RepresentedFunction.Refines Copy.program Copy.copyId
      (copyRepresentation (Representation.vector .nat length)) (fun _ => True) id :=
  copy_refines (Representation.vector .nat length) Vector.toArray (fun _ _ _ => Iff.rfl)

/-- Native array append is implemented by the same fresh allocating source function. -/
theorem append_array_refines :
    RepresentedFunction.Refines Copy.program Copy.appendId
      (appendRepresentation (Representation.array .nat) (Representation.array .nat)
        (Representation.array .nat)) (fun _ => True) (fun input => input.1 ++ input.2) :=
  append_refines (Representation.array .nat) (Representation.array .nat)
    (Representation.array .nat) id id (fun left right => left ++ right)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

/-- Native list append has a contiguous buffer implementation, not a new linked-list runtime. -/
theorem append_list_refines :
    RepresentedFunction.Refines Copy.program Copy.appendId
      (appendRepresentation (Representation.bufferList .nat) (Representation.bufferList .nat)
        (Representation.bufferList .nat)) (fun _ => True) (fun input => input.1 ++ input.2) := by
  apply append_refines (Representation.bufferList .nat) (Representation.bufferList .nat)
    (Representation.bufferList .nat) List.toArray List.toArray (fun left right => left ++ right)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
  intro left right buffer heap
  change buffer.Contents heap (left ++ right).toArray ↔
    buffer.Contents heap (left.toArray ++ right.toArray)
  rw [List.append_toArray]

/-- Native vector append retains its dependent output length in the mathematical
contract while reusing the same natural-buffer source function. -/
theorem append_vector_refines (leftLength rightLength : Nat) :
    RepresentedFunction.Refines Copy.program Copy.appendId
      (appendRepresentation (Representation.vector .nat leftLength)
        (Representation.vector .nat rightLength)
        (Representation.vector .nat (leftLength + rightLength)))
      (fun _ => True) (fun input => input.1 ++ input.2) := by
  exact append_refines (Representation.vector .nat leftLength)
    (Representation.vector .nat rightLength)
    (Representation.vector .nat (leftLength + rightLength))
    Vector.toArray Vector.toArray (fun left right => left ++ right)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

/-- A caller proves only the ordinary list length theorem; shared refinement
retains execution, fresh result storage and the initial-heap contents frame. -/
theorem append_list_length :
    RepresentedFunction.Total Copy.program Copy.appendId
      (appendRepresentation (Representation.bufferList .nat) (Representation.bufferList .nat)
        (Representation.bufferList .nat)) (fun _ => True)
      (fun input result => result.length = input.1.length + input.2.length) := by
  apply append_list_refines.of_math
  intro input _
  exact List.length_append

end Complexity.Language.Buffer
