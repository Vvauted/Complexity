/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List

/-!
# Explicit preservation of mathematical observations

`Representation.Preserves` retains an observation of the same runtime value
across a specified pair of heaps. Products and options compose explicit
preservation proofs, including representations whose components share storage.

Pure embeddings need no heap condition. Immutable linked lists reuse the
existing `Heap.ShapeExtends` frame. No such default is supplied for mutable
arrays or for `Representation.withHeap`, which observes the exact current heap.
-/

namespace Complexity.Language.Representation

universe u v

variable {α : Type u} {β : Type v} {τ σ : Ty}

/-- Preserve every existing observation of the same value across these heaps. -/
def Preserves (representation : Representation α τ) (initial finish : Heap) : Prop :=
  ∀ {a value}, representation.Rel a value initial → representation.Rel a value finish

namespace Preserves

/-- A pure embedding does not inspect the heap. -/
theorem ofEmbedding (encoding : α ↪ Value τ) (initial finish : Heap) :
    (Representation.ofEmbedding encoding).Preserves initial finish := by
  intro a value observed
  exact observed

/-- Both fields retain their observations at the same final heap. Their
underlying storage need not be disjoint. -/
theorem prod {left : Representation α τ} {right : Representation β σ}
    {initial finish : Heap} (leftPreserved : left.Preserves initial finish)
    (rightPreserved : right.Preserves initial finish) :
    (left.prod right).Preserves initial finish := by
  intro pair value observed
  exact ⟨leftPreserved observed.1, rightPreserved observed.2⟩

/-- An absent optional payload needs no observation; a present payload uses
the supplied preservation proof. -/
theorem option {payload : Representation α τ} {initial finish : Heap}
    (preserved : payload.Preserves initial finish) :
    payload.option.Preserves initial finish := by
  intro a value observed
  cases a with
  | none =>
      cases value with
      | none => trivial
      | some value => exact False.elim observed
  | some a =>
      cases value with
      | none => exact False.elim observed
      | some value => exact preserved observed

/-- Existing immutable node contents retain every list observation, including
shared tails, under the proved heap-shape extension. -/
theorem list (kind : CellTy) {initial finish : Heap}
    (preserved : initial.ShapeExtends finish) :
    (Representation.list kind).Preserves initial finish := by
  intro values root observed
  exact Representation.list_mono observed preserved

end Preserves

end Complexity.Language.Representation
