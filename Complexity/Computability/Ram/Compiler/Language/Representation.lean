/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Encoding
import Complexity.Language.Representation

/-!
# Word ranges from mathematical observations

`RepresentationFits` transfers mathematical range information to every actual
value related at its current heap. Pure embeddings, array observations, products
and mathematical views compose without choosing a canonical runtime handle.

These certificates assert only `ValueFits`. Array element ranges, rooting,
physical addresses and allocation capacity remain separate obligations. A
certificate does not establish that any representation exists; the client
supplies an actual observation when applying it.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u v

/-- Every actual representation of this mathematical value has word-sized fields. -/
def RepresentationFits {α : Type u} {τ : Ty}
    (representation : Representation α τ) (w : Nat) (model : α) : Prop :=
  ∀ {actual heap}, representation.Rel model actual heap → ValueFits w actual

namespace RepresentationFits

variable {α : Type u} {β : Type v} {τ σ : Ty} {w : Nat}

/-- Apply a mathematical range certificate to the actual value and current heap. -/
theorem valueFits {representation : Representation α τ} {model : α}
    {actual : Value τ} {heap : Heap}
    (fits : RepresentationFits representation w model)
    (observed : representation.Rel model actual heap) : ValueFits w actual :=
  fits observed

/-- A pure encoding reuses the range of its encoded mathematical value. -/
theorem ofEmbedding (encoding : α ↪ Value τ) {model : α}
    (fits : ValueFits w (encoding model)) :
    RepresentationFits (Representation.ofEmbedding encoding) w model := by
  intro actual heap observed
  change encoding model = actual at observed
  exact observed ▸ fits

/-- An observed array's descriptor fits when its mathematical length does.
This does not assert element ranges, rooting, address bounds or free capacity. -/
theorem array (kind : CellTy) {values : Array (CellValue kind)}
    (sizeFits : values.size < 2 ^ w) :
    RepresentationFits (Representation.array kind) w values := by
  intro actual heap observed
  change actual.length < 2 ^ w
  rw [← observed.size_eq]
  exact sizeFits

/-- Both fields use their supplied range certificates at the same actual heap.
The observed fields may share storage. -/
theorem prod {left : Representation α τ} {right : Representation β σ}
    {first : α} {second : β}
    (leftFits : RepresentationFits left w first)
    (rightFits : RepresentationFits right w second) :
    RepresentationFits (left.prod right) w (first, second) := by
  intro actual heap observed
  exact ⟨leftFits observed.1, rightFits observed.2⟩

/-- A mathematical view changes neither the observed runtime value nor its heap. -/
theorem comap {representation : Representation α τ} (view : β ↪ α) {model : β}
    (fits : RepresentationFits representation w (view model)) :
    RepresentationFits (representation.comap view) w model := by
  intro actual heap observed
  exact fits observed

end RepresentationFits

end Ram.LanguageCompiler
