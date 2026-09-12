/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Heap.Prefix
import Init.Data.Vector.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Mathematical representations of source values

A `Representation α τ` relates ordinary Lean values of type `α` to values of
the existing typed core at the actual current heap. A fixed runtime value and
heap determine at most one mathematical value. The relation need not decode an
invalid handle, and it supplies neither allocation nor an executable operation.

Pure encodings reuse `Function.Embedding`; products, options, sums, subtypes and
native arrays/vectors compose without a second source semantics. The explicit
`bufferList` view has the same contiguous layout, not a linked-list
runtime or a free conversion. Element representations and a compiler-proved
implementation are still required for operations on new data types.

Buffer contents are observations at the stated heap. They remain valid under
proved preservation, not arbitrary future mutation; this module does not turn
a borrowed buffer into an immutable owning value or erase copying costs.
-/

namespace Complexity.Language

universe u v

/-- A mathematical observation of one actual source value and current heap. -/
structure Representation (α : Type u) (τ : Ty) where
  Rel : α → Value τ → Heap → Prop
  functional : ∀ {a b value heap}, Rel a value heap → Rel b value heap → a = b

namespace Representation

variable {α : Type u} {β : Type v} {τ σ : Ty}

/-- An injective pure encoding needs no heap observation. This is a ghost
representation; it does not install the encoding as a runtime operation. -/
def ofEmbedding (encoding : α ↪ Value τ) : Representation α τ where
  Rel a value _ := encoding a = value
  functional left right := encoding.injective (left.trans right.symm)

@[simp] theorem ofEmbedding_rel (encoding : α ↪ Value τ)
    (a : α) (value : Value τ) (heap : Heap) :
    (ofEmbedding encoding).Rel a value heap ↔ encoding a = value := Iff.rfl

/-- Observe the current heap alongside a value without adding runtime fields.
An implementation contract can retain an initial heap in its mathematical state
to derive exact heap preservation from an existing represented-operation rule. -/
def withHeap (representation : Representation α τ) : Representation (α × Heap) τ where
  Rel input value heap := representation.Rel input.1 value heap ∧ heap = input.2
  functional first second :=
    Prod.ext (representation.functional first.1 second.1) (first.2.symm.trans second.2)

@[simp] theorem withHeap_rel (representation : Representation α τ)
    (input : α × Heap) (value : Value τ) (heap : Heap) :
    representation.withHeap.Rel input value heap ↔
      representation.Rel input.1 value heap ∧ heap = input.2 := Iff.rfl

/-- Reuse an existing injective mathematical view without changing the runtime
value, heap layout, or operations that implement it. -/
def comap (representation : Representation α τ) (view : β ↪ α) : Representation β τ where
  Rel b value heap := representation.Rel (view b) value heap
  functional left right := view.injective (representation.functional left right)

@[simp] theorem comap_rel (representation : Representation α τ) (view : β ↪ α)
    (b : β) (value : Value τ) (heap : Heap) :
    (representation.comap view).Rel b value heap ↔ representation.Rel (view b) value heap :=
  Iff.rfl

/-- Native naturals are the mathematical values of the existing natural core type. -/
def nat : Representation Nat .nat := ofEmbedding (Function.Embedding.refl Nat)

/-- Native booleans use the existing boolean core type. -/
def bool : Representation Bool .bool := ofEmbedding (Function.Embedding.refl Bool)

/-- Scalar heap cells reuse their ordinary natural or Boolean observation. -/
def cell : (kind : CellTy) → Representation (CellValue kind) kind.toTy
  | .nat => nat
  | .bool => bool

@[simp] theorem cell_rel (kind : CellTy) (head : CellValue kind)
    (value : Value kind.toTy) (heap : Heap) :
    (cell kind).Rel head value heap ↔ kind.toValue head = value := by
  cases kind <;> rfl

/-- Unit has no additional mathematical payload. -/
def unit : Representation Unit .unit := ofEmbedding (Function.Embedding.refl Unit)

/-- A pair observes both real fields at the same heap; no separation assumption
is imposed, so the components may share underlying storage. -/
def prod (left : Representation α τ) (right : Representation β σ) :
    Representation (α × β) (.prod τ σ) where
  Rel pair value heap := left.Rel pair.1 value.1 heap ∧ right.Rel pair.2 value.2 heap
  functional first second := Prod.ext
    (left.functional first.1 second.1) (right.functional first.2 second.2)

@[simp] theorem prod_rel (left : Representation α τ) (right : Representation β σ)
    (pair : α × β) (value : Value (.prod τ σ)) (heap : Heap) :
    (left.prod right).Rel pair value heap ↔
      left.Rel pair.1 value.1 heap ∧ right.Rel pair.2 value.2 heap := Iff.rfl

/-- Only `some` contains an observed payload. There is no default value or
default buffer in the absent case. -/
def option (payload : Representation α τ) : Representation (Option α) (.option τ) where
  Rel abstract value heap := match abstract, value with
    | none, none => True
    | some a, some value => payload.Rel a value heap
    | _, _ => False
  functional := by
    intro a b value heap first second
    cases a <;> cases b <;> cases value <;> try contradiction
    · rfl
    · exact congrArg some (payload.functional first second)

@[simp] theorem option_none (payload : Representation α τ) (heap : Heap) :
    payload.option.Rel none none heap := trivial

@[simp] theorem option_some (payload : Representation α τ) (a : α)
    (value : Value τ) (heap : Heap) :
    payload.option.Rel (some a) (some value) heap ↔ payload.Rel a value heap := Iff.rfl

/-- A general sum reuses the core's existing option/product layout. Exactly one
payload is present; pairs with both or neither payload do not represent a sum. -/
def sum (left : Representation α τ) (right : Representation β σ) :
    Representation (Sum α β) (.prod (.option τ) (.option σ)) where
  Rel abstract value heap := match abstract, value with
    | .inl a, (some encoded, none) => left.Rel a encoded heap
    | .inr b, (none, some encoded) => right.Rel b encoded heap
    | _, _ => False
  functional := by
    intro a b value heap first second
    rcases value with ⟨firstValue, secondValue⟩
    cases a <;> cases b <;> cases firstValue <;> cases secondValue <;> try contradiction
    · exact congrArg Sum.inl (left.functional first second)
    · exact congrArg Sum.inr (right.functional first second)

@[simp] theorem sum_inl (left : Representation α τ) (right : Representation β σ)
    (a : α) (value : Value τ) (heap : Heap) :
    (left.sum right).Rel (.inl a) (some value, none) heap ↔ left.Rel a value heap := Iff.rfl

@[simp] theorem sum_inr (left : Representation α τ) (right : Representation β σ)
    (b : β) (value : Value σ) (heap : Heap) :
    (left.sum right).Rel (.inr b) (none, some value) heap ↔ right.Rel b value heap := Iff.rfl

/-- Refinement proofs stay in the mathematical type. The actual runtime value
continues to represent the subtype's underlying value. -/
def subtype (representation : Representation α τ) (predicate : α → Prop) :
    Representation {a : α // predicate a} τ :=
  representation.comap ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem subtype_rel (representation : Representation α τ) (predicate : α → Prop)
    (a : {a : α // predicate a}) (value : Value τ) (heap : Heap) :
    (representation.subtype predicate).Rel a value heap ↔
      representation.Rel a.val value heap := Iff.rfl

/-- A scalar buffer is observed through its ordinary native array contents. -/
def array (kind : CellTy) : Representation (Array (CellValue kind)) (.buffer kind) where
  Rel values buffer heap := buffer.Contents heap values
  functional first second := first.unique second

@[simp] theorem array_rel (kind : CellTy) (values : Array (CellValue kind))
    (buffer : Buffer kind) (heap : Heap) :
    (array kind).Rel values buffer heap ↔ buffer.Contents heap values := Iff.rfl

/-- An explicit list-valued view of contiguous storage; this describes a layout, not a runtime
conversion or a claim that list cons can extend a borrowed buffer in place. -/
def bufferList (kind : CellTy) : Representation (List (CellValue kind)) (.buffer kind) :=
  (array kind).comap ⟨List.toArray, by
    intro xs ys same
    simpa using congrArg Array.toList same⟩

/-- Native length-indexed vectors reuse their existing array field. The length
proof is erased from the representation, not from the mathematical contract. -/
def vector (kind : CellTy) (length : Nat) :
    Representation (Vector (CellValue kind) length) (.buffer kind) :=
  (array kind).comap ⟨Vector.toArray, by
    rintro ⟨xs, sizeXs⟩ ⟨ys, sizeYs⟩ same
    cases same
    rfl⟩

/-- Existing exact-prefix preservation suffices to retain an observed array.
This is a proved frame condition, not unconditional persistence. -/
theorem array_mono_prefix {kind : CellTy} {values : Array (CellValue kind)}
    {buffer : Buffer kind} {initial finish : Heap}
    (observed : (array kind).Rel values buffer initial)
    (preserved : List.IsPrefix initial.objects.toList finish.objects.toList) :
    (array kind).Rel values buffer finish := observed.mono_prefix preserved

end Representation

end Complexity.Language
