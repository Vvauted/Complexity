/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Input

/-!
# Compositional preloaded array inputs

An array prefix appends its object after the remaining input's objects and adds
one argument for its whole-buffer view. Existing object identifiers and argument
values are retained exactly, including for empty arrays. The opt-in
`Input.PrefixClosed` property supplies preservation of the remaining input's
mathematical observation under this exact object prefix. Arbitrary registered
inputs need not satisfy that property.

These are fixed input-preparation conventions, not executable source allocation,
copying, or a free loader. Their representation proofs use the existing heap and
buffer relations. Multiple arrays have distinct object identities; this does not
change the aliasing meaning of source operations after invocation.
-/

namespace Complexity.Program.Input

open Language

universe u v

/-- The registered input observation survives exact preservation of every old
heap object. This is an additional property, not a condition on arbitrary inputs. -/
class PrefixClosed (α : Type u) [Input α] : Prop where
  mono : ∀ {x : α} {args : Env (Input.params α)} {initial finish : Heap},
    (Input.representation (α := α)).Rel x args initial →
    List.IsPrefix initial.objects.toList finish.objects.toList →
    (Input.representation (α := α)).Rel x args finish

namespace PrefixClosed

/-- A pure input encoding observes no heap contents. -/
theorem ofEmbedding {α : Type u} {τ : Ty} (encoding : α ↪ Value τ) :
    @PrefixClosed α (Input.ofEmbedding encoding) := by
  refine @PrefixClosed.mk α (Input.ofEmbedding encoding) ?_
  intro x args initial finish observed _
  exact observed

instance nat : PrefixClosed Nat := ofEmbedding (τ := .nat) (Function.Embedding.refl Nat)

instance bool : PrefixClosed Bool := ofEmbedding (τ := .bool) (Function.Embedding.refl Bool)

instance unit : PrefixClosed Unit := ofEmbedding (τ := .unit) (Function.Embedding.refl Unit)

instance arrayNat : PrefixClosed (Array Nat) where
  mono observed extension := Buffer.Contents.mono_prefix observed extension

/-- Adding a heap-independent field preserves prefix closure. -/
theorem consScalar {α : Type u} {β : Type v} {τ : Ty}
    (encoding : α ↪ Value τ) (tail : Input β) [closed : @PrefixClosed β tail] :
    @PrefixClosed (α × β) (Input.consScalar encoding tail) := by
  refine @PrefixClosed.mk (α × β) (Input.consScalar encoding tail) ?_
  intro x args initial finish observed extension
  exact ⟨observed.1,
    @PrefixClosed.mono β tail closed x.2 args.tail initial finish observed.2 extension⟩

instance natProd {β : Type v} [Input β] [PrefixClosed β] : PrefixClosed (Nat × β) :=
  consScalar (τ := .nat) (Function.Embedding.refl Nat) inferInstance

instance boolProd {β : Type v} [Input β] [PrefixClosed β] : PrefixClosed (Bool × β) :=
  consScalar (τ := .bool) (Function.Embedding.refl Bool) inferInstance

instance unitProd {β : Type v} [Input β] [PrefixClosed β] : PrefixClosed (Unit × β) :=
  consScalar (τ := .unit) (Function.Embedding.refl Unit) inferInstance

/-- An injective mathematical presentation retains the existing prefix law.
As with `Input.comap`, this is registration, not an executable transformation. -/
theorem comap {α : Type u} {β : Type v} (input : Input α) (view : β ↪ α)
    [closed : @PrefixClosed α input] : @PrefixClosed β (Input.comap input view) := by
  refine @PrefixClosed.mk β (Input.comap input view) ?_
  intro x args initial finish observed extension
  exact @PrefixClosed.mono α input closed (view x) args initial finish observed extension

end PrefixClosed

/-- Append one preloaded scalar array while leaving all old objects unchanged. -/
def arrayHeap (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) : Heap :=
  ⟨heap.objects.push (.buffer kind xs)⟩

/-- The new argument views the complete appended object, even when empty. -/
def arrayBuffer (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) : Buffer kind :=
  ⟨heap.objects.size, 0, xs.size⟩

@[simp] theorem arrayHeap_objects (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) :
    (arrayHeap kind heap xs).objects = heap.objects.push (.buffer kind xs) := rfl

@[simp] theorem arrayHeap_size (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) :
    (arrayHeap kind heap xs).objects.size = heap.objects.size + 1 := by
  simp only [arrayHeap_objects, Array.size_push]

@[simp] theorem arrayBuffer_object (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) :
    (arrayBuffer kind heap xs).object = heap.objects.size := rfl

@[simp] theorem arrayBuffer_offset (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) : (arrayBuffer kind heap xs).offset = 0 := rfl

@[simp] theorem arrayBuffer_length (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) : (arrayBuffer kind heap xs).length = xs.size := rfl

/-- The exact old object prefix is preserved by preparation of the new input. -/
theorem arrayHeap_prefix (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) :
    List.IsPrefix heap.objects.toList (arrayHeap kind heap xs).objects.toList := by
  simpa only [arrayHeap_objects, Array.toList_push] using
    (List.prefix_append heap.objects.toList [.buffer kind xs])

/-- Preparing the extra array preserves the old object domain, array extents,
and immutable nodes, so existing rooted arguments remain rooted. -/
theorem arrayHeap_shapeExtends (kind : CellTy) (heap : Heap)
    (xs : Array (CellValue kind)) : heap.ShapeExtends (arrayHeap kind heap xs) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [arrayHeap_size]
    exact Nat.le_succ heap.objects.size
  · intro otherKind object values found
    exact ⟨values,
      (Heap.object?_eq_of_prefix (arrayHeap_prefix kind heap xs)
        (Heap.object_lt_size found)).trans found, rfl⟩
  · intro otherKind object head tail found
    exact (Heap.node?_eq_of_prefix (arrayHeap_prefix kind heap xs)
      (Heap.node_lt_size found)).trans found

/-- Typed lookup at the new identity returns the supplied array itself. -/
theorem arrayHeap_object? (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) :
    (arrayHeap kind heap xs).object? kind (arrayBuffer kind heap xs).object = some xs := by
  apply Heap.object?_eq_some_iff.mpr
  exact Array.getElem?_push_size

/-- The new whole-buffer argument represents exactly the supplied array. -/
theorem arrayBuffer_contents (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) :
    (arrayBuffer kind heap xs).Contents (arrayHeap kind heap xs) xs := by
  refine ⟨xs, arrayHeap_object? kind heap xs, ?_, ?_⟩
  · simp only [arrayBuffer_offset, arrayBuffer_length, Nat.zero_add, Nat.le_refl]
  · simpa only [arrayBuffer_offset, arrayBuffer_length, Nat.zero_add] using
      (Array.extract_size (xs := xs)).symm

/-- The freshly prepared input handle names an actual object in the extended heap. -/
theorem arrayBuffer_rooted (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind)) :
    (arrayBuffer kind heap xs).Rooted (arrayHeap kind heap xs) :=
  (arrayBuffer_contents kind heap xs).valid.rooted

/-- Every old rooted view belongs to a different object than the new array. -/
theorem arrayBuffer_disjoint (kind : CellTy) (heap : Heap) (xs : Array (CellValue kind))
    {otherKind : CellTy} {other : Buffer otherKind} (rooted : other.Rooted heap) :
    (arrayBuffer kind heap xs).Disjoint other :=
  Or.inl (Nat.ne_of_gt rooted)

/-- Prepend an array argument and append its object after the remaining input's
objects. Prefix closure preserves the existing mathematical tail observation. -/
def consArray (kind : CellTy) {β : Type v} (tail : Input β)
    [closed : @PrefixClosed β tail] : Input (Array (CellValue kind) × β) where
  params := .buffer kind :: @Input.params β tail
  heap x := arrayHeap kind (@Input.heap β tail x.2) x.1
  args x := Env.cons (arrayBuffer kind (@Input.heap β tail x.2) x.1)
    (@Input.args β tail x.2)
  representation := ArgumentRepresentation.cons
    (Representation.array kind) (@Input.representation β tail)
  represented x := ⟨arrayBuffer_contents kind (@Input.heap β tail x.2) x.1,
    @PrefixClosed.mono β tail closed x.2 (@Input.args β tail x.2)
      (@Input.heap β tail x.2) (arrayHeap kind (@Input.heap β tail x.2) x.1)
      (@Input.represented β tail x.2) (arrayHeap_prefix kind (@Input.heap β tail x.2) x.1)⟩

/-- One initially populated Boolean array, with the same whole-object convention
as natural arrays and no extra trailing unit parameter. -/
instance arrayBool : Input (Array Bool) where
  params := [.buffer .bool]
  heap xs := arrayHeap .bool emptyHeap xs
  args xs := Env.cons (arrayBuffer .bool emptyHeap xs) Env.empty
  representation := ArgumentRepresentation.single (Representation.array .bool)
  represented := arrayBuffer_contents .bool emptyHeap

/-- A natural-array prefix has its own object and keeps the tail's existing views. -/
instance arrayNatProd {β : Type v} [Input β] [PrefixClosed β] : Input (Array Nat × β) :=
  consArray .nat inferInstance

/-- A Boolean-array prefix has its own object and keeps the tail's existing views. -/
instance arrayBoolProd {β : Type v} [Input β] [PrefixClosed β] : Input (Array Bool × β) :=
  consArray .bool inferInstance

namespace PrefixClosed

instance arrayBool : PrefixClosed (Array Bool) where
  mono observed extension := Buffer.Contents.mono_prefix observed extension

/-- Both the appended array observation and the tail survive further exact prefixes. -/
theorem consArray (kind : CellTy) {β : Type v} (tail : Input β)
    [closed : @PrefixClosed β tail] :
    @PrefixClosed (Array (CellValue kind) × β) (Input.consArray kind tail) := by
  refine @PrefixClosed.mk (Array (CellValue kind) × β) (Input.consArray kind tail) ?_
  intro x args initial finish observed extension
  exact ⟨Buffer.Contents.mono_prefix observed.1 extension,
    @PrefixClosed.mono β tail closed x.2 args.tail initial finish observed.2 extension⟩

instance arrayNatProd {β : Type v} [Input β] [PrefixClosed β] :
    PrefixClosed (Array Nat × β) := consArray .nat inferInstance

instance arrayBoolProd {β : Type v} [Input β] [PrefixClosed β] :
    PrefixClosed (Array Bool × β) := consArray .bool inferInstance

end PrefixClosed

end Complexity.Program.Input

namespace Complexity.Program.Output

/-- Observe the returned Boolean buffer through its actual final-heap contents. -/
instance arrayBool : Output (Array Bool) where
  type := .buffer .bool
  representation := Language.Representation.array .bool

end Complexity.Program.Output
