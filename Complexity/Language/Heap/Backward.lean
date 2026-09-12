/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Restriction
import Mathlib.Logic.Relation

/-!
# Backward object links and retained heap prefixes

The supplied reference projection describes dependencies of actual objects in
`Heap.objects`. If every dependency points to an earlier object, retaining a
root's object prefix also retains every object transitively reachable from it.
The preservation statements use the existing `Heap.alloc`, `Heap.write` and
`Heap.take`; they introduce neither a second heap nor another execution model.

The concrete `nodeReferences` projection follows only explicit immutable-node
tails, never scalar buffer cells. Backward links guarantee object-domain closure,
not the target's node tag or scalar type; linked contents contracts retain those
separate facts. Neither projection changes the current scope-safety check or
identifies source object numbers with machine addresses.
-/

namespace Complexity.Language.Heap

/-- One projected reference from an object actually stored in the given heap. -/
def References (references : HeapObject → List Nat) (heap : Heap)
    (source target : Nat) : Prop :=
  ∃ object, heap.objects[source]? = some object ∧ target ∈ references object

/-- Every projected object reference points strictly into the earlier domain.
Several objects may refer to the same earlier object. -/
def BackwardLinks (references : HeapObject → List Nat) (heap : Heap) : Prop :=
  ∀ ⦃source target⦄, References references heap source target → target < source

/-- Reachability follows the actual stored-object reference relation. The root
itself is reachable; its existence is a separate object-domain premise. -/
abbrev Reachable (references : HeapObject → List Nat) (heap : Heap) :=
  Relation.ReflTransGen (References references heap)

/-- Only an explicit immutable-node tail denotes an object reference.
Scalar buffer contents are not reinterpreted as pointers. -/
def nodeReferences : HeapObject → List Nat
  | .buffer _ _ => []
  | .node _ _ none => []
  | .node _ _ (some tail) => [tail.object]

/-- A successfully looked-up node contributes its actual stored tail edge. -/
theorem references_node {heap : Heap} {τ : CellTy} {source : Nat}
    {head : CellValue τ} {tail : NodeRef τ}
    (found : heap.node? τ source = some (head, some tail)) :
    References nodeReferences heap source tail.object :=
  ⟨.node τ head (some tail), node?_eq_some_iff.mp found, by simp [nodeReferences]⟩

/-- The concrete invariant orders an actual tail strictly before its node. -/
theorem BackwardLinks.node_tail_lt {heap : Heap}
    (backward : BackwardLinks nodeReferences heap) {τ : CellTy} {source : Nat}
    {head : CellValue τ} {tail : NodeRef τ}
    (found : heap.node? τ source = some (head, some tail)) : tail.object < source :=
  backward (references_node found)

/-- Actual backward tails are in the heap domain. This does not by itself
assert that their target has the expected node tag and scalar type. -/
theorem BackwardLinks.node_tail_lt_size {heap : Heap}
    (backward : BackwardLinks nodeReferences heap) {τ : CellTy} {source : Nat}
    {head : CellValue τ} {tail : NodeRef τ}
    (found : heap.node? τ source = some (head, some tail)) :
    tail.object < heap.objects.size :=
  Nat.lt_trans (backward.node_tail_lt found) (node_lt_size found)

variable {references : HeapObject → List Nat} {heap finish : Heap}
variable {root source target count : Nat}

/-- Following backward links can never move beyond the original root. -/
theorem BackwardLinks.reachable_le (backward : BackwardLinks references heap)
    (reachable : Reachable references heap root target) : target ≤ root := by
  induction reachable with
  | refl => exact Nat.le_refl _
  | tail previous edge ih => exact Nat.le_trans (Nat.le_of_lt (backward edge)) ih

/-- Every object reachable from an existing root is itself in the heap domain. -/
theorem BackwardLinks.reachable_lt_size (backward : BackwardLinks references heap)
    (rooted : root < heap.objects.size)
    (reachable : Reachable references heap root target) : target < heap.objects.size :=
  Nat.lt_of_le_of_lt (backward.reachable_le reachable) rooted

/-- At a retained source identifier, restriction keeps exactly the same links. -/
theorem references_take_iff (retained : source < count) :
    References references (heap.take count) source target ↔
      References references heap source target := by
  unfold References
  rw [heap.getElem?_take_of_lt count retained]

/-- Any reference found in a restricted heap also belongs to the original heap. -/
theorem References.of_take (edge : References references (heap.take count) source target) :
    References references heap source target := by
  obtain ⟨object, found, member⟩ := edge
  have present : source < (heap.take count).objects.size :=
    (Array.getElem?_eq_some_iff.mp found).choose
  have retained : source < count := by
    rw [take_size] at present
    exact Nat.lt_of_lt_of_le present (Nat.min_le_left _ _)
  exact (references_take_iff retained).mp ⟨object, found, member⟩

/-- Discarding an object suffix preserves the backward-link invariant. -/
theorem BackwardLinks.take (backward : BackwardLinks references heap) (count : Nat) :
    BackwardLinks references (heap.take count) := by
  intro source target edge
  exact backward edge.of_take

/-- Restriction cannot create a new path. This direction needs no backward-link
assumption because it only forgets a restriction of the same current heap. -/
theorem Reachable.of_take (reachable : Reachable references (heap.take count) root target) :
    Reachable references heap root target := by
  induction reachable with
  | refl => exact .refl
  | tail previous edge ih => exact .tail ih edge.of_take

/-- A retained root keeps its entire path of backward links in the same final
heap, without consulting a previous snapshot or scanning a mutable graph. -/
theorem BackwardLinks.reachable_take (backward : BackwardLinks references heap)
    (retained : root < count) (reachable : Reachable references heap root target) :
    Reachable references (heap.take count) root target := by
  induction reachable with
  | refl => exact .refl
  | tail previous edge ih =>
    have sourceRetained := Nat.lt_of_le_of_lt (backward.reachable_le previous) retained
    exact .tail ih ((references_take_iff sourceRetained).mpr edge)

/-- Prefix reclamation preserves exactly the reachable objects of a retained
root when all stored links point backwards. -/
theorem BackwardLinks.reachable_take_iff (backward : BackwardLinks references heap)
    (retained : root < count) :
    Reachable references (heap.take count) root target ↔
      Reachable references heap root target :=
  ⟨Reachable.of_take, backward.reachable_take retained⟩

/-- Every transitively reachable object retains its exact current contents,
not merely its identifier, when a containing prefix is kept. -/
theorem BackwardLinks.getElem?_take_of_reachable
    (backward : BackwardLinks references heap) (retained : root < count)
    (reachable : Reachable references heap root target) :
    (heap.take count).objects[target]? = heap.objects[target]? :=
  heap.getElem?_take_of_lt count
    (Nat.lt_of_le_of_lt (backward.reachable_le reachable) retained)

/-- Appending one actual object preserves backward links when all its references
belong to the old object domain. Several new objects may share an old target. -/
theorem BackwardLinks.push (backward : BackwardLinks references heap) (newObject : HeapObject)
    (older : ∀ target ∈ references newObject,
      target < heap.objects.size) :
    BackwardLinks references ⟨heap.objects.push newObject⟩ := by
  rintro source target ⟨object, found, member⟩
  by_cases fresh : source = heap.objects.size
  · subst source
    have same : object = newObject := by
      apply Option.some.inj
      exact found.symm.trans Array.getElem?_push_size
    subst object
    exact older target member
  · apply backward
    refine ⟨object, ?_, member⟩
    simpa only [Array.getElem?_push, if_neg fresh] using found

/-- The actual allocator preserves backward links when every reference in its
new initialized object belongs to the previous object domain. Initialization
and scalar values alone do not establish this premise automatically. -/
theorem BackwardLinks.alloc (backward : BackwardLinks references heap)
    {kind : CellTy} (length : Nat) (initial : CellValue kind)
    (older : ∀ target ∈ references (.buffer kind (Array.replicate length initial)),
      target < heap.objects.size) :
    BackwardLinks references (heap.alloc length initial).2 :=
  backward.push (.buffer kind (Array.replicate length initial)) older

/-- An actual successful scalar write preserves backward links if it leaves the
written object's reference projection unchanged. Arbitrary writes to encoded
links do not satisfy this premise; immutable node tags must enforce that boundary. -/
theorem BackwardLinks.write (backward : BackwardLinks references heap)
    {kind : CellTy} {buffer : Buffer kind} {index : Nat} {value : CellValue kind}
    (written : heap.write buffer index value = .ok finish)
    (unchanged : ∀ values, heap.object? kind buffer.object = some values →
      references (.buffer kind (values.setIfInBounds (buffer.offset + index) value)) =
        references (.buffer kind values)) :
    BackwardLinks references finish := by
  obtain ⟨values, found, extent, bound, rfl⟩ := write_eq_ok_iff.mp written
  rintro source target ⟨object, stored, member⟩
  by_cases changed : buffer.object = source
  · subst source
    have same : object = .buffer kind (values.setIfInBounds (buffer.offset + index) value) := by
      apply Option.some.inj
      exact stored.symm.trans
        (object?_eq_some_iff.mp (object?_replace_self (object_lt_size found)))
    subst object
    apply backward
    refine ⟨.buffer kind values, object?_eq_some_iff.mp found, ?_⟩
    rw [← unchanged values found]
    exact member
  · apply backward
    refine ⟨object, ?_, member⟩
    simpa only [replace, Array.getElem?_setIfInBounds_ne changed] using stored

end Complexity.Language.Heap
