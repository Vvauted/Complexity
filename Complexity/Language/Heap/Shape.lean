/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap

/-!
# Heap shape extension and rooted handles

Shape extension retains every existing object's identifier, scalar type and
extent, while allowing its contents to change and new objects to appear.
Successful writes are shape extensions even when aliases observe changed cells.

A rooted buffer names an existing object slot. Rootedness does not assert the
stored scalar type or the validity of the view's offset and length. This weaker
condition supports transporting handles without changing invalid-access behavior.
-/

namespace Complexity.Language

namespace Heap

/-- Existing object slots retain their scalar types and extents, but not
necessarily their contents. Additional object slots are permitted. -/
structure ShapeExtends (initial finish : Heap) : Prop where
  /-- Existing object identifiers remain within the heap's domain. -/
  size_le : initial.objects.size ≤ finish.objects.size
  /-- Every existing typed object retains its type and number of cells. -/
  objects : ∀ {τ : CellTy} {object : Nat} {values : Array (CellValue τ)},
    initial.object? τ object = some values →
      ∃ newValues, finish.object? τ object = some newValues ∧ newValues.size = values.size

namespace ShapeExtends

/-- An unchanged heap retains its own shape. -/
theorem refl (heap : Heap) : ShapeExtends heap heap :=
  ⟨Nat.le_refl _, fun found => ⟨_, found, rfl⟩⟩

/-- Successive shape extensions retain every original object's shape. -/
theorem trans {initial middle finish : Heap}
    (first : ShapeExtends initial middle) (second : ShapeExtends middle finish) :
    ShapeExtends initial finish := by
  refine ⟨first.size_le.trans second.size_le, ?_⟩
  intro τ object values found
  obtain ⟨middleValues, middleFound, middleSize⟩ := first.objects found
  obtain ⟨finalValues, finalFound, finalSize⟩ := second.objects middleFound
  exact ⟨finalValues, finalFound, finalSize.trans middleSize⟩

end ShapeExtends

/-- A successful cell update preserves all object identifiers, types and extents. -/
theorem shapeExtends_write {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    ShapeExtends heap finish := by
  obtain ⟨values, found, _, _, rfl⟩ := write_eq_ok_iff.mp written
  refine ⟨?_, ?_⟩
  · simp [replace]
  · intro σ object oldValues oldFound
    by_cases sameObject : buffer.object = object
    · have sameStored : (⟨τ, values⟩ : HeapObject) = ⟨σ, oldValues⟩ := by
        apply Option.some.inj
        exact (object?_eq_some_iff.mp found).symm.trans
          (by simpa only [← sameObject] using object?_eq_some_iff.mp oldFound)
      have sameType : τ = σ := congrArg Sigma.fst sameStored
      subst σ
      have sameValues : oldValues = values := by
        rw [← sameObject, found] at oldFound
        exact (Option.some.inj oldFound).symm
      subst oldValues
      refine ⟨values.setIfInBounds (buffer.offset + index) value, ?_, ?_⟩
      · rw [← sameObject]
        exact object?_replace_self (object_lt_size found)
      · simp only [Array.size_setIfInBounds]
    · exact ⟨oldValues, (object?_replace_ne sameObject).trans oldFound, rfl⟩

end Heap

namespace Buffer

/-- A handle names an existing object slot, without asserting its type or view extent. -/
def Rooted {τ : CellTy} (buffer : Buffer τ) (heap : Heap) : Prop :=
  buffer.object < heap.objects.size

/-- A valid view necessarily names an existing object slot. -/
theorem Valid.rooted {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    (valid : buffer.Valid heap) : buffer.Rooted heap := by
  obtain ⟨values, found, _⟩ := valid
  exact Heap.object_lt_size found

/-- Extending the heap's shape retains rooted handles, including invalid views. -/
theorem Rooted.mono {τ : CellTy} {buffer : Buffer τ} {initial finish : Heap}
    (rooted : buffer.Rooted initial) (extended : Heap.ShapeExtends initial finish) :
    buffer.Rooted finish :=
  Nat.lt_of_lt_of_le rooted extended.size_le

/-- Shape extension preserves valid view extents without preserving their contents. -/
theorem Valid.mono {τ : CellTy} {buffer : Buffer τ} {initial finish : Heap}
    (valid : buffer.Valid initial) (extended : Heap.ShapeExtends initial finish) :
    buffer.Valid finish := by
  obtain ⟨values, found, extent⟩ := valid
  obtain ⟨newValues, newFound, sameSize⟩ := extended.objects found
  exact ⟨newValues, newFound, by simpa only [sameSize] using extent⟩

/-- A successful write retains all rooted handles, without requiring valid views. -/
theorem Rooted.write {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {other : Buffer σ} {index : Nat} {value : CellValue τ}
    (rooted : other.Rooted heap) (written : heap.write buffer index value = .ok finish) :
    other.Rooted finish :=
  rooted.mono (Heap.shapeExtends_write written)

end Buffer

end Complexity.Language
