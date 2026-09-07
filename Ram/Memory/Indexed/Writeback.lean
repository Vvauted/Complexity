/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Memory.Indexed
import Mathlib.Data.Set.Piecewise

/-!
# Reassembling a modified indexed view

After a block modifies a selected part of an indexed object, its whole model
is the ordinary function `changed.piecewise new old`. The new values are
required only on the selected indices; values elsewhere come from the original
representation and a proved endpoint frame. This is mathematical write-back,
not an additional RAM store, allocation, bulk operation, or cost annotation.

`IndexedRep.piecewise` needs no injectivity when unchanged observations outside
the view are supplied directly. `IndexedRep.replace_on` instead consumes a
standard memory frame outside the physical address image. Its injectivity
premise ensures that an index outside the view cannot alias a changed cell.
The `IndexedAt` rules retain the original source-heap bounds.
-/

namespace Ram.IndexedRep

variable {ι : Type*} {before after : Word w → Word w}
  {address : ι → Word w} {old new : ι → Word w}
  {changed : Set ι} [∀ i, Decidable (i ∈ changed)]

/-- Reassemble an updated subview using direct equality of the observations
outside it. Even an aliased layout is allowed when these premises hold. -/
theorem piecewise (h : IndexedRep before address old)
    (updated : Set.EqOn (after ∘ address) new changed)
    (outside : Set.EqOn (after ∘ address) (before ∘ address) changedᶜ) :
    IndexedRep after address (changed.piecewise new old) := by
  intro i
  by_cases hi : i ∈ changed
  · exact (updated hi).trans (Set.piecewise_eq_of_mem changed new old hi).symm
  · exact ((outside hi).trans (h i)).trans
      (Set.piecewise_eq_of_notMem changed new old hi).symm

/-- A whole-block frame outside the physical image reconstructs the parent
model after changing a subview. Injectivity is used only to separate indices
outside the view from addresses that the block may have changed. -/
theorem replace_on (h : IndexedRep before address old)
    (injective : Function.Injective address)
    (updated : Set.EqOn (after ∘ address) new changed)
    (frame : Set.EqOn after before (address '' changed)ᶜ) :
    IndexedRep after address (changed.piecewise new old) := by
  apply h.piecewise updated
  intro i hi
  exact frame (by
    rintro ⟨j, hj, same⟩
    exact hi ((injective same) ▸ hj))

/-- A block may also change auxiliary cells provided they do not overlap
observations outside the selected view. The auxiliary region may overlap
the view itself; no ownership or allocation premise is needed. -/
theorem replace_on_union {auxiliary : Set (Word w)}
    (h : IndexedRep before address old)
    (injective : Function.Injective address)
    (updated : Set.EqOn (after ∘ address) new changed)
    (frame : Set.EqOn after before (address '' changed ∪ auxiliary)ᶜ)
    (hdisjoint : Disjoint (address '' changedᶜ) auxiliary) :
    IndexedRep after address (changed.piecewise new old) := by
  apply h.piecewise updated
  intro i hi
  apply frame
  rintro (⟨j, hj, same⟩ | haux)
  · exact hi ((injective same) ▸ hj)
  · exact Set.disjoint_left.mp hdisjoint ⟨i, hi, rfl⟩ haux

end Ram.IndexedRep

namespace Ram.Source.IndexedAt

variable {ι : Type*} {heapLimit : Nat} {s t : State w}
  {address : ι → Word w} {old new : ι → Word w}
  {changed : Set ι} [∀ i, Decidable (i ∈ changed)]

/-- Reassembling values does not change the address layout or its heap bounds. -/
theorem piecewise (h : IndexedAt heapLimit address old s)
    (updated : Set.EqOn (t.mem ∘ address) new changed)
    (outside : Set.EqOn (t.mem ∘ address) (s.mem ∘ address) changedᶜ) :
    IndexedAt heapLimit address (changed.piecewise new old) t :=
  ⟨h.1.piecewise updated outside, h.2⟩

/-- Recover a whole heap object from a changed subview and the existing
physical endpoint frame; no allocation or full-memory equality is required. -/
theorem replace_on (h : IndexedAt heapLimit address old s)
    (injective : Function.Injective address)
    (updated : Set.EqOn (t.mem ∘ address) new changed)
    (frame : Set.EqOn t.mem s.mem (address '' changed)ᶜ) :
    IndexedAt heapLimit address (changed.piecewise new old) t :=
  ⟨h.1.replace_on injective updated frame, h.2⟩

/-- Reassemble a view even when the block also changes a disjoint scratch
region, retaining the complete indexed object's original heap bounds. -/
theorem replace_on_union {auxiliary : Set (Word w)}
    (h : IndexedAt heapLimit address old s)
    (injective : Function.Injective address)
    (updated : Set.EqOn (t.mem ∘ address) new changed)
    (frame : Set.EqOn t.mem s.mem (address '' changed ∪ auxiliary)ᶜ)
    (hdisjoint : Disjoint (address '' changedᶜ) auxiliary) :
    IndexedAt heapLimit address (changed.piecewise new old) t :=
  ⟨h.1.replace_on_union injective updated frame hdisjoint, h.2⟩

end Ram.Source.IndexedAt
