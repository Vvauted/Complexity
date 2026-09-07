/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.TwoBuffer
import Ram.Memory.Frame
import Mathlib.Order.Interval.Set.Defs

/-!
# Array effects as ordinary set-local memory equality

Existing array contracts already return `ArrayFrame` or `TwoBufferFrame`.
These assertions are exactly mathlib's `Set.EqOn` outside a natural-address
interval or the union of two intervals. Exposing that equality lets the same
contracts preserve any disjoint indexed model, not just another list array.
There is no new ownership, allocation or effect datatype here.
-/

namespace Ram

namespace ArrayFrame

variable {base : Word w} {length : Nat} {before after : Word w → Word w}

/-- The existing frame is precisely equality off the written interval.
Intervals use natural addresses, not modular word ordering. -/
theorem iff_eqOn : ArrayFrame base length before after ↔
    Set.EqOn after before
      {address : Word w | address.toNat ∈ Set.Ico base.toNat (base.toNat + length)}ᶜ := by
  constructor
  · intro h address hout
    change ¬ (base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length) at hout
    exact h address (by omega)
  · intro h address hout
    apply h
    change ¬ (base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length)
    omega

theorem eqOn (h : ArrayFrame base length before after) :
    Set.EqOn after before
      {address : Word w | address.toNat ∈ Set.Ico base.toNat (base.toNat + length)}ᶜ :=
  iff_eqOn.mp h

/-- A frame returned by any existing array contract preserves a disjoint
mathematical indexed model, irrespective of that model's data structure. -/
theorem preserves_indexed {ι : Type*} {address : ι → Word w} {values : ι → Word w}
    (h : ArrayFrame base length before after)
    (hdisjoint : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico base.toNat (base.toNat + length)})
    (model : IndexedRep before address values) : IndexedRep after address values :=
  model.frame h.eqOn hdisjoint

end ArrayFrame

namespace TwoBufferFrame

variable {first second : Word w} {firstLen secondLen : Nat}
  {before after : Word w → Word w}

/-- Two-buffer effects are equality outside the union, whether or not the
two writable intervals overlap. -/
theorem iff_eqOn : TwoBufferFrame first firstLen second secondLen before after ↔
    Set.EqOn after before
      ({address : Word w |
          address.toNat ∈ Set.Ico first.toNat (first.toNat + firstLen)} ∪
        {address : Word w |
          address.toNat ∈ Set.Ico second.toNat (second.toNat + secondLen)})ᶜ := by
  constructor
  · intro h address hout
    change ¬ ((first.toNat ≤ address.toNat ∧ address.toNat < first.toNat + firstLen) ∨
      (second.toNat ≤ address.toNat ∧ address.toNat < second.toNat + secondLen)) at hout
    exact h address (by omega) (by omega)
  · intro h address hfirst hsecond
    apply h
    change ¬ ((first.toNat ≤ address.toNat ∧ address.toNat < first.toNat + firstLen) ∨
      (second.toNat ≤ address.toNat ∧ address.toNat < second.toNat + secondLen))
    omega

theorem eqOn (h : TwoBufferFrame first firstLen second secondLen before after) :
    Set.EqOn after before
      ({address : Word w |
          address.toNat ∈ Set.Ico first.toNat (first.toNat + firstLen)} ∪
        {address : Word w |
          address.toNat ∈ Set.Ico second.toNat (second.toNat + secondLen)})ᶜ :=
  iff_eqOn.mp h

/-- The same indexed model can be retained across an existing two-buffer
contract when its observed cells lie outside both writable intervals. -/
theorem preserves_indexed {ι : Type*} {address : ι → Word w} {values : ι → Word w}
    (h : TwoBufferFrame first firstLen second secondLen before after)
    (hfirst : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico first.toNat (first.toNat + firstLen)})
    (hsecond : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico second.toNat (second.toNat + secondLen)})
    (model : IndexedRep before address values) : IndexedRep after address values :=
  model.frame h.eqOn (Set.disjoint_union_right.mpr ⟨hfirst, hsecond⟩)

end TwoBufferFrame

namespace Source.IndexedAt

variable {ι : Type*} {heapLimit length firstLen secondLen : Nat}
  {base first second : Word w} {address : ι → Word w} {values : ι → Word w}
  {s t : State w}

/-- Heap bounds and the complete indexed model survive an array effect. -/
theorem frame_array (model : IndexedAt heapLimit address values s)
    (h : ArrayFrame base length s.mem t.mem)
    (hdisjoint : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico base.toNat (base.toNat + length)}) :
    IndexedAt heapLimit address values t := model.frame h.eqOn hdisjoint

theorem frame_two (model : IndexedAt heapLimit address values s)
    (h : TwoBufferFrame first firstLen second secondLen s.mem t.mem)
    (hfirst : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico first.toNat (first.toNat + firstLen)})
    (hsecond : Disjoint (Set.range address)
      {a : Word w | a.toNat ∈ Set.Ico second.toNat (second.toNat + secondLen)}) :
    IndexedAt heapLimit address values t :=
  model.frame h.eqOn (Set.disjoint_union_right.mpr ⟨hfirst, hsecond⟩)

end Source.IndexedAt
end Ram
