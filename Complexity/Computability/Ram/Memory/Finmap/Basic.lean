/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Frame
import Mathlib.Data.Finmap

/-!
# Direct-address partial maps with ordinary mathlib specifications

The layout reserves two cells for each represented key: `(key, false)` holds
a presence marker and `(key, true)` holds its value. A zero marker means
absence; every nonzero marker means presence, including when the value is
zero. Payload cells of absent keys may contain arbitrary data.

`FinmapRep` describes this memory using mathlib's existing `Finmap.lookup`.
The update laws reuse `Finmap.insert` and `Finmap.erase`: insertion writes
the payload first and then a nonzero marker, while erasure clears only the
marker. Empty-map initialization requires every marker to be zero explicitly.

This is a direct-address representation over a bounded key universe, not a
sparse-map or hash-table implementation. An injective layout into word
addresses is required by the update laws; in particular it cannot cover an
infinite key type. Address computation, allocation, and instruction counts
are not supplied by this representation. Source heap bounds remain explicit
in `Source.FinmapAt`, which transfers through the existing compiler observations.
The shared `Set.EqOn`/`Disjoint` endpoint-frame interface preserves the table
using its full reserved footprint. This is a sufficient condition; the finer
`FinmapRep.congr_mem` rule still ignores payload cells of absent keys.
-/

namespace Ram

universe u

/-- Observe a key through its presence cell and, when present, its value cell. -/
def finmapLookup {κ : Type u} (mem : Word w → Word w)
    (address : κ × Bool → Word w) (key : κ) : Option (Word w) :=
  if mem (address (key, false)) = 0 then none else some (mem (address (key, true)))

/-- A direct-address table represents the native optional lookups of a finite
map. Absence constrains the marker but does not constrain the payload. -/
def FinmapRep {κ : Type u} [DecidableEq κ] (mem : Word w → Word w)
    (address : κ × Bool → Word w) (map : Finmap (fun _ : κ => Word w)) : Prop :=
  ∀ key, finmapLookup mem address key = map.lookup key

namespace FinmapRep

variable {κ : Type u} [DecidableEq κ] {mem before after : Word w → Word w}
  {address : κ × Bool → Word w} {map other : Finmap (fun _ : κ => Word w)}

theorem lookup (h : FinmapRep mem address map) (key : κ) :
    finmapLookup mem address key = map.lookup key := h key

/-- The full lookup observation is a function equality for ordinary rewriting. -/
theorem contents_eq (h : FinmapRep mem address map) :
    finmapLookup mem address = fun key => map.lookup key := funext h

/-- Extensional equality is mathlib's native finite-map equality, not equality
of unrelated heap cells or of an implementation's physical layout. -/
theorem eq (h : FinmapRep mem address map) (h' : FinmapRep mem address other) :
    map = other :=
  Finmap.ext_lookup (fun key => (h key).symm.trans (h' key))

theorem lookup_eq_none_iff (h : FinmapRep mem address map) (key : κ) :
    map.lookup key = none ↔ mem (address (key, false)) = 0 := by
  rw [← h.lookup key]
  by_cases hz : mem (address (key, false)) = 0 <;> simp [finmapLookup, hz]

theorem lookup_eq_some_iff (h : FinmapRep mem address map) (key : κ) (value : Word w) :
    map.lookup key = some value ↔
      mem (address (key, false)) ≠ 0 ∧ mem (address (key, true)) = value := by
  rw [← h.lookup key]
  by_cases hz : mem (address (key, false)) = 0 <;> simp [finmapLookup, hz]

/-- The mathematical domain is determined by markers, never by whether the
payload happens to be zero. -/
theorem notMem_iff (h : FinmapRep mem address map) (key : κ) :
    key ∉ map ↔ mem (address (key, false)) = 0 :=
  Finmap.lookup_eq_none.symm.trans (h.lookup_eq_none_iff key)

/-- Empty representation requires initialized markers, but no initialized payloads. -/
theorem empty (flags : ∀ key, mem (address (key, false)) = 0) :
    FinmapRep mem address (∅ : Finmap (fun _ : κ => Word w)) := by
  intro key
  simp [finmapLookup, flags key]

/-- Only payloads of present keys need to be preserved. In particular, garbage
in an absent key's value cell is not part of the represented map. -/
theorem congr_mem (h : FinmapRep before address map)
    (flags : ∀ key, after (address (key, false)) = before (address (key, false)))
    (values : ∀ key, before (address (key, false)) ≠ 0 →
      after (address (key, true)) = before (address (key, true))) :
    FinmapRep after address map := by
  intro key
  rw [← h.lookup key]
  unfold finmapLookup
  rw [flags key]
  by_cases hz : before (address (key, false)) = 0
  · simp only [if_pos hz]
  · simp only [if_neg hz, values key hz]

/-- Agreement on the complete reserved footprint is a sufficient frame.
The payload-sensitive `congr_mem` rule permits additional changes. -/
theorem congr_eqOn (h : FinmapRep before address map)
    (hmem : Set.EqOn after before (Set.range address)) :
    FinmapRep after address map :=
  h.congr_mem (fun key => hmem ⟨(key, false), rfl⟩)
    (fun key _ => hmem ⟨(key, true), rfl⟩)

/-- Reuse the shared whole-block endpoint frame for a disjoint table.
No claim about intermediate states or exact write events is made. -/
theorem frame {writes : Set (Word w)} (h : FinmapRep before address map)
    (hframe : Set.EqOn after before writesᶜ)
    (hdisjoint : Disjoint (Set.range address) writes) :
    FinmapRep after address map :=
  h.congr_eqOn (Set.EqOn.mono
    (fun _ hi => hdisjoint.notMem_of_mem_left hi) hframe)

/-- The final memory of a payload store followed by a presence-marker store
represents native insertion. A zero payload is a valid present value. -/
theorem store_insert (h : FinmapRep mem address map)
    (hinj : Function.Injective address) (key : κ) (value marker : Word w)
    (hmarker : marker ≠ 0) :
    FinmapRep
      (fun a => if a = address (key, false) then marker
        else if a = address (key, true) then value else mem a)
      address (map.insert key value) := by
  intro query
  by_cases hquery : query = key
  · subst query
    simp [finmapLookup, hinj.eq_iff]
    exact hmarker
  · rw [Finmap.lookup_insert_of_ne _ hquery]
    simpa [finmapLookup, hinj.eq_iff, hquery] using h.lookup query

/-- Clearing the marker is native erasure; the payload remains untouched. -/
theorem store_erase (h : FinmapRep mem address map)
    (hinj : Function.Injective address) (key : κ) :
    FinmapRep (fun a => if a = address (key, false) then 0 else mem a)
      address (map.erase key) := by
  intro query
  by_cases hquery : query = key
  · subst query
    simp [finmapLookup]
  · rw [Finmap.lookup_erase_ne hquery]
    simpa [finmapLookup, hinj.eq_iff, hquery] using h.lookup query

/-- Stores outside the reserved table cells preserve all optional lookups. -/
theorem store_outside (h : FinmapRep mem address map) (storedAt value : Word w)
    (hout : ∀ cell, address cell ≠ storedAt) :
    FinmapRep (fun a => if a = storedAt then value else mem a) address map := by
  apply h.congr_mem
  · intro key
    simp only [if_neg (hout (key, false))]
  · intro key _
    simp only [if_neg (hout (key, true))]

theorem setMem_insert {s : State w} (h : FinmapRep s.mem address map)
    (hinj : Function.Injective address) (key : κ) (value marker : Word w)
    (hmarker : marker ≠ 0) :
    FinmapRep ((s.setMem (address (key, true)) value).setMem
      (address (key, false)) marker).mem address (map.insert key value) :=
  h.store_insert hinj key value marker hmarker

theorem setMem_erase {s : State w} (h : FinmapRep s.mem address map)
    (hinj : Function.Injective address) (key : κ) :
    FinmapRep (s.setMem (address (key, false)) 0).mem address (map.erase key) :=
  h.store_erase hinj key

end FinmapRep

namespace Source

/-- A direct-address finite map whose reserved cells lie in the visible heap. -/
def FinmapAt {κ : Type u} [DecidableEq κ] (heapLimit : Nat)
    (address : κ × Bool → Word w) (map : Finmap (fun _ : κ => Word w)) (s : State w) : Prop :=
  FinmapRep s.mem address map ∧ ∀ cell, (address cell).toNat < heapLimit

namespace FinmapAt

variable {κ : Type u} [DecidableEq κ] {heapLimit : Nat}
  {address : κ × Bool → Word w} {map : Finmap (fun _ : κ => Word w)} {s t : State w}

theorem lookup (h : FinmapAt heapLimit address map s) (key : κ) :
    finmapLookup s.mem address key = map.lookup key := h.1.lookup key

theorem addr_lt (h : FinmapAt heapLimit address map s) (cell : κ × Bool) :
    (address cell).toNat < heapLimit := h.2 cell

theorem contents_eq (h : FinmapAt heapLimit address map s) :
    finmapLookup s.mem address = fun key => map.lookup key := h.1.contents_eq

theorem congr_eqOn (h : FinmapAt heapLimit address map s)
    (hmem : Set.EqOn t.mem s.mem (Set.range address)) :
    FinmapAt heapLimit address map t := ⟨h.1.congr_eqOn hmem, h.2⟩

/-- Framing retains both the mathematical map and its source-visible heap bounds. -/
theorem frame {writes : Set (Word w)} (h : FinmapAt heapLimit address map s)
    (hframe : Set.EqOn t.mem s.mem writesᶜ)
    (hdisjoint : Disjoint (Set.range address) writes) :
    FinmapAt heapLimit address map t := ⟨h.1.frame hframe hdisjoint, h.2⟩

theorem setReg (h : FinmapAt heapLimit address map s) (dst : Reg) (value : Word w) :
    FinmapAt heapLimit address map (s.setReg dst value) := h

theorem setMem_insert (h : FinmapAt heapLimit address map s)
    (hinj : Function.Injective address) (key : κ) (value marker : Word w)
    (hmarker : marker ≠ 0) :
    FinmapAt heapLimit address (map.insert key value)
      ((s.setMem (address (key, true)) value).setMem (address (key, false)) marker) :=
  ⟨h.1.store_insert hinj key value marker hmarker, h.2⟩

theorem setMem_erase (h : FinmapAt heapLimit address map s)
    (hinj : Function.Injective address) (key : κ) :
    FinmapAt heapLimit address (map.erase key) (s.setMem (address (key, false)) 0) :=
  ⟨h.1.store_erase hinj key, h.2⟩

theorem setMem_outside (h : FinmapAt heapLimit address map s) (storedAt value : Word w)
    (hout : ∀ cell, address cell ≠ storedAt) :
    FinmapAt heapLimit address map (s.setMem storedAt value) :=
  ⟨h.1.store_outside storedAt value hout, h.2⟩

/-- Source-visible heap agreement is enough; private stack cells are not part
of the table representation. -/
theorem heapEqBelow (h : FinmapAt heapLimit address map s)
    (hmem : HeapEqBelow heapLimit s.mem t.mem) : FinmapAt heapLimit address map t :=
  ⟨h.1.congr_mem (fun key => (hmem _ (h.2 (key, false))).symm)
    (fun key _ => (hmem _ (h.2 (key, true))).symm), h.2⟩

end FinmapAt

/-- The same finite-map lookups hold on the actual target heap, including
after halt. This uses the existing source/target compiler observation. -/
theorem State.Observes.finmap {κ : Type u} [DecidableEq κ] {heapLimit locals : Nat}
    {address : κ × Bool → Word w} {map : Finmap (fun _ : κ => Word w)}
    {s : Source.State w} {t : Ram.State w} (ho : State.Observes heapLimit locals s t)
    (h : FinmapAt heapLimit address map s) : FinmapRep t.mem address map :=
  h.1.congr_mem (fun key => (ho.heap _ (h.2 (key, false))).symm)
    (fun key _ => (ho.heap _ (h.2 (key, true))).symm)

end Source
end Ram
