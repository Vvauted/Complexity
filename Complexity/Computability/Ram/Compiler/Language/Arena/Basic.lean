/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap

/-!
# Shared-object representation in a monotone arena

The opt-in arena convention reserves address zero for a shared allocation
cursor. Every represented word's address is positive and below that cursor,
including storage for immutable-node payloads, tags and tail addresses.
Holes and empty objects are allowed. The fixed `heapLimit` separates heap and
stack. Existing `HeapRep` clients acquire no new restriction.

Reservation retains the old source heap until the fresh region is initialized.
These memory-frame rules assert neither a completed allocation nor its cost.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace HeapRep

/-- Transport heap representation using equality only on actual object words.
Unrepresented memory, registers and input/output may differ. -/
theorem of_mem_eq_on {placement : Nat → Word w} {heapLimit : Nat}
    {heap : Complexity.Language.Heap} {entry finish : Source.State w}
    (represented : HeapRep placement heapLimit heap entry)
    (same : ∀ {id : Nat} {object : HeapObject}, heap.objects[id]? = some object →
      ∀ index, index < (heapObjectWords placement object).size →
        finish.mem (arrayAddr (placement id) index) =
          entry.mem (arrayAddr (placement id) index)) :
    HeapRep placement heapLimit heap finish := by
  refine ⟨?_, represented.fit, represented.disjoint, represented.backward⟩
  intro id object found
  have whole := represented.stored found
  refine ⟨⟨whole.1.fits, ?_⟩, whole.2⟩
  intro index bound
  exact (same found index (by
    simpa only [Array.length_toList] using bound)).trans
      (whole.1.lookup index bound)

end HeapRep

/-- Complete objects below a shared bump cursor. This measures reserved extent,
not compact storage, reclaimable space or reachable live data. -/
structure ArenaRep (placement : Nat → Word w) (next heapLimit : Nat)
    (heap : Complexity.Language.Heap) (target : Source.State w) : Prop where
  heapRep : HeapRep placement heapLimit heap target
  cursor_pos : 0 < next
  cursor_le : next ≤ heapLimit
  limit_lt : heapLimit < 2 ^ w
  cursor_eq : target.mem 0 = BitVec.ofNat w next
  storedReserved : ∀ {id : Nat} {object : HeapObject}, heap.objects[id]? = some object →
    ∀ index, index < (heapObjectWords placement object).size →
      0 < (arrayAddr (placement id) index).toNat ∧
        (arrayAddr (placement id) index).toNat < next

namespace ArenaRep

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Complexity.Language.Heap} {entry finish : Source.State w}

/-- The original scalar-array reservation rule follows from reservation of
every word in both object kinds. -/
theorem reserved (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) (index : Nat)
    (bound : index < values.size) :
    0 < (arrayAddr (placement object) index).toNat ∧
      (arrayAddr (placement object) index).toNat < next :=
  arena.storedReserved (Complexity.Language.Heap.object?_eq_some_iff.mp found) index
    (by simpa only [heapObjectWords_buffer_size] using bound)

/-- The cursor is observed exactly, without modular reduction. -/
theorem cursor_toNat (arena : ArenaRep placement next heapLimit heap entry) :
    (entry.mem 0).toNat = next := by
  rw [arena.cursor_eq, Word.ofNat_toNat_of_lt (lt_of_le_of_lt arena.cursor_le arena.limit_lt)]

/-- No represented word, including a node field, occupies the metadata cell. -/
theorem stored_address_ne_zero (arena : ArenaRep placement next heapLimit heap entry)
    {id : Nat} {object : HeapObject} (found : heap.objects[id]? = some object)
    {index : Nat} (bound : index < (heapObjectWords placement object).size) :
    arrayAddr (placement id) index ≠ 0 := by
  intro same
  have positive := (arena.storedReserved found index bound).1
  simp [same] at positive

/-- Fresh arena addresses are disjoint from every old object word. -/
theorem stored_address_ne_fresh (arena : ArenaRep placement next heapLimit heap entry)
    {id : Nat} {object : HeapObject} (found : heap.objects[id]? = some object)
    {index : Nat} (bound : index < (heapObjectWords placement object).size)
    {address : Word w} (fresh : next ≤ address.toNat) :
    arrayAddr (placement id) index ≠ address := by
  intro same
  have below := (arena.storedReserved found index bound).2
  rw [same] at below
  omega

/-- Existing object cells never denote the metadata cell. -/
theorem address_ne_zero (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) {index : Nat}
    (bound : index < values.size) : arrayAddr (placement object) index ≠ 0 := by
  intro same
  have positive := (arena.reserved found index bound).1
  simp [same] at positive

/-- Addresses at or above the old cursor cannot alias any old object cell. -/
theorem address_ne_fresh (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) {index : Nat}
    (bound : index < values.size) {address : Word w} (fresh : next ≤ address.toNat) :
    arrayAddr (placement object) index ≠ address := by
  intro same
  have below := (arena.reserved found index bound).2
  rw [same] at below
  omega

/-- A frame on the positive reserved prefix transports all old objects. The
new cursor and its capacity remain explicit and independent of that frame. -/
theorem of_mem_eq_on (arena : ArenaRep placement next heapLimit heap entry)
    {next' : Nat} (grows : next ≤ next') (capacity : next' ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w next')
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep placement next' heapLimit heap finish := by
  refine ⟨arena.heapRep.of_mem_eq_on ?_, lt_of_lt_of_le arena.cursor_pos grows,
    capacity, arena.limit_lt, cursor, ?_⟩
  · intro id object found index bound
    exact same _ (arena.storedReserved found index bound).1
      (arena.storedReserved found index bound).2
  · intro id object found index bound
    exact ⟨(arena.storedReserved found index bound).1,
      lt_of_lt_of_le (arena.storedReserved found index bound).2 grows⟩

/-- Updating metadata reserves space but does not pretend to initialize it. -/
theorem reserve (arena : ArenaRep placement next heapLimit heap entry)
    {next' : Nat} (grows : next ≤ next') (capacity : next' ≤ heapLimit) :
    ArenaRep placement next' heapLimit heap (entry.setMem 0 (BitVec.ofNat w next')) := by
  apply arena.of_mem_eq_on grows capacity
  · simp [Source.State.setMem]
  · intro address positive _
    have nonzero : address ≠ 0 := by
      intro same
      simp [same] at positive
    simp only [Source.State.setMem, if_neg nonzero]

/-- An initialization store at a fresh address preserves every old object. -/
theorem heapRep_setMem_fresh (arena : ArenaRep placement next heapLimit heap entry)
    (address value : Word w) (fresh : next ≤ address.toNat) :
    HeapRep placement heapLimit heap (entry.setMem address value) := by
  apply arena.heapRep.of_mem_eq_on
  intro id object found index bound
  simp only [Source.State.setMem, if_neg (arena.stored_address_ne_fresh found bound fresh)]

end ArenaRep
end Ram.LanguageCompiler
