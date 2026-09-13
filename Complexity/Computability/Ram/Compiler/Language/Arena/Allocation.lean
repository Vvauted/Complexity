/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Allocation
import Complexity.Computability.Ram.Compiler.Language.Placement
import Complexity.Computability.Ram.Compiler.Language.Arena.Basic

/-!
# Representing a completed arena allocation

A fully initialized fresh RAM interval represents an arbitrary native array
appended to the source heap. `Heap.alloc` specializes this to a replicated value.
The old positive prefix is framed, placement changes only at the new object
identifier, and the cursor records the enlarged reserved extent.
Empty arrays still acquire a fresh source identity and need no stored cell.

These theorems consume the actual runtime's initialization and frame results.
They do not perform allocation, assume a machine execution, or assign its cost.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The fresh source view encodes the base and length returned by the allocator.
This is an equality of descriptors, not a runtime conversion. -/
@[simp] theorem bufferRef_alloc (heap : Complexity.Language.Heap)
    (placement : Nat → Word w) (base : Word w) {τ : CellTy}
    (length : Nat) (initial : CellValue τ) :
    bufferRef (Function.update placement heap.objects.size base)
      (heap.alloc length initial).1 = ⟨base, BitVec.ofNat w length⟩ := by
  simp [bufferRef, Complexity.Language.Heap.alloc, arrayAddr]

namespace ArenaRep

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Complexity.Language.Heap} {entry finish : Source.State w}

/-- An initialized fresh interval extends the complete arena by one arbitrary
native buffer. Every actual cell has an exact word encoding, and the old
positive prefix is retained without constraining unrepresented memory. -/
theorem push_buffer (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {xs : Array (CellValue τ)}
    (cellsFit : ∀ (index : Nat) (bound : index < xs.size), cellToNat xs[index] < 2 ^ w)
    (capacity : next + xs.size ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + xs.size))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (objectWords w xs).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + xs.size) heapLimit ⟨heap.objects.push (.buffer τ xs)⟩ finish := by
  have oldArena := arena.of_mem_eq_on (Nat.le_add_right next xs.size) capacity cursor same
  let placed := Function.update placement heap.objects.size (BitVec.ofNat w next)
  have agreed : Placement.Agrees heap placement placed :=
    Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
      (BitVec.ofNat w next)
  have oldRepresented := oldArena.heapRep.placement agreed
  have oldFound : ∀ {object : Nat} {stored : HeapObject},
      object ≠ heap.objects.size →
      (heap.objects.push (.buffer τ xs))[object]? = some stored →
      heap.objects[object]? = some stored := by
    intro object stored different found
    simpa only [Array.getElem?_push, if_neg different] using found
  have retained : ∀ {object : Nat} {stored : HeapObject},
      heap.objects[object]? = some stored →
        ∀ index, index < (heapObjectWords placed stored).size →
          0 < (arrayAddr (placed object) index).toNat ∧
            (arrayAddr (placed object) index).toNat < next := by
    intro object stored found index bound
    rw [← agreed (Array.getElem?_eq_some_iff.mp found).choose]
    exact arena.storedReserved found index (by
      rw [heapObjectWords_size_eq placement placed stored]
      exact bound)
  have fresh : ∀ {stored : HeapObject},
      (heap.objects.push (.buffer τ xs))[heap.objects.size]? = some stored →
      Source.ArrayAt heapLimit (BitVec.ofNat w next)
        (heapObjectWords placed stored).toList finish ∧
      heapObjectFits w stored ∧
      (∀ index, index < (heapObjectWords placed stored).size →
        next ≤ (arrayAddr (BitVec.ofNat w next) index).toNat ∧
          (arrayAddr (BitVec.ofNat w next) index).toNat < next + xs.size) := by
    intro stored found
    have sameStored : stored = .buffer τ xs :=
      Option.some.inj (found.symm.trans Array.getElem?_push_size)
    subst stored
    refine ⟨initialized, cellsFit, ?_⟩
    intro index bound
    have indexBound : index < xs.size := by
      simpa only [heapObjectWords_buffer_size] using bound
    have encodedBound : index < (objectWords w xs).toList.length := by
      simpa only [objectWords, Array.length_toList, Array.size_map] using indexBound
    have address := initialized.1.addr_toNat encodedBound
    rw [Word.ofNat_toNat_of_lt (lt_of_le_of_lt arena.cursor_le arena.limit_lt)] at address
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lt_of_lt_of_le arena.cursor_pos (Nat.le_add_right next xs.size),
    capacity, arena.limit_lt, cursor, ?_⟩
  · intro object stored found
    by_cases isFresh : object = heap.objects.size
    · subst object
      simpa only [placed, Function.update_self] using (fresh found).1
    · exact oldRepresented.stored (oldFound isFresh found)
  · intro object stored found
    by_cases isFresh : object = heap.objects.size
    · subst object
      exact (fresh found).2.1
    · exact oldRepresented.fit (oldFound isFresh found)
  · intro object other stored otherStored found otherFound different
      index bound otherIndex otherBound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have oldOther := oldFound different.symm otherFound
      have below := (retained oldOther otherIndex otherBound).2
      have above := (fresh found).2.2 index bound |>.1
      simp only [Function.update_self]
      intro equal
      change arrayAddr (BitVec.ofNat w next) index = arrayAddr (placed other) otherIndex at equal
      rw [equal] at above
      omega
    · by_cases otherFresh : other = heap.objects.size
      · subst other
        have oldObject := oldFound isFresh found
        have below := (retained oldObject index bound).2
        have above := (fresh otherFound).2.2 otherIndex otherBound |>.1
        simp only [Function.update_self]
        intro equal
        change arrayAddr (placed object) index = arrayAddr (BitVec.ofNat w next) otherIndex at equal
        rw [← equal] at above
        omega
      · exact oldRepresented.disjoint
          (oldFound isFresh found) (oldFound otherFresh otherFound)
          different index bound otherIndex otherBound
  · intro kind object head tail found
    have pushed := Complexity.Language.Heap.node?_eq_some_iff.mp found
    have notFresh : object ≠ heap.objects.size := by
      intro isFresh
      subst object
      have impossible : HeapObject.node kind head (some tail) = .buffer τ xs :=
        Option.some.inj (pushed.symm.trans Array.getElem?_push_size)
      cases impossible
    exact arena.heapRep.backward
      (Complexity.Language.Heap.node?_eq_some_iff.mpr (oldFound notFresh pushed))
  · intro object stored found index bound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have bounds := (fresh found).2.2 index bound
      simp only [Function.update_self]
      exact ⟨lt_of_lt_of_le arena.cursor_pos bounds.1, bounds.2⟩
    · have bounds := retained (oldFound isFresh found) index bound
      exact ⟨bounds.1, lt_of_lt_of_le bounds.2 (Nat.le_add_right next xs.size)⟩

/-- Complete initialization and preservation of the old positive prefix extend
the arena representation by exactly the fresh source object. Capacity also
ensures that the new cursor and array length have exact word encodings. -/
theorem alloc (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {length : Nat} {initial : CellValue τ}
    (initialFits : cellToNat initial < 2 ^ w)
    (capacity : next + length ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + length))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (objectWords w (Array.replicate length initial)).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + length) heapLimit (heap.alloc length initial).2 finish := by
  have cellsFit : ∀ (index : Nat) (bound : index < (Array.replicate length initial).size),
      cellToNat (Array.replicate length initial)[index] < 2 ^ w := by
    intro index bound
    simpa only [Array.getElem_replicate] using initialFits
  simpa only [Array.size_replicate, Complexity.Language.Heap.alloc] using
    arena.push_buffer (τ := τ) (xs := Array.replicate length initial) cellsFit
      (by simpa only [Array.size_replicate] using capacity)
      (by simpa only [Array.size_replicate] using cursor) initialized same

/-- The returned source view has the fully initialized RAM contents and exact
two-word descriptor, including for length zero. -/
theorem alloc_view (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {length : Nat} {initial : CellValue τ}
    (initialFits : cellToNat initial < 2 ^ w)
    (capacity : next + length ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + length))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (objectWords w (Array.replicate length initial)).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    (bufferRef (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (heap.alloc length initial).1).Rep heapLimit
      (objectWords w (Array.replicate length initial)).toList finish := by
  apply (arena.alloc initialFits capacity cursor initialized same).heapRep.view
    (heap.alloc_contents length initial)
  change length < 2 ^ w
  have limit := arena.limit_lt
  omega

end ArenaRep
end Ram.LanguageCompiler
