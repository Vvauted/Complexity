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

A fully initialized fresh RAM interval represents the native array appended by
`Heap.alloc`. The old positive prefix is framed, placement changes only at the
new object identifier, and the cursor records the enlarged reserved extent.
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
  have oldArena := arena.of_mem_eq_on (Nat.le_add_right next length) capacity cursor same
  have agreed := Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
    (BitVec.ofNat w next)
  have oldRepresented := oldArena.heapRep.placement agreed
  have retained : ∀ {σ : CellTy} {object : Nat} {values : Array (CellValue σ)},
      heap.object? σ object = some values → ∀ index, index < values.size →
        0 < (arrayAddr
          (Function.update placement heap.objects.size (BitVec.ofNat w next) object) index).toNat ∧
        (arrayAddr
          (Function.update placement heap.objects.size (BitVec.ofNat w next) object) index).toNat < next := by
    intro σ object values found index bound
    rw [← agreed (Complexity.Language.Heap.object_lt_size found)]
    exact arena.reserved found index bound
  have fresh : ∀ {σ : CellTy} {values : Array (CellValue σ)},
      (heap.alloc length initial).2.object? σ heap.objects.size = some values →
      Source.ArrayAt heapLimit (BitVec.ofNat w next) (objectWords w values).toList finish ∧
      (∀ index (bound : index < values.size), cellToNat values[index] < 2 ^ w) ∧
      (∀ index, index < values.size →
        next ≤ (arrayAddr (BitVec.ofNat w next) index).toNat ∧
          (arrayAddr (BitVec.ofNat w next) index).toNat < next + length) := by
    intro σ values found
    have actual : (heap.alloc length initial).2.object? τ heap.objects.size =
        some (Array.replicate length initial) := heap.object?_alloc_new length initial
    have stored : (⟨σ, values⟩ : HeapObject) = ⟨τ, Array.replicate length initial⟩ := by
      apply Option.some.inj
      exact (Complexity.Language.Heap.object?_eq_some_iff.mp found).symm.trans
        (Complexity.Language.Heap.object?_eq_some_iff.mp actual)
    have sameType : σ = τ := congrArg Sigma.fst stored
    subst σ
    have sameValues : values = Array.replicate length initial :=
      Option.some.inj (found.symm.trans actual)
    subst values
    refine ⟨initialized, ?_, ?_⟩
    · intro index bound
      simpa only [Array.getElem_replicate] using initialFits
    · intro index bound
      have encodedBound : index < (objectWords w (Array.replicate length initial)).toList.length := by
        simpa only [objectWords, Array.length_toList, Array.size_map] using bound
      have address := initialized.1.addr_toNat encodedBound
      rw [Word.ofNat_toNat_of_lt (lt_of_le_of_lt arena.cursor_le arena.limit_lt)] at address
      have indexBound : index < length := by simpa only [Array.size_replicate] using bound
      omega
  refine ⟨⟨?_, ?_, ?_⟩, lt_of_lt_of_le arena.cursor_pos (Nat.le_add_right next length),
    capacity, arena.limit_lt, cursor, ?_⟩
  · intro σ object values found
    by_cases isFresh : object = heap.objects.size
    · subst object
      simpa only [Function.update_self] using (fresh found).1
    · exact oldRepresented.objects
        ((heap.object?_alloc_of_ne length initial isFresh).symm.trans found)
  · intro σ object values found index bound
    by_cases isFresh : object = heap.objects.size
    · subst object
      exact (fresh found).2.1 index bound
    · exact oldRepresented.ranges
        ((heap.object?_alloc_of_ne length initial isFresh).symm.trans found) index bound
  · intro σ ρ object other values otherValues found otherFound different
      index bound otherIndex otherBound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have oldFound := (heap.object?_alloc_of_ne length initial different.symm).symm.trans otherFound
      have below := (retained oldFound otherIndex otherBound).2
      have above := (fresh found).2.2 index bound |>.1
      simp only [Function.update_self]
      intro equal
      rw [equal] at above
      omega
    · by_cases otherFresh : other = heap.objects.size
      · subst other
        have oldFound := (heap.object?_alloc_of_ne length initial isFresh).symm.trans found
        have below := (retained oldFound index bound).2
        have above := (fresh otherFound).2.2 otherIndex otherBound |>.1
        simp only [Function.update_self]
        intro equal
        rw [← equal] at above
        omega
      · exact oldRepresented.separated
          ((heap.object?_alloc_of_ne length initial isFresh).symm.trans found)
          ((heap.object?_alloc_of_ne length initial otherFresh).symm.trans otherFound)
          different index bound otherIndex otherBound
  · intro σ object values found index bound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have bounds := (fresh found).2.2 index bound
      simp only [Function.update_self]
      exact ⟨lt_of_lt_of_le arena.cursor_pos bounds.1, bounds.2⟩
    · have oldFound := (heap.object?_alloc_of_ne length initial isFresh).symm.trans found
      have bounds := retained oldFound index bound
      exact ⟨bounds.1, by omega⟩

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
