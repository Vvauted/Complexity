/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Restriction
import Complexity.Computability.Ram.Compiler.Language.Arena.Basic
import Complexity.Computability.Ram.Compiler.Language.Placement

/-!
# Retaining current objects when restoring an arena cursor

Heap restriction forgets the newly allocated object suffix, not writes to older
objects. Their current contents remain represented in the current RAM memory.
The initial arena shape and stable placement put every retained cell below the
saved cursor; restoring only its metadata therefore preserves those contents.

These are representation rules. They do not establish that discarded handles
cannot escape or that a reset instruction has executed.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem object_lt_take_count {heap : Complexity.Language.Heap} {count object : Nat}
    {kind : CellTy} {values : Array (CellValue kind)}
    (found : (heap.take count).object? kind object = some values) : object < count := by
  have bound := Complexity.Language.Heap.object_lt_size found
  rw [Complexity.Language.Heap.take_size] at bound
  exact lt_of_lt_of_le bound (Nat.min_le_left _ _)

private theorem object?_of_take {heap : Complexity.Language.Heap} {count object : Nat}
    {kind : CellTy} {values : Array (CellValue kind)}
    (found : (heap.take count).object? kind object = some values) :
    heap.object? kind object = some values :=
  (heap.object?_take_of_lt count (object_lt_take_count found)).symm.trans found

namespace HeapRep

/-- Forgetting an object suffix preserves representation of every retained
object's current contents, scalar ranges and separation. No memory is restored. -/
theorem take {w heapLimit : Nat} {placement : Nat → Word w}
    {heap : Complexity.Language.Heap} {target : Source.State w}
    (represented : HeapRep placement heapLimit heap target) (count : Nat) :
    HeapRep placement heapLimit (heap.take count) target := by
  refine ⟨?_, ?_, ?_⟩
  · intro kind object values found
    exact represented.objects (object?_of_take found)
  · intro kind object values found index bound
    exact represented.ranges (object?_of_take found) index bound
  · intro kind otherKind object other values otherValues found otherFound different
      index bound otherIndex otherBound
    exact represented.separated (object?_of_take found) (object?_of_take otherFound)
      different index bound otherIndex otherBound

end HeapRep

namespace ArenaRep

/-- Restore the saved cursor while retaining the current contents of every
pre-existing object. Shape extension and stable old placement recover the saved
address bound; current representation supplies the actual possibly updated cells.
Discarded suffix objects no longer impose any representation obligation. -/
theorem take {w start stop heapLimit : Nat} {initial current : Complexity.Language.Heap}
    {initialPlacement currentPlacement : Nat → Word w} {entry target : Source.State w}
    (initialArena : ArenaRep initialPlacement start heapLimit initial entry)
    (finalArena : ArenaRep currentPlacement stop heapLimit current target)
    (growth : initial.ShapeExtends current)
    (agreement : Placement.Agrees initial initialPlacement currentPlacement) :
    ArenaRep currentPlacement start heapLimit (current.take initial.objects.size)
      (target.setMem 0 (BitVec.ofNat w start)) := by
  have reserved : ∀ {kind : CellTy} {object : Nat} {values : Array (CellValue kind)},
      (current.take initial.objects.size).object? kind object = some values →
        ∀ index, index < values.size →
          0 < (arrayAddr (currentPlacement object) index).toNat ∧
            (arrayAddr (currentPlacement object) index).toNat < start := by
    intro kind object values found index bound
    have retained := object_lt_take_count found
    obtain ⟨oldValues, oldFound, sameSize⟩ :=
      growth.objects_of_lt retained (object?_of_take found)
    have oldBound : index < oldValues.size := by simpa only [sameSize] using bound
    simpa only [agreement retained] using initialArena.reserved oldFound index oldBound
  refine ⟨(finalArena.heapRep.take initial.objects.size).of_mem_eq_on ?_,
    initialArena.cursor_pos, initialArena.cursor_le, initialArena.limit_lt, ?_, reserved⟩
  · intro kind object values found index bound
    have positive := (reserved found index bound).1
    have nonzero : arrayAddr (currentPlacement object) index ≠ 0 := by
      intro same
      simp only [same] at positive
      exact (Nat.lt_irrefl 0) positive
    simp only [Source.State.setMem, if_neg nonzero]
  · simp [Source.State.setMem]

end ArenaRep
end Ram.LanguageCompiler
