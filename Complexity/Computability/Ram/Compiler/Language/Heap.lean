/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap
import Complexity.Computability.Ram.Array.Indexed
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Basic
import Init.Data.Array.Extract

/-!
# Representing shared source objects in RAM memory

One fixed mathematical placement gives each source object a RAM base address.
The complete current native array is represented at that address; borrowed
views derive their base and length without copying contents or storing an
object table. Views of the same object may overlap or coincide. Distinct
objects have disjoint actual cells, with no condition on empty objects' unused
addresses.

Natural cells must fit the target word and Boolean cells use their exact
zero-or-one encoding. Object intervals retain the existing non-strict endpoint
bound. A view's length needs its own word-range premise only when exposed as a
two-word `ArrayRef`. No injectivity of source handle encoding is asserted.

The read and write theorems relate the existing source heap operations to the
existing RAM memory update. They do not add an evaluator, allocation, a loader,
statement syntax, instruction prices or a complete buffer-lowering theorem.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Exact mathematical scalar observation of a source object cell. -/
def cellToNat : {τ : CellTy} → CellValue τ → Nat
  | .nat, value => value
  | .bool, value => if value then 1 else 0

/-- One actual word for a source cell; exactness is a separate range fact. -/
def cellWord (w : Nat) {τ : CellTy} (value : CellValue τ) : Word w :=
  BitVec.ofNat w (cellToNat value)

/-- Encode the existing native array elementwise, without loading any memory. -/
def objectWords (w : Nat) {τ : CellTy} (values : Array (CellValue τ)) : Array (Word w) :=
  values.map (cellWord w)

/-- Two-word metadata for a view of a placed object. This is not a runtime
conversion and does not recover the source object's identity from the fields. -/
def bufferRef (placement : Nat → Word w) {τ : CellTy} (buffer : Buffer τ) : ArrayRef w :=
  ⟨arrayAddr (placement buffer.object) buffer.offset, BitVec.ofNat w buffer.length⟩

/-- A fitting cell is observed as its exact mathematical value, not a residue. -/
theorem cellWord_toNat {τ : CellTy} {value : CellValue τ}
    (fits : cellToNat value < 2 ^ w) : (cellWord w value).toNat = cellToNat value :=
  Word.ofNat_toNat_of_lt fits

/-- Complete typed objects, their scalar ranges and separation of actual cells.
The placement is fixed across heap updates and real function calls. -/
structure HeapRep (placement : Nat → Word w) (heapLimit : Nat)
    (heap : Complexity.Language.Heap) (target : Source.State w) : Prop where
  /-- Each successful typed object lookup describes its complete native contents. -/
  objects : ∀ {τ : CellTy} {object : Nat} {values : Array (CellValue τ)},
    heap.object? τ object = some values →
      Source.ArrayAt heapLimit (placement object) (objectWords w values).toList target
  /-- Every represented cell has its exact scalar value at the selected width. -/
  ranges : ∀ {τ : CellTy} {object : Nat} {values : Array (CellValue τ)},
    heap.object? τ object = some values →
      ∀ (index : Nat) (bound : index < values.size), cellToNat values[index] < 2 ^ w
  /-- Only different objects' actual cells are separated, never arbitrary views. -/
  separated : ∀ {τ σ : CellTy} {object other : Nat}
    {values : Array (CellValue τ)} {otherValues : Array (CellValue σ)},
    heap.object? τ object = some values → heap.object? σ other = some otherValues →
      object ≠ other → ∀ (index : Nat), index < values.size →
        ∀ (otherIndex : Nat), otherIndex < otherValues.size →
          arrayAddr (placement object) index ≠ arrayAddr (placement other) otherIndex

namespace HeapRep

variable {w heapLimit : Nat} {placement : Nat → Word w}
variable {heap finish : Complexity.Language.Heap} {target : Source.State w}

/-- Parameter binding retains the same complete shared-heap representation. -/
theorem enter (represented : HeapRep placement heapLimit heap target)
    (args : List (Word w)) : HeapRep placement heapLimit heap (target.enter args) := by
  refine ⟨?_, represented.ranges, represented.separated⟩
  intro τ object contents found
  exact (represented.objects found).enter args

/-- Receiving actual return fields changes no represented heap cell. -/
theorem setRegs (represented : HeapRep placement heapLimit heap target)
    (dsts : List Reg) (values : List (Word w)) :
    HeapRep placement heapLimit heap (target.setRegs dsts values) := by
  refine ⟨?_, represented.ranges, represented.separated⟩
  intro τ object contents found
  simpa only [Source.ArrayAt, Source.State.setRegs_mem] using represented.objects found

/-- Caller restoration keeps the callee's final heap, not the caller's old heap. -/
theorem restore (represented : HeapRep placement heapLimit heap target)
    (caller : Source.State w) : HeapRep placement heapLimit heap (caller.restore target) := by
  refine ⟨?_, represented.ranges, represented.separated⟩
  intro τ object contents found
  simpa only [Source.ArrayAt, Source.State.restore_mem] using represented.objects found

/-- A view's current native contents use the existing contiguous-array
assertion. Even an empty view at the allocation endpoint is admitted. -/
theorem view_arrayAt (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {buffer : Buffer τ} {contents : Array (CellValue τ)}
    (observed : buffer.Contents heap contents) :
    Source.ArrayAt heapLimit (bufferRef placement buffer).base
      (objectWords w contents).toList target := by
  obtain ⟨values, found, extent, rfl⟩ := observed
  have whole := represented.objects found
  have offsetBound : buffer.offset ≤ (objectWords w values).toList.length := by
    simp only [Array.length_toList, objectWords, Array.size_map]
    omega
  simpa only [bufferRef, objectWords, Array.map_extract, Array.toList_extract,
    List.extract_eq_drop_take, Nat.add_sub_cancel_left] using
    whole.slice offsetBound buffer.length

/-- A word-sized view is exactly the existing by-value `ArrayRef` together
with its actual native contents. The descriptor allocates and copies nothing. -/
theorem view (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {buffer : Buffer τ} {contents : Array (CellValue τ)}
    (observed : buffer.Contents heap contents) (lengthFits : buffer.length < 2 ^ w) :
    (bufferRef placement buffer).Rep heapLimit (objectWords w contents).toList target := by
  refine ⟨?_, represented.view_arrayAt observed⟩
  change (BitVec.ofNat w buffer.length).toNat = (objectWords w contents).toList.length
  rw [Word.ofNat_toNat_of_lt lengthFits]
  simpa only [Array.length_toList, objectWords, Array.size_map] using observed.size_eq.symm

/-- Every successful source read is the exact represented RAM cell, lies below
the heap boundary and returns a source scalar fitting the target word. -/
theorem read (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    (read : heap.read buffer index = .ok value) :
    target.mem (arrayAddr (bufferRef placement buffer).base index) = cellWord w value ∧
      (arrayAddr (bufferRef placement buffer).base index).toNat < heapLimit ∧
      cellToNat value < 2 ^ w := by
  cases found : heap.object? τ buffer.object with
  | none => simp [Complexity.Language.Heap.read, found] at read
  | some values =>
      by_cases extent : buffer.offset + buffer.length ≤ values.size
      · by_cases bound : index < buffer.length
        · have absoluteBound : buffer.offset + index < values.size := by omega
          have sourceValue : values[buffer.offset + index] = value :=
            Except.ok.inj ((Complexity.Language.Heap.read_eq found extent bound).symm.trans read)
          have contents := represented.objects found
          have encodedBound : buffer.offset + index < (objectWords w values).toList.length := by
            simpa only [Array.length_toList, objectWords, Array.size_map] using absoluteBound
          refine ⟨?_, ?_, ?_⟩
          · have observed := contents.1.lookup (buffer.offset + index) encodedBound
            simpa only [bufferRef, arrayAddr_add, objectWords, Array.getElem_toList,
              Array.getElem_map, sourceValue] using observed
          · simpa only [bufferRef, arrayAddr_add] using contents.addr_lt encodedBound
          · simpa only [sourceValue] using represented.ranges found (buffer.offset + index) absoluteBound
        · simp [Complexity.Language.Heap.read, found, extent, bound] at read
      · simp [Complexity.Language.Heap.read, found, extent] at read

/-- A successful source write is represented by the same single RAM memory
update. Complete objects, scalar ranges and separation all survive; aliases
are not assumed disjoint, and other objects retain their actual contents. -/
theorem write (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (valueFits : cellToNat value < 2 ^ w) :
    HeapRep placement heapLimit finish
      (target.setMem (arrayAddr (bufferRef placement buffer).base index) (cellWord w value)) := by
  obtain ⟨values, found, extent, bound, rfl⟩ := Complexity.Language.Heap.write_eq_ok_iff.mp written
  have absoluteBound : buffer.offset + index < values.size := by omega
  simp only [bufferRef, arrayAddr_add]
  have updatedObjects : ∀ {σ : CellTy} {other : Nat} {otherValues : Array (CellValue σ)},
      (heap.replace buffer.object
        (values.setIfInBounds (buffer.offset + index) value)).object? σ other = some otherValues →
      ∃ originalValues : Array (CellValue σ),
        heap.object? σ other = some originalValues ∧ otherValues.size = originalValues.size ∧
        Source.ArrayAt heapLimit (placement other) (objectWords w otherValues).toList
          (target.setMem (arrayAddr (placement buffer.object) (buffer.offset + index))
            (cellWord w value)) ∧
        ∀ (next : Nat) (nextBound : next < otherValues.size),
          cellToNat otherValues[next] < 2 ^ w := by
    intro σ other otherValues otherFound
    by_cases sameObject : buffer.object = other
    · subst other
      have updatedFound :
          (heap.replace buffer.object
            (values.setIfInBounds (buffer.offset + index) value)).object? τ buffer.object =
            some (values.setIfInBounds (buffer.offset + index) value) :=
        Complexity.Language.Heap.object?_replace_self
          (Complexity.Language.Heap.object_lt_size found)
      have sameStored : (⟨σ, otherValues⟩ : HeapObject) =
          ⟨τ, values.setIfInBounds (buffer.offset + index) value⟩ := by
        apply Option.some.inj
        exact (Complexity.Language.Heap.object?_eq_some_iff.mp otherFound).symm.trans
          (Complexity.Language.Heap.object?_eq_some_iff.mp updatedFound)
      have sameType : σ = τ := congrArg Sigma.fst sameStored
      subst σ
      have sameValues : otherValues = values.setIfInBounds (buffer.offset + index) value :=
        Option.some.inj (otherFound.symm.trans updatedFound)
      subst otherValues
      refine ⟨values, found, by simp only [Array.size_setIfInBounds], ?_, ?_⟩
      · have stored := (represented.objects found).setMem_toArray
          (i := buffer.offset + index)
          (by simpa only [objectWords, Array.size_map] using absoluteBound) (cellWord w value)
        simpa only [objectWords, Array.map_setIfInBounds, Array.map_set, Array.setIfInBounds_def,
          Array.size_map, absoluteBound, ↓reduceDIte] using stored
      · intro next nextBound
        have originalBound : next < values.size := by
          simpa only [Array.size_setIfInBounds] using nextBound
        by_cases sameCell : buffer.offset + index = next
        · subst next
          simpa only [Array.getElem_setIfInBounds_self] using valueFits
        · simpa only [Array.getElem_setIfInBounds_ne originalBound sameCell] using
            represented.ranges found next originalBound
    · have originalFound : heap.object? σ other = some otherValues :=
        (Complexity.Language.Heap.object?_replace_ne sameObject).symm.trans otherFound
      have otherRep := represented.objects originalFound
      have outside : ∀ next : Fin (objectWords w otherValues).toList.length,
          arrayAddr (placement other) next.val ≠
            arrayAddr (placement buffer.object) (buffer.offset + index) := by
        intro next
        exact represented.separated originalFound found (Ne.symm sameObject) next.val
          (by simpa only [Array.length_toList, objectWords, Array.size_map] using next.isLt)
          (buffer.offset + index) absoluteBound
      have preserved := otherRep.indexed.setMem_outside
        (arrayAddr (placement buffer.object) (buffer.offset + index)) (cellWord w value) outside
      refine ⟨otherValues, originalFound, rfl, ?_, represented.ranges originalFound⟩
      exact ⟨ArrayRep.iff_indexed.mpr ⟨otherRep.1.fits, preserved.1⟩, otherRep.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro σ other otherValues otherFound
    obtain ⟨_, _, _, contents, _⟩ := updatedObjects otherFound
    exact contents
  · intro σ other otherValues otherFound
    obtain ⟨_, _, _, _, ranges⟩ := updatedObjects otherFound
    exact ranges
  · intro σ ρ object other objectValues otherValues objectFound otherFound different
      objectIndex objectBound otherIndex otherBound
    obtain ⟨oldObject, oldObjectFound, objectSize, _, _⟩ := updatedObjects objectFound
    obtain ⟨oldOther, oldOtherFound, otherSize, _, _⟩ := updatedObjects otherFound
    exact represented.separated oldObjectFound oldOtherFound different objectIndex
      (by omega) otherIndex (by omega)

end HeapRep

end Ram.LanguageCompiler
