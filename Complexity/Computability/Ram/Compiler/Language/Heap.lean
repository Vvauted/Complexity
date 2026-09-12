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
The complete current object is represented at that address: arrays contain
their scalar cells, while immutable nodes contain a head, an option tag and
the actual placement of their tail. Borrowed array views derive their base and
length without copying contents or storing an object table. Views of the same
object may overlap or coincide. Distinct objects have disjoint actual cells,
with no condition on empty objects' unused addresses.

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

/-- Complete storage of either object kind. The optional link contains an
actual address, not a numeric source identifier; `none` uses a separate zero tag. -/
def heapObjectWords (placement : Nat → Word w) : HeapObject → Array (Word w)
  | .buffer _ values => objectWords w values
  | .node _ head none => #[cellWord w head, 0, 0]
  | .node _ head (some tail) => #[cellWord w head, 1, placement tail.object]

/-- Exact scalar payloads and node tags. Link addresses already have type `Word`. -/
def heapObjectFits (w : Nat) : HeapObject → Prop
  | .buffer _ values => ∀ (index : Nat) (bound : index < values.size),
      cellToNat values[index] < 2 ^ w
  | .node _ head _ => cellToNat head < 2 ^ w ∧ 1 < 2 ^ w

@[simp] theorem heapObjectWords_buffer (placement : Nat → Word w) {τ : CellTy}
    (values : Array (CellValue τ)) :
    heapObjectWords placement (.buffer τ values) = objectWords w values := rfl

@[simp] theorem heapObjectWords_buffer_size (placement : Nat → Word w) {τ : CellTy}
    (values : Array (CellValue τ)) :
    (heapObjectWords placement (.buffer τ values)).size = values.size := by
  simp only [heapObjectWords, objectWords, Array.size_map]

@[simp] theorem heapObjectWords_node_size (placement : Nat → Word w) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heapObjectWords placement (.node τ head tail)).size = 3 := by
  cases tail <;> rfl

/-- Storage extent depends on the object, not its placement or referenced addresses. -/
theorem heapObjectWords_size_eq (left right : Nat → Word w) (object : HeapObject) :
    (heapObjectWords left object).size = (heapObjectWords right object).size := by
  cases object with
  | buffer τ values => rfl
  | node τ head tail => simp only [heapObjectWords_node_size]

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
  /-- Every actual object occupies its complete encoded interval. -/
  stored : ∀ {id : Nat} {object : HeapObject}, heap.objects[id]? = some object →
    Source.ArrayAt heapLimit (placement id) (heapObjectWords placement object).toList target
  /-- Every payload and tag has its exact value at the selected width. -/
  fit : ∀ {id : Nat} {object : HeapObject}, heap.objects[id]? = some object →
    heapObjectFits w object
  /-- Every pair of distinct objects has disjoint storage, regardless of kind. -/
  disjoint : ∀ {id other : Nat} {object otherObject : HeapObject},
    heap.objects[id]? = some object → heap.objects[other]? = some otherObject →
      id ≠ other → ∀ (index : Nat), index < (heapObjectWords placement object).size →
        ∀ (otherIndex : Nat), otherIndex < (heapObjectWords placement otherObject).size →
          arrayAddr (placement id) index ≠ arrayAddr (placement other) otherIndex
  /-- A live node's actual link points into its earlier object prefix. -/
  backward : ∀ {τ : CellTy} {id : Nat} {head : CellValue τ} {tail : NodeRef τ},
    heap.node? τ id = some (head, some tail) → tail.object < id

namespace HeapRep

variable {w heapLimit : Nat} {placement : Nat → Word w}
variable {heap finish : Complexity.Language.Heap} {target : Source.State w}

/-- Typed array observation is a projection of complete object representation. -/
theorem objects (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) :
    Source.ArrayAt heapLimit (placement object) (objectWords w values).toList target :=
  represented.stored (Complexity.Language.Heap.object?_eq_some_iff.mp found)

/-- Every represented array cell retains the original exact scalar range interface. -/
theorem ranges (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {values : Array (CellValue τ)}
    (found : heap.object? τ object = some values) :
    ∀ (index : Nat) (bound : index < values.size), cellToNat values[index] < 2 ^ w :=
  represented.fit (Complexity.Language.Heap.object?_eq_some_iff.mp found)

/-- The original array separation interface follows from separation of all objects. -/
theorem separated (represented : HeapRep placement heapLimit heap target)
    {τ σ : CellTy} {object other : Nat}
    {values : Array (CellValue τ)} {otherValues : Array (CellValue σ)}
    (found : heap.object? τ object = some values)
    (otherFound : heap.object? σ other = some otherValues) (different : object ≠ other)
    (index : Nat) (bound : index < values.size)
    (otherIndex : Nat) (otherBound : otherIndex < otherValues.size) :
    arrayAddr (placement object) index ≠ arrayAddr (placement other) otherIndex :=
  represented.disjoint (Complexity.Language.Heap.object?_eq_some_iff.mp found)
    (Complexity.Language.Heap.object?_eq_some_iff.mp otherFound) different index
    (by simpa only [heapObjectWords_buffer_size] using bound) otherIndex
    (by simpa only [heapObjectWords_buffer_size] using otherBound)

/-- A node lookup exposes all three real words, including its placed optional tail. -/
theorem nodes (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) :
    Source.ArrayAt heapLimit (placement object)
      (heapObjectWords placement (.node τ head tail)).toList target :=
  represented.stored (Complexity.Language.Heap.node?_eq_some_iff.mp found)

/-- A stored backward link always names an existing object, without requiring
the numeric source identifier to fit a RAM word. -/
theorem tail_lt_size (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {head : CellValue τ} {tail : NodeRef τ}
    (found : heap.node? τ object = some (head, some tail)) :
    tail.object < heap.objects.size :=
  Nat.lt_trans (represented.backward found) (Complexity.Language.Heap.node_lt_size found)

/-- The empty source heap imposes no restriction on placement, capacity or RAM memory. -/
theorem empty (placement : Nat → Word w) (heapLimit : Nat) (target : Source.State w) :
    HeapRep placement heapLimit ⟨#[]⟩ target := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id object found
    simp at found
  · intro id object found
    simp at found
  · intro id other object otherObject found
    simp at found
  · intro τ object head tail found
    exact (Nat.not_lt_zero object (Complexity.Language.Heap.node_lt_size found)).elim

/-- Parameter binding retains the same complete shared-heap representation. -/
theorem enter (represented : HeapRep placement heapLimit heap target)
    (args : List (Word w)) : HeapRep placement heapLimit heap (target.enter args) := by
  refine ⟨?_, represented.fit, represented.disjoint, represented.backward⟩
  intro id object found
  exact (represented.stored found).enter args

/-- Receiving actual return fields changes no represented heap cell. -/
theorem setRegs (represented : HeapRep placement heapLimit heap target)
    (dsts : List Reg) (values : List (Word w)) :
    HeapRep placement heapLimit heap (target.setRegs dsts values) := by
  refine ⟨?_, represented.fit, represented.disjoint, represented.backward⟩
  intro id object found
  simpa only [Source.ArrayAt, Source.State.setRegs_mem] using represented.stored found

/-- Updating one local register changes no represented shared object. -/
theorem setReg (represented : HeapRep placement heapLimit heap target)
    (dst : Reg) (value : Word w) :
    HeapRep placement heapLimit heap (target.setReg dst value) := by
  simpa only [Source.State.setRegs_singleton] using represented.setRegs [dst] [value]

/-- Caller restoration keeps the callee's final heap, not the caller's old heap. -/
theorem restore (represented : HeapRep placement heapLimit heap target)
    (caller : Source.State w) : HeapRep placement heapLimit heap (caller.restore target) := by
  refine ⟨?_, represented.fit, represented.disjoint, represented.backward⟩
  intro id object found
  simpa only [Source.ArrayAt, Source.State.restore_mem] using represented.stored found

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
  have rawFound := Complexity.Language.Heap.object?_eq_some_iff.mp found
  simp only [bufferRef, arrayAddr_add]
  have updatedStored : ∀ {other : Nat} {object : HeapObject},
      (heap.replace buffer.object
        (values.setIfInBounds (buffer.offset + index) value)).objects[other]? = some object →
      ∃ original : HeapObject,
        heap.objects[other]? = some original ∧
        (heapObjectWords placement object).size = (heapObjectWords placement original).size ∧
        Source.ArrayAt heapLimit (placement other) (heapObjectWords placement object).toList
          (target.setMem (arrayAddr (placement buffer.object) (buffer.offset + index))
            (cellWord w value)) ∧
        heapObjectFits w object := by
    intro other object otherFound
    by_cases sameObject : buffer.object = other
    · subst other
      have updatedFound :
          (heap.replace buffer.object
            (values.setIfInBounds (buffer.offset + index) value)).objects[buffer.object]? =
            some (.buffer τ (values.setIfInBounds (buffer.offset + index) value)) :=
        Array.getElem?_setIfInBounds_self_of_lt
          (Complexity.Language.Heap.object_lt_size found)
      have sameStored : object =
          .buffer τ (values.setIfInBounds (buffer.offset + index) value) :=
        Option.some.inj (otherFound.symm.trans updatedFound)
      subst object
      refine ⟨.buffer τ values, rawFound, by
        simp only [heapObjectWords_buffer_size, Array.size_setIfInBounds], ?_, ?_⟩
      · have stored := (represented.objects found).setMem_toArray
          (i := buffer.offset + index)
          (by simpa only [objectWords, Array.size_map] using absoluteBound) (cellWord w value)
        simpa only [heapObjectWords_buffer, objectWords,
          Array.map_setIfInBounds, Array.map_set, Array.setIfInBounds_def,
          Array.size_map, absoluteBound, ↓reduceDIte] using stored
      · intro next nextBound
        have originalBound : next < values.size := by
          simpa only [Array.size_setIfInBounds] using nextBound
        by_cases sameCell : buffer.offset + index = next
        · subst next
          simpa only [Array.getElem_setIfInBounds_self] using valueFits
        · simpa only [Array.getElem_setIfInBounds_ne originalBound sameCell] using
            represented.ranges found next originalBound
    · have originalFound : heap.objects[other]? = some object := by
        simpa only [Complexity.Language.Heap.replace,
          Array.getElem?_setIfInBounds_ne sameObject] using otherFound
      have otherRep := represented.stored originalFound
      have outside : ∀ next : Fin (heapObjectWords placement object).toList.length,
          arrayAddr (placement other) next.val ≠
            arrayAddr (placement buffer.object) (buffer.offset + index) := by
        intro next
        exact represented.disjoint originalFound rawFound (Ne.symm sameObject) next.val
          (by simpa only [Array.length_toList] using next.isLt)
          (buffer.offset + index)
          (by simpa only [heapObjectWords_buffer_size] using absoluteBound)
      have preserved := otherRep.indexed.setMem_outside
        (arrayAddr (placement buffer.object) (buffer.offset + index)) (cellWord w value) outside
      refine ⟨object, originalFound, rfl, ?_, represented.fit originalFound⟩
      exact ⟨ArrayRep.iff_indexed.mpr ⟨otherRep.1.fits, preserved.1⟩, otherRep.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other object otherFound
    obtain ⟨_, _, _, contents, _⟩ := updatedStored otherFound
    exact contents
  · intro other object otherFound
    obtain ⟨_, _, _, _, fits⟩ := updatedStored otherFound
    exact fits
  · intro object other objectValues otherValues objectFound otherFound different
      objectIndex objectBound otherIndex otherBound
    obtain ⟨oldObject, oldObjectFound, objectSize, _, _⟩ := updatedStored objectFound
    obtain ⟨oldOther, oldOtherFound, otherSize, _, _⟩ := updatedStored otherFound
    exact represented.disjoint oldObjectFound oldOtherFound different objectIndex
      (by omega) otherIndex (by omega)
  · intro σ object head tail nodeFound
    exact represented.backward
      ((Complexity.Language.Heap.node?_write written).symm.trans nodeFound)

end HeapRep

end Ram.LanguageCompiler
