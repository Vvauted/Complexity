/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Shared source objects and borrowed buffers

The heap contains scalar arrays and immutable scalar nodes with typed tail
references. Array accesses reject nodes, so ordinary buffer writes cannot
modify their payloads or links. A buffer is only an
object identifier, offset and length: copying a handle or taking a slice does
not copy its contents. Overlapping views of one object therefore observe the
same writes. Object identifiers are not machine addresses.

Reads and writes check the object's type, the entire view extent and the local
index. Invalid accesses return an explicit error, never a default value or a
successful no-op. Updates use Lean's array operations; their successful-access
conditions establish that the updated slots exist. Slicing checks relative
extent only; validity of the original object is a separate heap predicate.

These are mathematical operations on a shared heap, independent of statement syntax,
an execution relation or a claim about allocation or machine costs.

`Buffer.Contents` observes a valid view as an ordinary `Array.extract` for
mathematical specifications. It is a ghost relation, not an operation that
copies the buffer before execution. Reads and writes still access the current
shared object, and the content rules retain aliasing and unaffected cells.
-/

namespace Complexity.Language

/-- Scalar element types of the initial shared objects. -/
inductive CellTy where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- Object cells use the ordinary Lean scalar types. -/
abbrev CellValue : CellTy → Type
  | .nat => Nat
  | .bool => Bool

/-- The source identity of an immutable node, not a machine address.
The element type alone does not assert that the identifier is present. -/
structure NodeRef (τ : CellTy) where
  object : Nat
  deriving DecidableEq, Repr

/-- Mutable scalar arrays and immutable nodes occupy distinct object kinds.
Node links are typed source identities; scalar array cells remain scalars. -/
inductive HeapObject where
  | buffer (τ : CellTy) (values : Array (CellValue τ))
  | node (τ : CellTy) (head : CellValue τ) (tail : Option (NodeRef τ))

/-- The scalar element type of an object, independently of its storage kind. -/
@[simp] def HeapObject.kind : HeapObject → CellTy
  | .buffer τ _ => τ
  | .node τ _ _ => τ

/-- A borrowed view. Equal or overlapping views need not be distinct handles. -/
structure Buffer (τ : CellTy) where
  object : Nat
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- A finite collection of shared objects; handles index this array. -/
structure Heap where
  objects : Array HeapObject

namespace Heap

/-- Failed object/type lookup, an invalid whole view, or an invalid local index. -/
inductive Error where
  /-- The identifier is absent or its object has a different type or storage kind. -/
  | invalidObject
  | invalidView
  | outOfBounds
  deriving DecidableEq, Repr

private def objectValues? : (τ : CellTy) → HeapObject → Option (Array (CellValue τ))
  | .nat, .buffer .nat values => some values
  | .bool, .buffer .bool values => some values
  | _, _ => none

/-- Look up the current array, checking its element type and rejecting nodes. -/
def object? (heap : Heap) (τ : CellTy) (object : Nat) : Option (Array (CellValue τ)) :=
  heap.objects[object]?.bind (objectValues? τ)

private def nodeValues? : (τ : CellTy) → HeapObject →
    Option (CellValue τ × Option (NodeRef τ))
  | .nat, .node .nat head tail => some (head, tail)
  | .bool, .node .bool head tail => some (head, tail)
  | _, _ => none

/-- Look up an immutable node of the requested element type, rejecting arrays. -/
def node? (heap : Heap) (τ : CellTy) (object : Nat) :
    Option (CellValue τ × Option (NodeRef τ)) :=
  heap.objects[object]?.bind (nodeValues? τ)

/-- Typed lookup is exactly lookup of the corresponding native array object. -/
theorem object?_eq_some_iff {heap : Heap} {τ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} :
    heap.object? τ object = some values ↔
      heap.objects[object]? = some (.buffer τ values) := by
  cases found : heap.objects[object]? with
  | none => simp [object?, found]
  | some stored =>
      cases stored with
      | buffer kind contents =>
          cases kind <;> cases τ <;> simp [object?, objectValues?, found]
      | node kind head tail =>
          cases kind <;> cases τ <;> simp [object?, objectValues?, found]

/-- Typed node lookup exposes exactly the actual stored payload and tail link. -/
theorem node?_eq_some_iff {heap : Heap} {τ : CellTy} {object : Nat}
    {head : CellValue τ} {tail : Option (NodeRef τ)} :
    heap.node? τ object = some (head, tail) ↔
      heap.objects[object]? = some (.node τ head tail) := by
  cases found : heap.objects[object]? with
  | none => simp [node?, found]
  | some stored =>
      cases stored with
      | buffer kind contents =>
          cases kind <;> cases τ <;> simp [node?, nodeValues?, found]
      | node kind storedHead storedTail =>
          cases kind <;> cases τ <;> simp [node?, nodeValues?, found]

/-- A successful array lookup excludes a node at the same identifier. -/
theorem node?_eq_none_of_object {heap : Heap} {τ σ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ object = some values) :
    heap.node? σ object = none := by
  cases τ <;> cases σ <;>
    simp [node?, nodeValues?, object?_eq_some_iff.mp found]

/-- A successful node lookup excludes every scalar-array view of its identifier. -/
theorem object?_eq_none_of_node {heap : Heap} {τ σ : CellTy} {object : Nat}
    {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) :
    heap.object? σ object = none := by
  cases τ <;> cases σ <;>
    simp [object?, objectValues?, node?_eq_some_iff.mp found]

/-- A successful typed lookup denotes an existing object slot. -/
theorem object_lt_size {heap : Heap} {τ : CellTy} {object : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ object = some values) :
    object < heap.objects.size :=
  (Array.getElem?_eq_some_iff.mp (object?_eq_some_iff.mp found)).choose

/-- A successfully observed node names an existing object slot. -/
theorem node_lt_size {heap : Heap} {τ : CellTy} {object : Nat}
    {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) : object < heap.objects.size :=
  (Array.getElem?_eq_some_iff.mp (node?_eq_some_iff.mp found)).choose

/-- Mathematical replacement of an object slot. Operational writes below first
check that this slot exists and preserve its element type and length. -/
def replace (heap : Heap) (object : Nat) {τ : CellTy} (values : Array (CellValue τ)) : Heap :=
  ⟨heap.objects.setIfInBounds object (.buffer τ values)⟩

/-- Replacing an existing object exposes precisely its new native contents. -/
theorem object?_replace_self {heap : Heap} {object : Nat} {τ : CellTy}
    {values : Array (CellValue τ)} (bound : object < heap.objects.size) :
    (heap.replace object values).object? τ object = some values := by
  apply object?_eq_some_iff.mpr
  exact Array.getElem?_setIfInBounds_self_of_lt bound

/-- Other object slots retain their contents, also when their types differ. -/
theorem object?_replace_ne {heap : Heap} {object other : Nat} {τ σ : CellTy}
    {values : Array (CellValue τ)} (different : object ≠ other) :
    (heap.replace object values).object? σ other = heap.object? σ other := by
  simp only [object?, replace, Array.getElem?_setIfInBounds_ne different]

/-- Array replacement leaves every different node lookup unchanged. -/
theorem node?_replace_ne {heap : Heap} {object other : Nat} {τ σ : CellTy}
    {values : Array (CellValue τ)} (different : object ≠ other) :
    (heap.replace object values).node? σ other = heap.node? σ other := by
  simp only [node?, replace, Array.getElem?_setIfInBounds_ne different]

end Heap

namespace Buffer

/-- A valid view denotes the advertised type and lies entirely within its object. -/
def Valid {τ : CellTy} (buffer : Buffer τ) (heap : Heap) : Prop :=
  ∃ values, heap.object? τ buffer.object = some values ∧
    buffer.offset + buffer.length ≤ values.size

/-- Form a view of a view without accessing or copying the object. The original
view's object/type validity is supplied separately by `Valid`. -/
def slice {τ : CellTy} (buffer : Buffer τ) (offset length : Nat) :
    Except Heap.Error (Buffer τ) :=
  if offset + length ≤ buffer.length then
    .ok ⟨buffer.object, buffer.offset + offset, length⟩
  else .error .outOfBounds

/-- A fitting slice retains the same object and adds only its relative offset. -/
theorem slice_eq {τ : CellTy} (buffer : Buffer τ) {offset length : Nat}
    (bound : offset + length ≤ buffer.length) :
    buffer.slice offset length = .ok ⟨buffer.object, buffer.offset + offset, length⟩ := by
  simp [slice, bound]

/-- The full relative slice is the original borrowed view, including an empty view. -/
@[simp] theorem slice_self {τ : CellTy} (buffer : Buffer τ) :
    buffer.slice 0 buffer.length = .ok buffer := by
  simpa only [Nat.add_zero] using buffer.slice_eq (offset := 0) (length := buffer.length)
    (by omega)

/-- Relative slicing preserves validity of an already valid view. -/
theorem Valid.slice {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    (valid : buffer.Valid heap) {offset length : Nat}
    (bound : offset + length ≤ buffer.length) :
    (⟨buffer.object, buffer.offset + offset, length⟩ : Buffer τ).Valid heap := by
  obtain ⟨values, found, extent⟩ := valid
  exact ⟨values, found, by dsimp; omega⟩

end Buffer

namespace Heap

/-- Read the current shared cell after checking object, view and index validity. -/
def read (heap : Heap) {τ : CellTy} (buffer : Buffer τ) (index : Nat) :
    Except Error (CellValue τ) :=
  match heap.object? τ buffer.object with
  | none => .error .invalidObject
  | some values =>
      if extent : buffer.offset + buffer.length ≤ values.size then
        if bound : index < buffer.length then
          .ok (getElem values (buffer.offset + index) (by omega))
        else .error .outOfBounds
      else .error .invalidView

/-- Update one current shared cell. Both native array updates target existing
slots because the object lookup, whole view and local index were checked. -/
def write (heap : Heap) {τ : CellTy} (buffer : Buffer τ) (index : Nat)
    (value : CellValue τ) : Except Error Heap :=
  match heap.object? τ buffer.object with
  | none => .error .invalidObject
  | some values =>
      if buffer.offset + buffer.length ≤ values.size then
        if index < buffer.length then
          .ok (heap.replace buffer.object
            (values.setIfInBounds (buffer.offset + index) value))
        else .error .outOfBounds
      else .error .invalidView

/-- A valid read is ordinary native array indexing at the view's absolute index. -/
theorem read_eq {heap : Heap} {τ : CellTy} {buffer : Buffer τ} {index : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ buffer.object = some values)
    (extent : buffer.offset + buffer.length ≤ values.size) (bound : index < buffer.length) :
    heap.read buffer index = .ok (getElem values (buffer.offset + index) (by omega)) := by
  simp [read, found, extent, bound]

/-- Successful writes give the native contents, actual validity conditions and
the precise updated heap. This rules out a successful out-of-bounds no-op. -/
theorem write_eq_ok_iff {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ} :
    heap.write buffer index value = .ok finish ↔
      ∃ values, heap.object? τ buffer.object = some values ∧
        buffer.offset + buffer.length ≤ values.size ∧ index < buffer.length ∧
        finish = heap.replace buffer.object
          (values.setIfInBounds (buffer.offset + index) value) := by
  cases found : heap.object? τ buffer.object with
  | none => simp [write, found]
  | some values =>
      by_cases extent : buffer.offset + buffer.length ≤ values.size
      · by_cases bound : index < buffer.length <;> simp [write, found, extent, bound, eq_comm]
      · simp [write, found, extent]

/-- A successful source write uses actual native `Array.set` at both levels. -/
theorem write_eq_set {heap : Heap} {τ : CellTy} {buffer : Buffer τ} {index : Nat}
    {values : Array (CellValue τ)} (found : heap.object? τ buffer.object = some values)
    (extent : buffer.offset + buffer.length ≤ values.size) (bound : index < buffer.length)
    (value : CellValue τ) :
    heap.write buffer index value = .ok
      ⟨heap.objects.set buffer.object
        (.buffer τ (values.set (buffer.offset + index) value (by omega)))
        (object_lt_size found)⟩ := by
  simp [write, found, extent, bound, replace, Array.setIfInBounds_def,
    object_lt_size found, show buffer.offset + index < values.size by omega]

/-- A write preserves the complete contents of every different object. No
condition is imposed on distinct handles for the object that was written. -/
theorem object?_write_of_ne {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {index other : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (different : buffer.object ≠ other) :
    finish.object? σ other = heap.object? σ other := by
  obtain ⟨values, _, _, _, rfl⟩ := write_eq_ok_iff.mp written
  exact object?_replace_ne different

/-- A successful scalar write preserves every node lookup, including absence
and type mismatches. Its checked array tag rules out overwriting a node. -/
theorem node?_write {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {index object : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    finish.node? σ object = heap.node? σ object := by
  obtain ⟨values, found, _, _, rfl⟩ := write_eq_ok_iff.mp written
  by_cases same : buffer.object = object
  · subst object
    exact (node?_eq_none_of_object (σ := σ)
      (object?_replace_self (heap := heap)
        (values := values.setIfInBounds (buffer.offset + index) value)
        (object_lt_size found))).trans
        (node?_eq_none_of_object found).symm
  · exact node?_replace_ne same

/-- The payload and tail of an existing immutable node survive every scalar write. -/
theorem node?_write_of_some {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {index object : Nat} {value : CellValue τ} {head : CellValue σ}
    {tail : Option (NodeRef σ)} (written : heap.write buffer index value = .ok finish)
    (found : heap.node? σ object = some (head, tail)) :
    finish.node? σ object = some (head, tail) :=
  (node?_write written).trans found

/-- Reads from another object are unchanged, including their error outcomes. -/
theorem read_write_of_ne {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {other : Buffer σ} {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (different : buffer.object ≠ other.object) :
    finish.read other otherIndex = heap.read other otherIndex := by
  simp only [read, object?_write_of_ne (σ := σ) written different]

/-- A read of another cell in the same object is unchanged, including its error
outcome. Views may overlap; only the two absolute cell indices must differ. -/
theorem read_write_of_ne_cell {heap finish : Heap} {τ : CellTy}
    {buffer other : Buffer τ} {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (sameObject : buffer.object = other.object)
    (differentCell : buffer.offset + index ≠ other.offset + otherIndex) :
    finish.read other otherIndex = heap.read other otherIndex := by
  obtain ⟨values, found, _, _, rfl⟩ := write_eq_ok_iff.mp written
  have original : heap.object? τ other.object = some values := by
    simpa only [← sameObject] using found
  have updated :
      (heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)).object?
        τ other.object = some (values.setIfInBounds (buffer.offset + index) value) := by
    rw [← sameObject]
    exact object?_replace_self (object_lt_size found)
  by_cases extent : other.offset + other.length ≤ values.size
  · by_cases bound : otherIndex < other.length
    · rw [read_eq updated (by simpa using extent) bound, read_eq original extent bound]
      exact congrArg Except.ok (Array.getElem_setIfInBounds_ne
        (xs := values) (i := buffer.offset + index) (a := value)
        (j := other.offset + otherIndex) (by omega) differentCell)
    · simp [read, updated, original, extent, bound]
  · simp [read, updated, original, extent]

/-- Any valid alias of the written cell observes its new value. Views may be
equal, differently sized or overlapping; equality is on object and cell identity. -/
theorem read_write_alias {heap finish : Heap} {τ : CellTy} {buffer other : Buffer τ}
    {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (valid : other.Valid heap) (sameObject : buffer.object = other.object)
    (bound : otherIndex < other.length)
    (sameCell : buffer.offset + index = other.offset + otherIndex) :
    finish.read other otherIndex = .ok value := by
  obtain ⟨values, found, extent, indexBound, rfl⟩ := write_eq_ok_iff.mp written
  obtain ⟨otherValues, otherFound, otherExtent⟩ := valid
  rw [← sameObject, found] at otherFound
  have sameValues : otherValues = values := (Option.some.inj otherFound).symm
  subst otherValues
  have updated :
      (heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)).object?
        τ other.object = some (values.setIfInBounds (buffer.offset + index) value) := by
    rw [← sameObject]
    exact object?_replace_self (object_lt_size found)
  rw [read_eq updated (by simpa using otherExtent) bound]
  apply congrArg Except.ok
  have cellBound : buffer.offset + index < values.size := by omega
  simpa only [← sameCell] using
    (Array.getElem_setIfInBounds_self
      (xs := values) (i := buffer.offset + index) (a := value) (by simpa using cellBound))

/-- Reading through the written handle itself returns the actual stored value. -/
theorem read_write {heap finish : Heap} {τ : CellTy} {buffer : Buffer τ}
    {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    finish.read buffer index = .ok value := by
  obtain ⟨values, found, extent, bound, _⟩ := write_eq_ok_iff.mp written
  exact read_write_alias written ⟨values, found, extent⟩ rfl bound rfl

end Heap

namespace Buffer

/-- A successful write preserves every valid view's object, type and extent.
The views may be equal or overlap; no separation of their handles is required. -/
theorem Valid.write {heap finish : Heap} {τ σ : CellTy} {buffer : Buffer τ}
    {other : Buffer σ} {index : Nat} {value : CellValue τ}
    (valid : other.Valid heap) (written : heap.write buffer index value = .ok finish) :
    other.Valid finish := by
  obtain ⟨values, found, _, _, rfl⟩ := Heap.write_eq_ok_iff.mp written
  obtain ⟨otherValues, otherFound, otherExtent⟩ := valid
  by_cases sameObject : buffer.object = other.object
  · have sameStored : HeapObject.buffer τ values = .buffer σ otherValues := by
      apply Option.some.inj
      exact (Heap.object?_eq_some_iff.mp found).symm.trans
        (by simpa only [← sameObject] using Heap.object?_eq_some_iff.mp otherFound)
    have sameType : τ = σ := congrArg HeapObject.kind sameStored
    subst σ
    have sameValues : otherValues = values := by
      rw [← sameObject, found] at otherFound
      exact (Option.some.inj otherFound).symm
    subst otherValues
    refine ⟨values.setIfInBounds (buffer.offset + index) value, ?_, ?_⟩
    · rw [← sameObject]
      exact Heap.object?_replace_self (Heap.object_lt_size found)
    · simpa using otherExtent
  · exact ⟨otherValues, (Heap.object?_replace_ne sameObject).trans otherFound, otherExtent⟩

/-- The ordinary mathematical contents of a valid borrowed view. This relation
observes the current heap; it does not introduce a runtime snapshot or copy. -/
def Contents {τ : CellTy} (buffer : Buffer τ) (heap : Heap)
    (contents : Array (CellValue τ)) : Prop :=
  ∃ values, heap.object? τ buffer.object = some values ∧
    buffer.offset + buffer.length ≤ values.size ∧
    contents = values.extract buffer.offset (buffer.offset + buffer.length)

/-- Observing contents includes validity of the complete view. -/
theorem Contents.valid {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents) :
    buffer.Valid heap := by
  obtain ⟨values, found, extent, _⟩ := observed
  exact ⟨values, found, extent⟩

/-- Every valid view has mathematical contents in the native array type. -/
theorem Valid.contents {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    (valid : buffer.Valid heap) : ∃ contents, buffer.Contents heap contents := by
  obtain ⟨values, found, extent⟩ := valid
  exact ⟨_, values, found, extent, rfl⟩

/-- A valid view's mathematical contents have exactly its advertised length. -/
theorem Contents.size_eq {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents) :
    contents.size = buffer.length := by
  obtain ⟨values, _, extent, rfl⟩ := observed
  simp only [Array.size_extract, Nat.min_eq_left extent, Nat.add_sub_cancel_left]

/-- The same view and heap determine a unique ordinary array. -/
theorem Contents.unique {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents other : Array (CellValue τ)} (observed : buffer.Contents heap contents)
    (observedOther : buffer.Contents heap other) : contents = other := by
  obtain ⟨values, found, _, rfl⟩ := observed
  obtain ⟨otherValues, otherFound, _, rfl⟩ := observedOther
  have same : values = otherValues := Option.some.inj (found.symm.trans otherFound)
  rw [same]

/-- Reading a valid mathematical index returns its ordinary array element. -/
theorem Contents.read {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents)
    {index : Nat} (bound : index < contents.size) :
    heap.read buffer index = .ok contents[index] := by
  obtain ⟨values, found, extent, rfl⟩ := observed
  have localBound : index < buffer.length := by
    simpa only [Array.size_extract, Nat.min_eq_left extent, Nat.add_sub_cancel_left] using bound
  rw [Heap.read_eq found extent localBound]
  simp only [Array.getElem_extract]

/-- Native array extensionality establishes contents from the actual reads of
a valid view. No independently supplied evaluator or snapshot is involved. -/
theorem Contents.of_read {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents : Array (CellValue τ)} (valid : buffer.Valid heap)
    (size : contents.size = buffer.length)
    (reads : ∀ index (bound : index < contents.size),
      heap.read buffer index = .ok contents[index]) :
    buffer.Contents heap contents := by
  obtain ⟨actual, observed⟩ := valid.contents
  have same : contents = actual := by
    apply Array.ext (size.trans observed.size_eq.symm)
    intro index bound actualBound
    exact Except.ok.inj ((reads index bound).symm.trans (observed.read actualBound))
  exact same.symm ▸ observed

/-- A successful write supplies the index proof needed by native `Array.set`. -/
theorem Contents.index_lt_size_of_write {τ : CellTy} {buffer : Buffer τ}
    {heap finish : Heap} {contents : Array (CellValue τ)}
    (observed : buffer.Contents heap contents) {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) : index < contents.size := by
  obtain ⟨_, _, _, bound, _⟩ := Heap.write_eq_ok_iff.mp written
  simpa only [observed.size_eq] using bound

/-- A write falling inside another valid view updates that view at the matching
relative index. The views may coincide, overlap or have different extents. -/
theorem Contents.write_alias {τ : CellTy} {buffer other : Buffer τ}
    {heap finish : Heap} {contents : Array (CellValue τ)}
    (observed : other.Contents heap contents) {index otherIndex : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (sameObject : buffer.object = other.object) (bound : otherIndex < contents.size)
    (sameCell : buffer.offset + index = other.offset + otherIndex) :
    other.Contents finish (contents.set otherIndex value bound) := by
  apply Contents.of_read (observed.valid.write written)
    (by simpa only [Array.size_set] using observed.size_eq)
  intro next nextBound
  have originalBound : next < contents.size := by
    simpa only [Array.size_set] using nextBound
  by_cases sameIndex : otherIndex = next
  · subst next
    rw [Heap.read_write_alias written observed.valid sameObject
      (by simpa only [observed.size_eq] using bound) sameCell]
    simp only [Array.getElem_set_self]
  · have differentCell : buffer.offset + index ≠ other.offset + next := by omega
    rw [Heap.read_write_of_ne_cell written sameObject differentCell,
      observed.read originalBound]
    simp only [Array.getElem_set_ne bound originalBound sameIndex]

/-- Writing through a view updates its ordinary array with native `Array.set`.
The successful write supplies the index bound; it is not required again. -/
theorem Contents.write {τ : CellTy} {buffer : Buffer τ} {heap finish : Heap}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents)
    {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    buffer.Contents finish
      (contents.set index value (observed.index_lt_size_of_write written)) :=
  observed.write_alias written rfl (observed.index_lt_size_of_write written) rfl

/-- A valid mathematical index admits an actual heap write with the specified
native array update. Callers need not construct or unfold the object storage. -/
theorem Contents.write_exists {τ : CellTy} {buffer : Buffer τ} {heap : Heap}
    {contents : Array (CellValue τ)} (observed : buffer.Contents heap contents)
    {index : Nat} (bound : index < contents.size) (value : CellValue τ) :
    ∃ finish, heap.write buffer index value = .ok finish ∧
      buffer.Contents finish (contents.set index value bound) := by
  obtain ⟨values, found, extent⟩ := observed.valid
  have localBound : index < buffer.length := by simpa only [observed.size_eq] using bound
  let finish := heap.replace buffer.object (values.setIfInBounds (buffer.offset + index) value)
  have written : heap.write buffer index value = .ok finish :=
    Heap.write_eq_ok_iff.mpr ⟨values, found, extent, localBound, rfl⟩
  exact ⟨finish, written, observed.write written⟩

/-- A write to a different object preserves this view's entire contents,
including when the two objects have different element types. -/
theorem Contents.write_of_ne {τ σ : CellTy} {buffer : Buffer τ} {other : Buffer σ}
    {heap finish : Heap} {contents : Array (CellValue σ)}
    (observed : other.Contents heap contents) {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (different : buffer.object ≠ other.object) : other.Contents finish contents := by
  obtain ⟨values, found, extent, same⟩ := observed
  exact ⟨values, (Heap.object?_write_of_ne written different).trans found, extent, same⟩

/-- A write outside this view's interval leaves its entire mathematical contents
unchanged, even when it updates the same shared object. -/
theorem Contents.write_of_outside {τ : CellTy} {buffer other : Buffer τ}
    {heap finish : Heap} {contents : Array (CellValue τ)}
    (observed : other.Contents heap contents) {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (outside : buffer.offset + index < other.offset ∨
      other.offset + other.length ≤ buffer.offset + index) :
    other.Contents finish contents := by
  by_cases sameObject : buffer.object = other.object
  · apply Contents.of_read (observed.valid.write written) observed.size_eq
    intro next bound
    have localBound : next < other.length := by simpa only [observed.size_eq] using bound
    have differentCell : buffer.offset + index ≠ other.offset + next := by omega
    rw [Heap.read_write_of_ne_cell written sameObject differentCell]
    exact observed.read bound
  · exact observed.write_of_ne written sameObject

/-- Two borrowed views share no physical cell. Their objects may coincide;
empty views are disjoint through the ordinary empty-interval rules. -/
def Disjoint {τ σ : CellTy} (buffer : Buffer τ) (other : Buffer σ) : Prop :=
  buffer.object ≠ other.object ∨
    _root_.Disjoint (Set.Ico buffer.offset (buffer.offset + buffer.length))
      (Set.Ico other.offset (other.offset + other.length))

/-- Disjoint borrowed views protect each other, including slices of one object. -/
theorem Disjoint.symm {τ σ : CellTy} {buffer : Buffer τ} {other : Buffer σ}
    (separated : buffer.Disjoint other) : other.Disjoint buffer := by
  rcases separated with different | intervals
  · exact Or.inl (Ne.symm different)
  · exact Or.inr intervals.symm

/-- A successful write preserves the contents of any disjoint view, including
another slice of the same object. Object tags, not an assumption about handles,
resolve the element types when the objects coincide. -/
theorem Contents.write_of_disjoint {τ σ : CellTy} {buffer : Buffer τ} {other : Buffer σ}
    {heap finish : Heap} {contents : Array (CellValue σ)}
    (observed : other.Contents heap contents) {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (separated : buffer.Disjoint other) : other.Contents finish contents := by
  by_cases sameObject : buffer.object = other.object
  · have intervals := separated.resolve_left (fun different => different sameObject)
    obtain ⟨values, found, _, bound, _⟩ := Heap.write_eq_ok_iff.mp written
    obtain ⟨otherValues, otherFound, _⟩ := observed.valid
    have sameStored : HeapObject.buffer τ values = .buffer σ otherValues := by
      apply Option.some.inj
      exact (Heap.object?_eq_some_iff.mp found).symm.trans
        (by simpa only [← sameObject] using Heap.object?_eq_some_iff.mp otherFound)
    have sameType : τ = σ := congrArg HeapObject.kind sameStored
    subst σ
    have writtenCell : buffer.offset + index ∈
        Set.Ico buffer.offset (buffer.offset + buffer.length) := ⟨by omega, by omega⟩
    have outside := Set.disjoint_left.mp intervals writtenCell
    change ¬(other.offset ≤ buffer.offset + index ∧
      buffer.offset + index < other.offset + other.length) at outside
    exact observed.write_of_outside written (by omega)
  · exact observed.write_of_ne written sameObject

/-- Every initially observed view outside the permitted region retains its
ordinary contents in the final heap. This is a relation on actual heaps, not
ownership of handles or a restriction on aliases inside the region. -/
def PreservesOutside {τ : CellTy} (buffer : Buffer τ) (initial finish : Heap) : Prop :=
  ∀ {σ : CellTy} (other : Buffer σ) (contents : Array (CellValue σ)),
    buffer.Disjoint other → other.Contents initial contents → other.Contents finish contents

/-- Transport an observed array through a frame for a disjoint borrowed view.
Both heaps are the actual endpoints of the supplied frame. -/
theorem PreservesOutside.contents {τ σ : CellTy} {buffer : Buffer τ} {other : Buffer σ}
    {initial finish : Heap} {values : Array (CellValue σ)}
    (preserved : buffer.PreservesOutside initial finish)
    (separated : buffer.Disjoint other) (observed : other.Contents initial values) :
    other.Contents finish values :=
  preserved other values separated observed

/-- An unchanged heap preserves every outside observation. -/
theorem PreservesOutside.refl {τ : CellTy} (buffer : Buffer τ) (heap : Heap) :
    buffer.PreservesOutside heap heap := by
  intro σ other contents separated observed
  exact observed

/-- Preservation composes through the actual intermediate shared heap. -/
theorem PreservesOutside.trans {τ : CellTy} {buffer : Buffer τ}
    {initial middle finish : Heap}
    (first : buffer.PreservesOutside initial middle)
    (second : buffer.PreservesOutside middle finish) :
    buffer.PreservesOutside initial finish := by
  intro σ other contents separated observed
  exact second other contents separated (first other contents separated observed)

/-- A successful write changes no observation outside its borrowed view. -/
theorem PreservesOutside.write {τ : CellTy} {buffer : Buffer τ}
    {heap finish : Heap} {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish) :
    buffer.PreservesOutside heap finish := by
  intro σ other contents separated observed
  exact observed.write_of_disjoint written separated

/-- A frame for a smaller interval also permits changes within a containing
interval of the same object. The inclusion is ordinary mathlib set inclusion. -/
theorem PreservesOutside.mono {τ σ : CellTy} {buffer : Buffer τ} {larger : Buffer σ}
    {initial finish : Heap} (preserved : buffer.PreservesOutside initial finish)
    (sameObject : buffer.object = larger.object)
    (included : Set.Ico buffer.offset (buffer.offset + buffer.length) ⊆
      Set.Ico larger.offset (larger.offset + larger.length)) :
    larger.PreservesOutside initial finish := by
  intro κ other contents separated observed
  refine preserved other contents ?_ observed
  rcases separated with different | intervals
  · exact Or.inl (fun same => different (sameObject.symm.trans same))
  · exact Or.inr (intervals.mono_left included)

end Buffer

end Complexity.Language
