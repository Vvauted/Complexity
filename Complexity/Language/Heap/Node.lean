/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Backward

/-!
# Immutable nodes and shared linked-list contents

A node allocation appends one actual object containing a scalar head and a typed
optional tail reference. Uncons observes that same stored object and rejects an
absent reference, an array object or a different scalar type. Neither operation
traverses or copies the tail. Source object identifiers are not machine addresses.

The inductive contents relation describes a finite, correctly typed chain as an
ordinary Lean list. Different roots may share any suffix. Successful buffer writes
and allocations retain every old node, so they preserve all old list observations
without a separation premise. Backward links additionally let a retained root keep
its whole chain during prefix reclamation.

These are source heap operations and mathematical contracts, not new source
statements, an unchecked RAM primitive or an instruction-cost claim. The bare
allocator accepts a reference value; its list and lifecycle theorems require an
actual valid tail rather than treating an arbitrary identifier as a list.
-/

namespace Complexity.Language

namespace Heap

/-- Append one immutable node, retaining its existing tail by reference. -/
def cons (heap : Heap) {τ : CellTy} (head : CellValue τ) (tail : Option (NodeRef τ)) :
    NodeRef τ × Heap :=
  (⟨heap.objects.size⟩, ⟨heap.objects.push (.node τ head tail)⟩)

@[simp] theorem cons_object (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heap.cons head tail).1.object = heap.objects.size := rfl

@[simp] theorem cons_objects (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heap.cons head tail).2.objects = heap.objects.push (.node τ head tail) := rfl

/-- Exactly one object is appended, independently of the shared tail's length. -/
@[simp] theorem cons_size (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heap.cons head tail).2.objects.size = heap.objects.size + 1 := by
  simp only [cons_objects, Array.size_push]

/-- Every slot other than the fresh node retains its exact stored object. -/
theorem getElem?_cons_of_ne (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) {object : Nat}
    (different : object ≠ heap.objects.size) :
    (heap.cons head tail).2.objects[object]? = heap.objects[object]? := by
  simp only [cons_objects, Array.getElem?_push, if_neg different]

/-- Typed node lookup away from the fresh identifier has its exact old outcome. -/
theorem node?_cons_of_ne (heap : Heap) {τ σ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) {object : Nat}
    (different : object ≠ heap.objects.size) :
    (heap.cons head tail).2.node? σ object = heap.node? σ object := by
  unfold node?
  rw [heap.getElem?_cons_of_ne head tail different]

/-- Every old mutable array keeps its exact contents after node allocation. -/
theorem object?_cons_of_lt (heap : Heap) {τ σ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) {object : Nat}
    (bound : object < heap.objects.size) :
    (heap.cons head tail).2.object? σ object = heap.object? σ object := by
  unfold object?
  rw [heap.getElem?_cons_of_ne head tail (Nat.ne_of_lt bound)]

/-- The fresh identifier denotes precisely the new head and the shared tail. -/
theorem node?_cons_new (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heap.cons head tail).2.node? τ (heap.cons head tail).1.object = some (head, tail) := by
  apply node?_eq_some_iff.mpr
  exact Array.getElem?_push_size

/-- Node allocation preserves the complete old object prefix. -/
theorem objects_prefix_cons (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    List.IsPrefix heap.objects.toList (heap.cons head tail).2.objects.toList := by
  simpa only [cons_objects, Array.toList_push] using
    (List.prefix_append heap.objects.toList [.node τ head tail])

/-- All old shapes and complete immutable nodes survive the fresh allocation. -/
theorem shapeExtends_cons (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    heap.ShapeExtends (heap.cons head tail).2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [cons_size]
    omega
  · intro σ object values found
    exact ⟨values, (heap.object?_cons_of_lt head tail (object_lt_size found)).trans found, rfl⟩
  · intro σ object oldHead oldTail found
    exact (heap.node?_cons_of_ne head tail (Nat.ne_of_lt (node_lt_size found))).trans found

/-- Decompose an optional root by typed lookup of its actual immutable node.
An invalid nonempty root is an error, not an empty list. -/
def uncons (heap : Heap) {τ : CellTy} (root : Option (NodeRef τ)) :
    Except Error (Option (CellValue τ × Option (NodeRef τ))) :=
  match root with
  | none => .ok none
  | some ref =>
      match heap.node? τ ref.object with
      | none => .error .invalidObject
      | some contents => .ok (some contents)

@[simp] theorem uncons_none (heap : Heap) {τ : CellTy} :
    heap.uncons (τ := τ) none = .ok none := rfl

/-- Uncons returns the stored head and the identical tail handle. -/
theorem uncons_some_eq {heap : Heap} {τ : CellTy} {ref : NodeRef τ}
    {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ ref.object = some (head, tail)) :
    heap.uncons (some ref) = .ok (some (head, tail)) := by
  simp only [uncons, found]

/-- Missing or wrongly tagged nonempty roots fail the actual lookup. -/
theorem uncons_invalid {heap : Heap} {τ : CellTy} {ref : NodeRef τ}
    (missing : heap.node? τ ref.object = none) :
    heap.uncons (some ref) = .error .invalidObject := by
  simp only [uncons, missing]

/-- Reading the fresh node returns its head and shared tail without copying. -/
theorem uncons_cons (heap : Heap) {τ : CellTy}
    (head : CellValue τ) (tail : Option (NodeRef τ)) :
    (heap.cons head tail).2.uncons (some (heap.cons head tail).1) =
      .ok (some (head, tail)) :=
  uncons_some_eq (heap.node?_cons_new head tail)

end Heap

namespace NodeRef

/-- A finite, correctly typed linked chain observed as an ordinary list.
The nil root allocates no object; cons observes the actual stored tail. -/
inductive Contents {τ : CellTy} (heap : Heap) :
    Option (NodeRef τ) → List (CellValue τ) → Prop where
  | nil : Contents heap none []
  | cons {ref : NodeRef τ} {head : CellValue τ} {tail : Option (NodeRef τ)}
      {rest : List (CellValue τ)}
      (found : heap.node? τ ref.object = some (head, tail))
      (contents : Contents heap tail rest) : Contents heap (some ref) (head :: rest)

/-- A nonempty observed root denotes an existing typed node, not an arbitrary identifier. -/
theorem Contents.root_lt_size {heap : Heap} {τ : CellTy} {ref : NodeRef τ}
    {values : List (CellValue τ)} (observed : Contents heap (some ref) values) :
    ref.object < heap.objects.size := by
  cases observed with
  | cons found _ => exact Heap.node_lt_size found

/-- An observed chain has a uniquely determined mathematical list. -/
theorem Contents.unique {heap : Heap} {τ : CellTy} {root : Option (NodeRef τ)}
    {xs ys : List (CellValue τ)} (first : Contents heap root xs)
    (second : Contents heap root ys) : xs = ys := by
  revert second
  revert ys
  induction first with
  | nil =>
      intro ys second
      cases second
      rfl
  | cons found tail ih =>
      intro ys second
      cases second with
      | cons otherFound otherTail =>
          have same := Option.some.inj (found.symm.trans otherFound)
          have headEq := congrArg Prod.fst same
          have tailEq := congrArg Prod.snd same
          cases tailEq
          exact congrArg₂ List.cons headEq (@ih _ otherTail)

/-- Any extension preserving old immutable nodes preserves complete list contents. -/
theorem Contents.mono {initial finish : Heap} {τ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} (observed : Contents initial root values)
    (growth : initial.ShapeExtends finish) : Contents finish root values := by
  induction observed with
  | nil => exact .nil
  | cons found tail ih => exact .cons (growth.nodes found) ih

/-- Exact object-prefix preservation also preserves a shared linked chain. -/
theorem Contents.mono_prefix {initial finish : Heap} {τ : CellTy}
    {root : Option (NodeRef τ)} {values : List (CellValue τ)}
    (observed : Contents initial root values)
    (extension : List.IsPrefix initial.objects.toList finish.objects.toList) :
    Contents finish root values := by
  induction observed with
  | nil => exact .nil
  | cons found tail ih =>
      exact .cons ((Heap.node?_eq_of_prefix extension (Heap.node_lt_size found)).trans found) ih

/-- Successful scalar writes preserve every old list, even when other roots share its tail. -/
theorem Contents.write {heap finish : Heap} {τ σ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} {buffer : Buffer σ} {index : Nat} {value : CellValue σ}
    (observed : Contents heap root values) (written : heap.write buffer index value = .ok finish) :
    Contents finish root values :=
  observed.mono (Heap.shapeExtends_write written)

/-- Fresh buffer allocation preserves every existing linked-list observation. -/
theorem Contents.alloc {heap : Heap} {τ σ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} (observed : Contents heap root values)
    (length : Nat) (initial : CellValue σ) :
    Contents (heap.alloc length initial).2 root values :=
  observed.mono (heap.shapeExtends_alloc length initial)

/-- Adding any fresh node retains every old list; old roots need not be disjoint. -/
theorem Contents.node_alloc {heap : Heap} {τ σ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} (observed : Contents heap root values)
    (head : CellValue σ) (tail : Option (NodeRef σ)) :
    Contents (heap.cons head tail).2 root values :=
  observed.mono (heap.shapeExtends_cons head tail)

/-- Uncons has the ordinary nil/cons specification and retains a valid shared tail. -/
theorem Contents.uncons {heap : Heap} {τ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} (observed : Contents heap root values) :
    match values with
    | [] => heap.uncons root = .ok none
    | head :: rest => ∃ tail,
        heap.uncons root = .ok (some (head, tail)) ∧ Contents heap tail rest := by
  cases observed with
  | nil => rfl
  | cons found tail => exact ⟨_, Heap.uncons_some_eq found, tail⟩

/-- Keeping the root of an actual backward chain retains all of its typed nodes
and its complete contents. No global disjointness of roots is required. -/
theorem Contents.take {heap : Heap} {τ : CellTy} {root : Option (NodeRef τ)}
    {values : List (CellValue τ)} (observed : Contents heap root values)
    (backward : Heap.BackwardLinks Heap.nodeReferences heap) (count : Nat) :
    (∀ ref, root = some ref → ref.object < count) → Contents (heap.take count) root values := by
  induction observed with
  | nil => intro _; exact .nil
  | @cons ref head tail rest found observed ih =>
      intro retained
      refine .cons (Heap.node?_take_eq_some found (retained ref rfl)) (ih ?_)
      intro next sameTail
      have linked : heap.node? τ ref.object = some (head, some next) := by
        simpa only [sameTail] using found
      exact Nat.lt_trans (backward.node_tail_lt linked) (retained ref rfl)

end NodeRef

namespace Heap

/-- One actual node extends a valid shared tail with the ordinary list constructor. -/
theorem cons_contents {heap : Heap} {τ : CellTy} {tail : Option (NodeRef τ)}
    {values : List (CellValue τ)} (head : CellValue τ)
    (observed : NodeRef.Contents heap tail values) :
    NodeRef.Contents (heap.cons head tail).2 (some (heap.cons head tail).1) (head :: values) :=
  .cons (heap.node?_cons_new head tail) (observed.node_alloc head tail)

/-- A valid tail belongs to the old domain, so the fresh node's actual link is
strictly backward. No traversal, tail copying or address/id identification is assumed. -/
theorem BackwardLinks.cons {heap : Heap}
    (backward : BackwardLinks nodeReferences heap) {τ : CellTy}
    {tail : Option (NodeRef τ)} {values : List (CellValue τ)} (head : CellValue τ)
    (observed : NodeRef.Contents heap tail values) :
    BackwardLinks nodeReferences (heap.cons head tail).2 := by
  apply backward.push (.node τ head tail)
  intro target member
  cases tail with
  | none => simp [nodeReferences] at member
  | some ref =>
      have same : target = ref.object := by simpa only [nodeReferences, List.mem_singleton] using member
      subst target
      exact observed.root_lt_size

end Heap

end Complexity.Language
