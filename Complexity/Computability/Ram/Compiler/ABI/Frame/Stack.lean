/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.StackBasic

/-!
# Structural and counting interfaces for saved-frame stacks

The newest-first ordering permits extension and removal of a saved-frame
assertion without assuming contiguous allocation. Memory congruence is local
to the union of retained slots. Under the explicit no-wrap bound, the union's
cardinality is the ordinary list sum of the existing ABI frame sizes.

These are assertions about retained save areas, not a characterization of all
live frames or a tight peak-space semantics for an execution.
-/

namespace Ram.ABI

@[simp] theorem savedFrameSlots_nil : savedFrameSlots ([] : List (SavedFrame w)) = ∅ := rfl

@[simp] theorem savedFrameSlots_cons (frame : SavedFrame w) (frames : List (SavedFrame w)) :
    savedFrameSlots (frame :: frames) = frame.slots ∪ savedFrameSlots frames := rfl

/-- Membership in the union is witnessed by one retained frame. -/
theorem mem_savedFrameSlots {address : Word w} {frames : List (SavedFrame w)} :
    address ∈ savedFrameSlots frames ↔ ∃ frame ∈ frames, address ∈ frame.slots := by
  induction frames with
  | nil => simp [savedFrameSlots]
  | cons frame frames ih => simp [savedFrameSlots, ih, or_and_right, exists_or]

namespace SavedFrame

/-- Retention of one frame depends only on its own concrete slots. -/
theorem Holds.congr {frame : SavedFrame w} {mem mem' : Word w → Word w}
    (h : frame.Holds mem)
    (equal : ∀ address ∈ frame.slots, mem' address = mem address) :
    frame.Holds mem' := by
  refine ⟨?_, h.2.congr ?_⟩
  · exact (equal frame.base (by simp [slots, frameSlots])).trans h.1
  · intro i hi
    apply equal
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

end SavedFrame

namespace SavedFrames

/-- Empty saved-frame assertions require no relation between the two bounds. -/
theorem nil (heapLimit top : Nat) (mem : Word w → Word w) :
    SavedFrames heapLimit top [] mem := by
  constructor <;> simp

/-- Extend an old assertion bounded by the new frame's base. The new upper
bound may leave a gap above the saved frame. -/
theorem cons {heapLimit top : Nat} {frame : SavedFrame w}
    {frames : List (SavedFrame w)} {mem : Word w → Word w}
    (old : SavedFrames heapLimit frame.base.toNat frames mem)
    (lower : heapLimit ≤ frame.base.toNat) (upper : frame.endAddr ≤ top)
    (saved : frame.Holds mem) :
    SavedFrames heapLimit top (frame :: frames) mem := by
  have base_le_top : frame.base.toNat ≤ top :=
    (Nat.le_add_right frame.base.toNat (frameSize frame.locals)).trans upper
  refine ⟨?_, ?_, List.pairwise_cons.mpr ⟨old.upper, old.ordered⟩, ?_⟩
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact lower
    · exact old.lower other member
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact upper
    · exact (old.upper other member).trans base_le_top
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact saved
    · exact old.saved other member

/-- Discarding the newest assertion shrinks the bound to its base, using the
ordering field rather than any assertion about the current machine SP. -/
theorem tail {heapLimit top : Nat} {frame : SavedFrame w}
    {frames : List (SavedFrame w)} {mem : Word w → Word w}
    (h : SavedFrames heapLimit top (frame :: frames) mem) :
    SavedFrames heapLimit frame.base.toNat frames mem := by
  exact ⟨fun other member => h.lower other (List.mem_cons_of_mem _ member),
    (List.pairwise_cons.mp h.ordered).1, h.ordered.of_cons,
    fun other member => h.saved other (List.mem_cons_of_mem _ member)⟩

/-- Enlarge the natural upper bound without changing the retained slots. -/
theorem mono_top {heapLimit top top' : Nat} {frames : List (SavedFrame w)}
    {mem : Word w → Word w} (h : SavedFrames heapLimit top frames mem)
    (le : top ≤ top') : SavedFrames heapLimit top' frames mem :=
  ⟨h.lower, fun frame member => (h.upper frame member).trans le, h.ordered, h.saved⟩

/-- Changes outside the union of saved areas preserve all retained values. -/
theorem congr {heapLimit top : Nat} {frames : List (SavedFrame w)}
    {mem mem' : Word w → Word w} (h : SavedFrames heapLimit top frames mem)
    (equal : ∀ address ∈ savedFrameSlots frames, mem' address = mem address) :
    SavedFrames heapLimit top frames mem' := by
  refine ⟨h.lower, h.upper, h.ordered, ?_⟩
  intro frame member
  exact (h.saved frame member).congr fun address inFrame =>
    equal address (mem_savedFrameSlots.mpr ⟨frame, member, inFrame⟩)

/-- Every retained word lies between the heap limit and the natural top,
provided that top fits in the word-address space. -/
theorem slot_bounds {heapLimit top : Nat} {frames : List (SavedFrame w)}
    {mem : Word w → Word w} (h : SavedFrames heapLimit top frames mem)
    (topFit : top ≤ 2 ^ w) {address : Word w}
    (member : address ∈ savedFrameSlots frames) :
    heapLimit ≤ address.toNat ∧ address.toNat < top := by
  obtain ⟨frame, inFrames, inFrame⟩ := mem_savedFrameSlots.mp member
  have bounds := (mem_frameSlots_iff ((h.upper frame inFrames).trans topFit)).mp inFrame
  exact ⟨(h.lower frame inFrames).trans bounds.1,
    bounds.2.trans_le (h.upper frame inFrames)⟩

/-- A fitted new save area beginning at or above the old top is disjoint
from every slot named by the old assertion. -/
theorem slots_disjoint_new {heapLimit top : Nat} {frames : List (SavedFrame w)}
    {mem : Word w → Word w} (h : SavedFrames heapLimit top frames mem)
    {new : SavedFrame w} (newFit : new.endAddr ≤ 2 ^ w)
    (top_le_base : top ≤ new.base.toNat) :
    Disjoint (savedFrameSlots frames) new.slots := by
  apply Finset.disjoint_left.mpr
  intro address inOld inNew
  obtain ⟨old, member, inFrame⟩ := mem_savedFrameSlots.mp inOld
  have oldEnd : old.endAddr ≤ new.base.toNat := (h.upper old member).trans top_le_base
  have base_le_end : new.base.toNat ≤ new.endAddr :=
    Nat.le_add_right new.base.toNat (frameSize new.locals)
  exact Finset.disjoint_left.mp
    (frameSlots_disjoint_of_le (oldEnd.trans (base_le_end.trans newFit)) newFit oldEnd)
    inFrame inNew

/-- Ordered retained save areas have the sum of their individual ABI word
counts; no contiguity hypothesis or separately defined summation is needed. -/
theorem slots_card {heapLimit top : Nat} {frames : List (SavedFrame w)}
    {mem : Word w → Word w} (h : SavedFrames heapLimit top frames mem)
    (topFit : top ≤ 2 ^ w) :
    (savedFrameSlots frames).card = (frames.map (fun frame => frameSize frame.locals)).sum := by
  induction frames generalizing top with
  | nil => simp
  | cons frame frames ih =>
    have frameFit : frame.endAddr ≤ 2 ^ w := (h.upper frame (by simp)).trans topFit
    have baseFit : frame.base.toNat ≤ 2 ^ w :=
      (Nat.le_add_right frame.base.toNat (frameSize frame.locals)).trans frameFit
    have separate := (h.tail.slots_disjoint_new frameFit (Nat.le_refl _)).symm
    rw [savedFrameSlots_cons, Finset.card_union_of_disjoint separate,
      show frame.slots.card = frameSize frame.locals from frameSlots_card frameFit,
      ih h.tail baseFit]
    rfl

/-- The sum of saved frame sizes fits in the natural heap-to-top interval,
including stacks with gaps. This arithmetic bound does not require no-wrap. -/
theorem sum_frameSize_le {heapLimit top : Nat} {frames : List (SavedFrame w)}
    {mem : Word w → Word w} (h : SavedFrames heapLimit top frames mem) :
    (frames.map (fun frame => frameSize frame.locals)).sum ≤ top - heapLimit := by
  induction frames generalizing top with
  | nil => simp
  | cons frame frames ih =>
    have tailBound := ih h.tail
    have lower := h.lower frame (by simp)
    have upper := h.upper frame (by simp)
    simp only [SavedFrame.endAddr] at upper
    simp only [List.map_cons, List.sum_cons]
    omega

end SavedFrames

end Ram.ABI
