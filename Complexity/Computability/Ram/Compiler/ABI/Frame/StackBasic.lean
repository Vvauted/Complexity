/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.ABI.Slots
import Mathlib.Data.List.Pairwise

/-!
# Saved-frame assertions for nested execution

A `SavedFrame` records the original values in one concrete ABI save area.
`SavedFrames` relates a newest-first list of these assertions to the current
RAM memory. Older areas end at or below the next newer frame's base, so the
representation supports disjoint word counts even when there are gaps.

The list is specification data, not an added machine stack or allocation
operation. Its connection to the outstanding obligations of a particular
execution comes from the call, prefix-preservation and return lemmas.
-/

namespace Ram.ABI

/-- The values retained in one concrete return slot and local-save area. -/
structure SavedFrame (w : Nat) where
  base : Word w
  locals : Nat
  regs : Reg → Word w
  returnWord : Word w

namespace SavedFrame

/-- The exclusive natural end of the frame, before any modular reduction. -/
def endAddr (frame : SavedFrame w) : Nat := frame.base.toNat + frameSize frame.locals

/-- The existing ABI word-address set for this frame. -/
def slots (frame : SavedFrame w) : Finset (Word w) := frameSlots frame.base frame.locals

/-- All original saved values are still present in the specified RAM memory. -/
def Holds (frame : SavedFrame w) (mem : Word w → Word w) : Prop :=
  mem frame.base = frame.returnWord ∧ FrameSaved frame.locals frame.base frame.regs mem

end SavedFrame

/-- Union of the concrete saved areas in a newest-first frame list. -/
def savedFrameSlots : List (SavedFrame w) → Finset (Word w)
  | [] => ∅
  | frame :: frames => frame.slots ∪ savedFrameSlots frames

/-- Simultaneously retained frame values, with explicit heap/stack bounds
and ordered non-overlapping extents. `top` is a natural bound, not necessarily
the current SP during a partial save or restore phase. -/
structure SavedFrames (heapLimit top : Nat) (frames : List (SavedFrame w))
    (mem : Word w → Word w) : Prop where
  lower : ∀ frame ∈ frames, heapLimit ≤ frame.base.toNat
  upper : ∀ frame ∈ frames, frame.endAddr ≤ top
  ordered : frames.Pairwise (fun newer older => older.endAddr ≤ newer.base.toNat)
  saved : ∀ frame ∈ frames, frame.Holds mem

end Ram.ABI
