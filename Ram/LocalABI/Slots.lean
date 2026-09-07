/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Finset.Card
import Ram.LocalABI.Memory

/-!
# Counting and separating actual frame slots

`frameSlots` names the exact set already written by `callPrefixLocals`: the
return address followed by the callee-sized local save area. Its cardinality
is the existing `frameSize` when the addresses do not wrap. No global
injectivity of natural offsets into finite words is assumed.

These sets support later composition of simultaneously retained frames.
They are not a live-space semantics: merely taking their union does not prove
which frames coexist, and SP retreat alone does not release saved values.
-/

namespace Ram.ABI

/-- The return slot and local slots at one fixed frame base. This is the
same modular word-address set as the actual call-prefix write footprint. -/
def frameSlots (base : Word w) (locals : Nat) : Finset (Word w) :=
  {base} ∪ (Finset.range locals).image (fun i => arrayAddr base (i + 1))

/-- A fitted frame occupies its natural half-open interval. The interval may
end exactly at the address-space boundary; advancing SP needs its own fit. -/
theorem mem_frameSlots_iff {base address : Word w} {locals : Nat}
    (fits : base.toNat + frameSize locals ≤ 2 ^ w) :
    address ∈ frameSlots base locals ↔
      base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + frameSize locals := by
  have slotFit : base.toNat + locals < 2 ^ w := by
    unfold frameSize at fits
    omega
  simp only [frameSlots, Finset.mem_union, Finset.mem_singleton, mem_slot_image_iff slotFit]
  constructor
  · rintro (rfl | ⟨lower, upper⟩) <;> unfold frameSize <;> omega
  · intro bounds
    by_cases equal : address.toNat = base.toNat
    · exact Or.inl (BitVec.eq_of_toNat_eq equal)
    · right
      unfold frameSize at bounds
      omega

/-- No-wrap makes the actual local-slot image injective on its finite domain.
The return slot is distinct from every local slot. -/
theorem frameSlots_card {base : Word w} {locals : Nat}
    (fits : base.toNat + frameSize locals ≤ 2 ^ w) :
    (frameSlots base locals).card = frameSize locals := by
  have slotFit : base.toNat + locals < 2 ^ w := by
    unfold frameSize at fits
    omega
  have separate : Disjoint ({base} : Finset (Word w))
      ((Finset.range locals).image (fun i => arrayAddr base (i + 1))) := by
    apply Finset.disjoint_left.mpr
    intro address singleton member
    have equal := Finset.mem_singleton.mp singleton
    subst address
    have bounds := (mem_slot_image_iff slotFit).mp member
    omega
  have localCard : ((Finset.range locals).image
      (fun i => arrayAddr base (i + 1))).card = locals := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj equal
    have ilt := Finset.mem_range.mp hi
    have jlt := Finset.mem_range.mp hj
    have offsets := (arrayAddr_eq_iff (by omega) (by omega)).mp equal
    omega
  rw [frameSlots, Finset.card_union_of_disjoint separate, Finset.card_singleton, localCard]
  unfold frameSize
  omega

/-- Ordered non-overlapping fitted extents have disjoint word-address sets.
In particular, this applies when the next frame starts at the current end. -/
theorem frameSlots_disjoint_of_le {first second : Word w} {firstLocals secondLocals : Nat}
    (firstFit : first.toNat + frameSize firstLocals ≤ 2 ^ w)
    (secondFit : second.toNat + frameSize secondLocals ≤ 2 ^ w)
    (ordered : first.toNat + frameSize firstLocals ≤ second.toNat) :
    Disjoint (frameSlots first firstLocals) (frameSlots second secondLocals) := by
  apply Finset.disjoint_left.mpr
  intro address inFirst inSecond
  have firstBounds := (mem_frameSlots_iff firstFit).mp inFirst
  have secondBounds := (mem_frameSlots_iff secondFit).mp inSecond
  omega

/-- Disjoint saved areas add their exact word counts. A separate execution
argument must justify that both areas are retained at the same time. -/
theorem frameSlots_union_card {first second : Word w} {firstLocals secondLocals : Nat}
    (firstFit : first.toNat + frameSize firstLocals ≤ 2 ^ w)
    (secondFit : second.toNat + frameSize secondLocals ≤ 2 ^ w)
    (separate : Disjoint (frameSlots first firstLocals) (frameSlots second secondLocals)) :
    (frameSlots first firstLocals ∪ frameSlots second secondLocals).card =
      frameSize firstLocals + frameSize secondLocals := by
  rw [Finset.card_union_of_disjoint separate, frameSlots_card firstFit, frameSlots_card secondFit]

/-- The named frame set is exactly the complete call prefix's actual writes;
the base is entry SP, before argument evaluation and before SP advance. -/
theorem callPrefixLocals_heapWrites_eq_frameSlots {code : Code}
    {control locals returnPC : Nat} {args : List Expr} {s : State w}
    (bufferFit : args.length ≤ control) (bounded : ∀ e ∈ args, e.Bounded control)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running) :
    heapWrites code (callPrefixLocals control locals args returnPC).length s =
      frameSlots (s.regs (sp control)) locals :=
  (callPrefixLocals_footprints bufferFit bounded atBlock running).2

/-- A fitted actual call prefix writes exactly one return slot plus one slot
per callee local, irrespective of the global control-register bound. -/
theorem callPrefixLocals_heapWrites_card {code : Code}
    {control locals returnPC : Nat} {args : List Expr} {s : State w}
    (bufferFit : args.length ≤ control) (bounded : ∀ e ∈ args, e.Bounded control)
    (fits : (s.regs (sp control)).toNat + frameSize locals ≤ 2 ^ w)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running) :
    (heapWrites code (callPrefixLocals control locals args returnPC).length s).card =
      frameSize locals := by
  rw [callPrefixLocals_heapWrites_eq_frameSlots bufferFit bounded atBlock running]
  exact frameSlots_card fits

end Ram.ABI
