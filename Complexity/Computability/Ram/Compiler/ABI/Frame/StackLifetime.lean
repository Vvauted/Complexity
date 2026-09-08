/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Lifetime
import Complexity.Computability.Ram.Compiler.ABI.Frame.Stack

/-!
# Growing the retained frame stack during actual saves

The return-slot store adds a zero-local frame assertion. During the following
local saves, only the first `k / 3` completed stores are included in the new
frame. Its original values and every older frame hold in the same actual
prefix state. Their disjoint slot count grows by one per completed store,
before the ABI advances SP.

These assertions record the values already saved by the given operations.
They are not a new allocation instruction or a source-level space charge.
-/

namespace Ram.ABI

/-- The actual return-slot store retains the older stack and establishes its
newest one-word frame before any local register has been saved. -/
theorem saveReturn_savedFrames {code : Code} {control heapLimit returnPC : Nat}
    {start current : State w} {older : List (SavedFrame w)}
    (retained : SavedFrames heapLimit (start.regs (sp control)).toNat older start.mem)
    (heap : heapLimit ≤ (start.regs (sp control)).toNat)
    (atBlock : CodeAt code start.pc (saveReturn control returnPC))
    (running : start.status = .running) (execution : Exec code 2 start current) :
    let newest : SavedFrame w :=
      ⟨start.regs (sp control), 0, start.regs, BitVec.ofNat w returnPC⟩
    SavedFrames heapLimit newest.endAddr (newest :: older) current.mem ∧
      (savedFrameSlots (newest :: older)).card =
        1 + (older.map (fun frame => frameSize frame.locals)).sum := by
  let newest : SavedFrame w :=
    ⟨start.regs (sp control), 0, start.regs, BitVec.ofNat w returnPC⟩
  have topFit := (BitVec.isLt (start.regs (sp control))).le
  have preserved := saveReturn_prefix_heap atBlock running (Nat.le_refl _)
    (Nat.le_refl 2) execution
  have oldNow : SavedFrames heapLimit (start.regs (sp control)).toNat older current.mem :=
    retained.congr (fun address member =>
      (preserved address (retained.slot_bounds topFit member).2).symm)
  have complete : Exec code 2 start (execBlock (saveReturn control returnPC) start) :=
    execBlock_exec atBlock (saveReturn_linear control returnPC) running
  have newestSaved : newest.Holds current.mem := by
    constructor
    · rw [execution.deterministic complete]
      exact saveReturn_same control returnPC start
    · intro i hi
      exact (Nat.not_lt_zero i hi).elim
  have savedNow : SavedFrames heapLimit newest.endAddr (newest :: older) current.mem :=
    oldNow.cons heap (Nat.le_refl _) newestSaved
  refine ⟨savedNow, ?_⟩
  have newestFit : newest.endAddr ≤ 2 ^ w := by
    have bound := BitVec.isLt (start.regs (sp control))
    change (start.regs (sp control)).toNat + frameSize 0 ≤ 2 ^ w
    simp only [frameSize]
    omega
  simpa only [List.map_cons, List.sum_cons, newest, frameSize, Nat.zero_add] using
    savedNow.slots_card newestFit

/-- Partial local saves extend exactly the initialized part of the newest
frame. All older frames and the already stored return word survive throughout
the same real prefix; a pending address calculation adds no saved slot. -/
theorem saveLocals_prefix_savedFrames {code : Code} {control locals heapLimit k : Nat}
    {start current : State w} {older : List (SavedFrame w)} {returnWord : Word w}
    (retained : SavedFrames heapLimit (start.regs (sp control)).toNat older start.mem)
    (heap : heapLimit ≤ (start.regs (sp control)).toNat)
    (header : start.mem (start.regs (sp control)) = returnWord)
    (localFit : locals ≤ control)
    (fits : (start.regs (sp control)).toNat + locals < 2 ^ w)
    (atBlock : CodeAt code start.pc (saveLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (execution : Exec code k start current) :
    let newest : SavedFrame w := ⟨start.regs (sp control), k / 3, start.regs, returnWord⟩
    SavedFrames heapLimit newest.endAddr (newest :: older) current.mem ∧
      (savedFrameSlots (newest :: older)).card =
        frameSize (k / 3) + (older.map (fun frame => frameSize frame.locals)).sum := by
  let newest : SavedFrame w := ⟨start.regs (sp control), k / 3, start.regs, returnWord⟩
  have topFit := (BitVec.isLt (start.regs (sp control))).le
  have preserved := saveLocals_prefix_heap atBlock running (Nat.le_refl _) fits hk execution
  have oldNow : SavedFrames heapLimit (start.regs (sp control)).toNat older current.mem :=
    retained.congr (fun address member =>
      (preserved address (retained.slot_bounds topFit member).2).symm)
  have headerEq : current.mem (start.regs (sp control)) =
      start.mem (start.regs (sp control)) := by
    apply execution.prefix_mem_eq_of_not_written hk
    intro member
    rw [saveLocals_heapWrites atBlock running] at member
    exact (Nat.lt_irrefl _) ((mem_slot_image_iff fits).mp member).1
  have newestSaved : newest.Holds current.mem :=
    ⟨headerEq.trans header, saveLocals_prefix_frame localFit fits atBlock running hk execution⟩
  have savedNow : SavedFrames heapLimit newest.endAddr (newest :: older) current.mem :=
    oldNow.cons heap (Nat.le_refl _) newestSaved
  refine ⟨savedNow, ?_⟩
  have newestFit : newest.endAddr ≤ 2 ^ w := by
    change (start.regs (sp control)).toNat + frameSize (k / 3) ≤ 2 ^ w
    simp only [frameSize]
    omega
  simpa only [List.map_cons, List.sum_cons, newest] using savedNow.slots_card newestFit

end Ram.ABI
