/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalABI.Slots
import Ram.Frame.Lifetime

/-!
# Saved-frame obligations through the actual return phases

The named blocks below are only segments of `returnPrefixLocals`. They do not
introduce source operations, instructions, or another execution relation.

`pendingFrameSlots` subtracts actual return-time accesses from one fixed frame.
It describes still-to-be-restored saved words only for this proved write-free
return protocol: result evaluation stays below the frame, the header load
recovers the return address, and the remaining loads restore the saved locals.
It is not a general rule that reading memory frees it, nor a heap live-space
measure. SP movement itself consumes no saved-word obligation.
-/

namespace Ram.ABI

/-- Fixed saved slots not yet read since this return began. Interpretation as
restore obligations requires the concrete protocol proved below. -/
def pendingFrameSlots (code : Code) (base : Word w) (locals steps : Nat)
    (start : State w) : Finset (Word w) :=
  frameSlots base locals \ heapAccesses code steps start

/-- The existing return prefix through result buffering and SP retreat,
immediately before its first saved-frame load. -/
def returnRetreatBlock (control locals : Nat) (result : Expr) : Code :=
  result.compile (scratch control) ++ [.move (rv control) (scratch control)] ++
    retreatLocals control locals

/-- The same prefix including the real load of the saved return address. -/
def returnHeaderBlock (control locals : Nat) (result : Expr) : Code :=
  returnRetreatBlock control locals result ++ [.load (ra control) (sp control)]

/-- These named phases concatenate to exactly the existing emitted code. -/
theorem returnPrefixLocals_eq_stages (control locals : Nat) (result : Expr) :
    returnPrefixLocals control locals result =
      returnHeaderBlock control locals result ++ restoreLocals control locals := rfl

private theorem retreatBlock_linear (control locals : Nat) (result : Expr) :
    ∀ i ∈ returnRetreatBlock control locals result, i.Linear := by
  intro i hi
  simp only [returnRetreatBlock, List.mem_append, List.mem_singleton] at hi
  rcases hi with (he | rfl) | hr
  · exact result.compile_linear (scratch control) i he
  · trivial
  · exact retreatLocals_linear control locals i hr

private theorem headerBlock_linear (control locals : Nat) (result : Expr) :
    ∀ i ∈ returnHeaderBlock control locals result, i.Linear := by
  intro i hi
  simp only [returnHeaderBlock, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact retreatBlock_linear control locals result i hi
  · trivial

private theorem after_linear {code left right : Code} {s : State w}
    (atBlock : CodeAt code s.pc (left ++ right))
    (linear : ∀ i ∈ left, i.Linear) :
    CodeAt code (execBlock left s).pc right := by
  rw [execBlock_pc left s linear]
  exact atBlock.append_right

private theorem retreat_phase {code : Code} {control locals : Nat} {result : Expr}
    {s : State w} {base : Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    let retired := execBlock (returnRetreatBlock control locals result) s
    Exec code (returnRetreatBlock control locals result).length s retired ∧
    retired.regs (sp control) = base ∧ retired.mem = s.mem ∧
    heapAccesses code (returnRetreatBlock control locals result).length s =
      heapAccesses code (result.compile (scratch control)).length s := by
  let evaluated := execBlock (result.compile (scratch control)) s
  let buffered := execInstr (.move (rv control) (scratch control)) evaluated
  have scratchFit : control ≤ scratch control := by unfold scratch; omega
  have correct := Expr.compile_correct (bounded.mono (localFit.trans scratchFit)) s
  have spEvaluated : evaluated.regs (sp control) = s.regs (sp control) :=
    correct.below (sp control) (by change control < 2 * control + 5; omega)
  have spBuffered : buffered.regs (sp control) = s.regs (sp control) := by
    have ne : sp control ≠ rv control := by simp [sp, rv]
    simpa only [buffered, execInstr, State.next_regs, State.setReg_ne _ _ _ _ ne]
      using spEvaluated
  have atRetreat : CodeAt code s.pc (returnRetreatBlock control locals result) :=
    atBlock.append_left.append_left
  have retiredEq : execBlock (returnRetreatBlock control locals result) s =
      execBlock (retreatLocals control locals) buffered := by
    simp only [returnRetreatBlock, execBlock_append, execBlock_cons, execBlock_nil]
    rfl
  refine ⟨execBlock_exec atRetreat (retreatBlock_linear control locals result) running,
    ?_, ?_, ?_⟩
  · rw [retiredEq]
    exact retreatLocals_sp control locals buffered base (by rw [spBuffered]; exact stack) fits
  · rw [retiredEq]
    exact correct.memory
  · let tail := [.move (rv control) (scratch control)] ++ retreatLocals control locals
    have atSplit : CodeAt code s.pc (result.compile (scratch control) ++ tail) := by
      simpa only [returnRetreatBlock, tail, List.append_assoc] using atRetreat
    have atTail := after_linear atSplit (result.compile_linear (scratch control))
    have tailLinear : ∀ i ∈ tail, i.Linear := by
      intro i hi
      simp only [tail, List.mem_append, List.mem_singleton] at hi
      rcases hi with rfl | hi
      · trivial
      · exact retreatLocals_linear control locals i hi
    have tailEmpty : heapAccesses code tail.length evaluated = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro address member
      obtain ⟨k, hk, access⟩ := (mem_heapAccesses_execBlock_iff atTail tailLinear
        (correct.status.trans running) address).mp member
      have noAccess : ∀ i ∈ tail, ∀ t : State w, i.heapAccesses t = ∅ := by
        intro i hi t
        simp only [tail, retreatLocals, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> rfl
      rw [noAccess _ (List.getElem_mem hk)] at access
      exact Finset.notMem_empty _ access
    have split := heapAccesses_add (Expr.compile_exec atSplit.append_left running) tail.length
    rw [tailEmpty, Finset.union_empty] at split
    simpa only [returnRetreatBlock, tail, List.length_append, Nat.add_assoc]
      using split

/-- Result evaluation, buffering and the actual SP retreat leave every frame
obligation pending, at every real prefix through this phase. In particular,
retreating SP to `base` is not a release of saved storage. -/
theorem returnPrefixLocals_pending_before_header
    {code : Code} {control locals heapLimit : Nat} {result : Expr}
    {s : State w} {base : Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem) (heap : heapLimit ≤ base.toNat)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    let retired := execBlock (returnRetreatBlock control locals result) s
    Exec code (returnRetreatBlock control locals result).length s retired ∧
    retired.regs (sp control) = base ∧ retired.mem = s.mem ∧
    ∀ k, k ≤ (returnRetreatBlock control locals result).length →
      pendingFrameSlots code base locals k s = frameSlots base locals := by
  obtain ⟨execution, spEq, memEq, accesses⟩ :=
    retreat_phase localFit bounded stack fits atBlock running
  refine ⟨execution, spEq, memEq, ?_⟩
  intro k hk
  ext address
  simp only [pendingFrameSlots, Finset.mem_sdiff]
  constructor
  · exact And.left
  · intro member
    refine ⟨member, ?_⟩
    intro access
    have exprAccess := heapAccesses_mono code s hk access
    rw [accesses] at exprAccess
    have scratchFit : control ≤ scratch control := by unfold scratch; omega
    have below := Expr.compile_heapAccesses_below
      (bounded.mono (localFit.trans scratchFit)) reads
      atBlock.append_left.append_left.append_left.append_left running exprAccess
    have lower := (mem_frameSlots_iff fits.le).mp member
    omega

/-- The actual header load consumes exactly the return-slot obligation and
loads its saved value into RA. All local-slot obligations and saved values
remain, even though SP was already retreated before the load. -/
theorem returnPrefixLocals_header_lifetime
    {code : Code} {control locals heapLimit : Nat} {result : Expr}
    {s : State w} {base returnWord : Word w} {savedRegs : Reg → Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem) (heap : heapLimit ≤ base.toNat)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (saved : FrameSaved locals base savedRegs s.mem) (header : s.mem base = returnWord)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    let addressed := execBlock (returnHeaderBlock control locals result) s
    Exec code (returnHeaderBlock control locals result).length s addressed ∧
    addressed.regs (sp control) = base ∧ addressed.mem = s.mem ∧
    addressed.regs (ra control) = returnWord ∧
    FrameSaved locals base savedRegs addressed.mem ∧
    pendingFrameSlots code base locals (returnHeaderBlock control locals result).length s =
      (Finset.range locals).image (fun i => arrayAddr base (i + 1)) := by
  let retired := execBlock (returnRetreatBlock control locals result) s
  obtain ⟨beforeRun, spEq, memEq, pending⟩ :=
    returnPrefixLocals_pending_before_header localFit bounded reads heap stack fits atBlock running
  have atHeader : CodeAt code s.pc (returnHeaderBlock control locals result) := atBlock.append_left
  have atLoad := after_linear atHeader (retreatBlock_linear control locals result)
  have retiredRunning :=
    (execBlock_status _ s (retreatBlock_linear control locals result)).trans running
  have headerAccess : heapAccesses code (returnHeaderBlock control locals result).length s =
      heapAccesses code (returnRetreatBlock control locals result).length s ∪ {base} := by
    rw [returnHeaderBlock, List.length_append, List.length_singleton,
      heapAccesses_add beforeRun, heapAccesses_one,
      stepHeapAccesses_of_fetch retiredRunning atLoad.head]
    simp only [Instr.heapAccesses, spEq]
  have addressedEq : execBlock (returnHeaderBlock control locals result) s =
      execInstr (.load (ra control) (sp control)) retired := by
    simp only [returnHeaderBlock, execBlock_append, execBlock_cons, execBlock_nil]
    rfl
  have addressedMem : (execBlock (returnHeaderBlock control locals result) s).mem = s.mem := by
    rw [addressedEq]
    exact memEq
  refine ⟨execBlock_exec atHeader (headerBlock_linear control locals result) running,
    ?_, addressedMem, ?_, ?_, ?_⟩
  · have ne : sp control ≠ ra control := by simp [sp, ra]
    rw [addressedEq]
    simpa only [execInstr, State.next_regs, State.setReg_ne _ _ _ _ ne] using spEq
  · rw [addressedEq]
    simp only [execInstr, State.next_regs, State.setReg_same]
    rw [spEq, memEq]
    exact header
  · rw [addressedMem]
    exact saved
  · have noEarlier : ∀ address ∈ frameSlots base locals,
        address ∉ heapAccesses code (returnRetreatBlock control locals result).length s := by
      intro address member
      have hp : address ∈ pendingFrameSlots code base locals
          (returnRetreatBlock control locals result).length s := by
        rw [pending _ le_rfl]
        exact member
      exact (Finset.mem_sdiff.mp hp).2
    have slotFit : base.toNat + locals < 2 ^ w := by unfold frameSize at fits; omega
    ext address
    rw [pendingFrameSlots, headerAccess, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ⟨member, unread⟩
      rcases Finset.mem_union.mp member with hbase | hlocal
      · exact False.elim (unread (Or.inr (Finset.mem_singleton.mp hbase)))
      · exact hlocal
    · intro member
      have inFrame : address ∈ frameSlots base locals := Finset.mem_union.mpr (Or.inr member)
      refine ⟨inFrame, ?_⟩
      rintro (earlier | equal)
      · exact noEarlier address inFrame earlier
      · subst address
        have bounds := (mem_slot_image_iff slotFit).mp member
        omega

/-- Completing the real restore block consumes the remaining obligations and
recovers every saved local and the saved return address in the same endpoint.
The old frame words remain in memory; empty obligations do not mean erasure. -/
theorem returnPrefixLocals_restore_lifetime
    {code : Code} {control locals heapLimit : Nat} {result : Expr}
    {s : State w} {base returnWord : Word w} {savedRegs : Reg → Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem) (heap : heapLimit ≤ base.toNat)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (saved : FrameSaved locals base savedRegs s.mem) (header : s.mem base = returnWord)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    let finish := execBlock (returnPrefixLocals control locals result) s
    Exec code (returnPrefixLocals control locals result).length s finish ∧
    finish.regs (sp control) = base ∧ finish.mem = s.mem ∧
    finish.regs (ra control) = returnWord ∧
    (∀ i, i < locals → finish.regs i = savedRegs i) ∧
    pendingFrameSlots code base locals (returnPrefixLocals control locals result).length s = ∅ := by
  let addressed := execBlock (returnHeaderBlock control locals result) s
  obtain ⟨_, spEq, memEq, raEq, frame, _⟩ :=
    returnPrefixLocals_header_lifetime localFit bounded reads heap stack fits saved header
      atBlock running
  have finishEq : execBlock (returnPrefixLocals control locals result) s =
      execBlock (restoreLocals control locals) addressed := by
    rw [returnPrefixLocals_eq_stages, execBlock_append]
  refine ⟨returnPrefixLocals_exec atBlock running, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finishEq, restoreLocals_sp addressed localFit]
    exact spEq
  · rw [finishEq, restoreLocals_mem]
    exact memEq
  · rw [finishEq, restoreLocals_ra addressed localFit]
    exact raEq
  · rw [finishEq]
    apply restoreLocals_frame addressed localFit savedRegs
    rw [spEq]
    exact frame
  · have accesses := returnPrefixLocals_heapAccesses localFit bounded stack fits atBlock running
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro address member
    have hp := Finset.mem_sdiff.mp member
    apply hp.2
    rw [accesses]
    exact Finset.mem_union.mpr (Or.inr hp.1)

/-- Split the actual read history at a proved execution endpoint. This is an
identity of the existing sets, not a generic memory-release operation. -/
theorem pendingFrameSlots_add {code : Code} {base : Word w} {locals n : Nat}
    {start middle : State w} (execution : Exec code n start middle) (k : Nat) :
    pendingFrameSlots code base locals (n + k) start =
      pendingFrameSlots code base locals n start \ heapAccesses code k middle := by
  rw [pendingFrameSlots, heapAccesses_add execution]
  exact sdiff_sdiff_left.symm

/-- At every real restore prefix of the complete return, only completed loads
consume local obligations. The recovered registers and all still-saved memory
values are witnessed at the same endpoint, with an exact remaining-word count. -/
theorem returnPrefixLocals_restore_prefix_lifetime
    {code : Code} {control locals heapLimit k : Nat} {result : Expr}
    {s : State w} {base returnWord : Word w} {savedRegs : Reg → Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem) (heap : heapLimit ≤ base.toNat)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (saved : FrameSaved locals base savedRegs s.mem) (header : s.mem base = returnWord)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) (hk : k ≤ 3 * locals) :
    let addressed := execBlock (returnHeaderBlock control locals result) s
    let current := execBlock ((restoreLocals control locals).take k) addressed
    Exec code ((returnHeaderBlock control locals result).length + k) s current ∧
    current.mem = s.mem ∧ current.regs (ra control) = returnWord ∧
    (∀ i, i < k / 3 → current.regs i = savedRegs i) ∧
    FrameSaved locals base savedRegs current.mem ∧
    pendingFrameSlots code base locals ((returnHeaderBlock control locals result).length + k) s =
      pendingLocalSlots base locals (k / 3) ∧
    (pendingFrameSlots code base locals
      ((returnHeaderBlock control locals result).length + k) s).card = locals - k / 3 := by
  let addressed := execBlock (returnHeaderBlock control locals result) s
  obtain ⟨headerRun, spEq, memEq, raEq, frame, headerPending⟩ :=
    returnPrefixLocals_header_lifetime localFit bounded reads heap stack fits saved header
      atBlock running
  have atRestore : CodeAt code addressed.pc (restoreLocals control locals) :=
    after_linear (left := returnHeaderBlock control locals result) atBlock
      (headerBlock_linear control locals result)
  have ready : addressed.status = .running :=
    (execBlock_status _ s (headerBlock_linear control locals result)).trans running
  have restoreRun : Exec code k addressed
      (execBlock ((restoreLocals control locals).take k) addressed) :=
    execBlock_take_exec atRestore (restoreLocals_linear control locals) ready
      (by simpa only [restoreLocals_length] using hk)
  have spAddressed : addressed.regs (sp control) = base := spEq
  have frameAtSP : FrameSaved locals (addressed.regs (sp control)) savedRegs addressed.mem := by
    rw [spEq]
    exact frame
  have slotFit : base.toNat + locals < 2 ^ w := by unfold frameSize at fits; omega
  have restoreFit : (addressed.regs (sp control)).toNat + locals < 2 ^ w := by
    rw [spEq]
    exact slotFit
  have pendingEq : pendingFrameSlots code base locals
      ((returnHeaderBlock control locals result).length + k) s =
        pendingLocalSlots base locals (k / 3) := by
    rw [pendingFrameSlots_add headerRun k, headerPending]
    simpa only [spAddressed] using
      (restoreLocals_pending_slots localFit restoreFit atRestore ready hk).symm
  refine ⟨headerRun.trans restoreRun, ?_, ?_, ?_, ?_, pendingEq, ?_⟩
  · exact (restoreLocals_prefix_mem atRestore ready hk restoreRun).trans memEq
  · exact (restoreLocals_prefix_regs (register := ra control) atRestore ready hk
      (by simp [ra, addr]) (by simp [ra, tmp]) restoreRun).trans
        ((restoreLocals_ra addressed (by omega)).trans raEq)
  · exact restoreLocals_prefix_restored localFit frameAtSP atRestore ready hk restoreRun
  · simpa only [spAddressed] using
      restoreLocals_prefix_frame frameAtSP atRestore ready hk restoreRun
  · rw [pendingEq]
    exact pendingLocalSlots_card slotFit

end Ram.ABI
