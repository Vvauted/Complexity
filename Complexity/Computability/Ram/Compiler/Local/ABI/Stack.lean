/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Stack
import Complexity.Computability.Ram.Compiler.Local.ABI.Lifetime
import Complexity.Computability.Ram.Compiler.Local.Call.Setup

/-!
# Retained caller stacks across the actual ABI phases

Call setup adds its real saved return word and callee-sized register area to
an already retained stack. Every real setup prefix preserves the older areas
because its actual writes are disjoint from them. The completed setup reuses
`CallPreparedLocals`, with its endpoint fixed to the actual emitted block.

Return executes no stores, so all older saved values remain at every prefix.
During restoration, the union of older saved areas and the current frame's
pending obligations has an exact count at the same execution endpoint.
These are protocol-specific ghost obligations, not a heap live-space model:
SP retreat does not release them, and completed loads do not erase RAM.
-/

namespace Ram.ABI

/-- Every real setup prefix preserves the older saved stack. The separation
is from the actual complete write footprint, not from endpoint equality. -/
theorem callPrefixLocals_prefix_savedFrames
    {code : Code} {control locals returnPC heapLimit top k : Nat} {args : List Expr}
    {start current : State w} {frames : List (SavedFrame w)}
    (bufferFit : args.length ≤ control) (bounded : ∀ e ∈ args, e.Bounded control)
    (fits : (start.regs (sp control)).toNat + frameSize locals ≤ 2 ^ w)
    (retained : SavedFrames heapLimit top frames start.mem)
    (topBound : top ≤ (start.regs (sp control)).toNat)
    (atBlock : CodeAt code start.pc (callPrefixLocals control locals args returnPC))
    (running : start.status = .running)
    (hk : k ≤ (callPrefixLocals control locals args returnPC).length)
    (execution : Exec code k start current) :
    SavedFrames heapLimit top frames current.mem := by
  have separate : Disjoint (savedFrameSlots frames)
      (frameSlots (start.regs (sp control)) locals) :=
    retained.slots_disjoint_new
      (new := ⟨start.regs (sp control), locals, start.regs, BitVec.ofNat w returnPC⟩)
      fits topBound
  apply retained.congr
  intro address member
  apply execution.prefix_mem_eq_of_not_written hk
  rw [callPrefixLocals_heapWrites_eq_frameSlots bufferFit bounded atBlock running]
  exact fun written => Finset.disjoint_left.mp separate member written

/-- The actual call setup pushes its concrete saved descriptor at the advanced
SP. Correctness data is reused from the existing setup result; its `below`
field is used only at this completed endpoint, not to infer prefix safety. -/
theorem callPrefixLocals_savedFrames
    {code : Code} {control locals returnPC heapLimit : Nat} {args : List Expr}
    {source : Source.State w} {start : State w} {frames : List (SavedFrame w)}
    (prepared : CallPreparedLocals control locals heapLimit args returnPC source start
      (execBlock (callPrefixLocals control locals args returnPC) start))
    (retained : SavedFrames heapLimit (start.regs (sp control)).toNat frames start.mem)
    (heap : heapLimit ≤ (start.regs (sp control)).toNat)
    (atBlock : CodeAt code start.pc (callPrefixLocals control locals args returnPC))
    (running : start.status = .running) :
    let finish := execBlock (callPrefixLocals control locals args returnPC) start
    let newFrame : SavedFrame w :=
      ⟨start.regs (sp control), locals, start.regs, BitVec.ofNat w returnPC⟩
    Exec code (callPrefixLocals control locals args returnPC).length start finish ∧
    SavedFrames heapLimit (finish.regs (sp control)).toNat (newFrame :: frames) finish.mem := by
  have oldSaved : SavedFrames heapLimit (start.regs (sp control)).toNat frames
      (execBlock (callPrefixLocals control locals args returnPC) start).mem := by
    apply retained.congr
    intro address member
    exact prepared.below address
      (retained.slot_bounds (Word.toNat_lt _).le member).2
  refine ⟨callPrefixLocals_exec atBlock running, ?_⟩
  apply oldSaved.cons heap
  · exact prepared.sp.ge
  · exact ⟨prepared.returnAddress, prepared.saved⟩

/-- Every actual return prefix retains the whole older saved stack. The
reason is the proved empty write set, independently of the result's reads. -/
theorem returnPrefixLocals_prefix_savedFrames
    {code : Code} {control locals heapLimit top k : Nat} {result : Expr}
    {start current : State w} {frames : List (SavedFrame w)}
    (retained : SavedFrames heapLimit top frames start.mem)
    (atBlock : CodeAt code start.pc (returnPrefixLocals control locals result))
    (running : start.status = .running)
    (hk : k ≤ (returnPrefixLocals control locals result).length)
    (execution : Exec code k start current) :
    SavedFrames heapLimit top frames current.mem := by
  have memory := execution.prefix_mem_eq_of_heapWrites_empty hk
    (returnPrefixLocals_heapWrites_eq_empty atBlock running)
  exact retained.congr (fun address _ => congrFun memory address)

/-- At every actual restore prefix, the saved older stack, recovered RA and
locals, and precisely remaining current-frame obligations hold together.
The exact union count includes all older frames, not a sum of unrelated peaks. -/
theorem returnPrefixLocals_restore_prefix_savedFrames
    {code : Code} {control locals heapLimit k : Nat} {result : Expr}
    {start : State w} {base returnWord : Word w} {savedRegs : Reg → Word w}
    {frames : List (SavedFrame w)}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit start.regs start.mem) (heap : heapLimit ≤ base.toNat)
    (stack : (start.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (saved : FrameSaved locals base savedRegs start.mem)
    (header : start.mem base = returnWord)
    (retained : SavedFrames heapLimit base.toNat frames start.mem)
    (atBlock : CodeAt code start.pc (returnPrefixLocals control locals result))
    (running : start.status = .running) (hk : k ≤ 3 * locals) :
    let addressed := execBlock (returnHeaderBlock control locals result) start
    let current := execBlock ((restoreLocals control locals).take k) addressed
    Exec code ((returnHeaderBlock control locals result).length + k) start current ∧
    current.mem = start.mem ∧ current.regs (ra control) = returnWord ∧
    (∀ i, i < k / 3 → current.regs i = savedRegs i) ∧
    FrameSaved locals base savedRegs current.mem ∧
    SavedFrames heapLimit base.toNat frames current.mem ∧
    pendingFrameSlots code base locals
      ((returnHeaderBlock control locals result).length + k) start =
        pendingLocalSlots base locals (k / 3) ∧
    (pendingFrameSlots code base locals
      ((returnHeaderBlock control locals result).length + k) start).card = locals - k / 3 ∧
    (savedFrameSlots frames ∪ pendingFrameSlots code base locals
      ((returnHeaderBlock control locals result).length + k) start).card =
        (frames.map (fun frame => frameSize frame.locals)).sum + (locals - k / 3) := by
  obtain ⟨execution, memory, raEq, restored, frame, pending, pendingCard⟩ :=
    returnPrefixLocals_restore_prefix_lifetime localFit bounded reads heap stack fits
      saved header atBlock running hk
  have separateFrame : Disjoint (savedFrameSlots frames) (frameSlots base locals) :=
    retained.slots_disjoint_new (new := ⟨base, locals, savedRegs, returnWord⟩) fits.le le_rfl
  have separate : Disjoint (savedFrameSlots frames)
      (pendingFrameSlots code base locals
        ((returnHeaderBlock control locals result).length + k) start) := by
    apply Finset.disjoint_left.mpr
    intro address inOld inPending
    exact Finset.disjoint_left.mp separateFrame inOld (Finset.mem_sdiff.mp inPending).1
  refine ⟨execution, memory, raEq, restored, frame,
    retained.congr (fun address _ => congrFun memory address), pending, pendingCard, ?_⟩
  rw [Finset.card_union_of_disjoint separate,
    retained.slots_card (Word.toNat_lt base).le, pendingCard]

end Ram.ABI
