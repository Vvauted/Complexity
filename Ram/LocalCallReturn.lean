/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalABI
import Ram.LocalEffects

/-!
# Returning through a callee-sized frame

The reserved register base is independent of the number of locals saved by the
callee. The return code restores just those locals and preserves every user
register above them. Its cost is the length of the actual instruction sequence,
including the indirect jump to the saved return address.
-/

namespace Ram.ABI

private theorem returnLocals_scratch_bound (control : Nat) :
    control ≤ scratch control := by
  change control ≤ 2 * control + 5
  omega

private theorem returnLocals_sp_lt_scratch (control : Nat) :
    sp control < scratch control := by
  change control < 2 * control + 5
  omega

/-- State immediately before the final indirect jump. Locals come from the
saved frame; higher user registers retain their final-body values. -/
structure ReturnRestoredLocals (control localBound : Nat) (result : Expr)
    (sourceCallee : Source.State w) (savedRegs : Reg → Word w)
    (baseWord returnWord : Word w) (start finish : State w) : Prop where
  sp : finish.regs (ABI.sp control) = baseWord
  locals : ∀ i, i < localBound → finish.regs i = savedRegs i
  preservedAbove : RegsPreservedAbove control localBound start finish
  value : finish.regs (rv control) = sourceCallee.eval result
  address : finish.regs (ra control) = returnWord
  memory : finish.mem = start.mem
  input : finish.input = start.input
  output : finish.outputRev = start.outputRev
  status : finish.status = start.status
  pc : finish.pc = start.pc + (returnPrefixLocals control localBound result).length

/-- Evaluate the return expression before restoring the saved locals. Every
user register outside the callee's frame is preserved by the whole prefix. -/
theorem returnPrefixLocals_correct {control locals heapLimit : Nat} {result : Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (hlocals : locals ≤ control)
    (hmatch : sourceCallee.Matches heapLimit locals start)
    (hbounded : result.Bounded locals)
    (hreads : result.ReadsBelow heapLimit sourceCallee.regs sourceCallee.mem)
    (hfit : baseWord.toNat + frameSize locals < 2 ^ w)
    (hsp : (start.regs (sp control)).toNat = baseWord.toNat + frameSize locals)
    (hframe : FrameSaved locals baseWord savedRegs start.mem)
    (hreturn : start.mem baseWord = returnWord) :
    ReturnRestoredLocals control locals result sourceCallee savedRegs baseWord returnWord start
      (execBlock (returnPrefixLocals control locals result) start) := by
  let evaluated := execBlock (result.compile (scratch control)) start
  let buffered := execInstr (.move (rv control) (scratch control)) evaluated
  let retreated := execBlock (retreatLocals control locals) buffered
  let addressed := execInstr (.load (ra control) (sp control)) retreated
  have hc := Expr.compile_correct
    (hbounded.mono (Nat.le_trans hlocals (returnLocals_scratch_bound control))) start
  have heSP : evaluated.regs (sp control) = start.regs (sp control) :=
    hc.below (sp control) (returnLocals_sp_lt_scratch control)
  have hbSP : buffered.regs (sp control) = start.regs (sp control) := by
    have hne : sp control ≠ rv control := by simp [sp, rv]
    simpa only [buffered, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using heSP
  have hbValue : buffered.regs (rv control) = sourceCallee.eval result := by
    simpa only [buffered, execInstr, State.next_regs, State.setReg_same] using
      hc.value.trans (hmatch.eval_eq hbounded hreads).symm
  have hrSP : retreated.regs (sp control) = baseWord :=
    retreatLocals_sp control locals buffered baseWord (by rw [hbSP]; exact hsp) hfit
  have hrValue : retreated.regs (rv control) = sourceCallee.eval result :=
    (retreatLocals_regs control locals buffered (rv control) (by simp [rv, sp])
      (by simp [rv, tmp])).trans hbValue
  have hrMem : retreated.mem = start.mem := hc.memory
  have haSP : addressed.regs (sp control) = baseWord := by
    have hne : sp control ≠ ra control := by simp [sp, ra]
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hrSP
  have haValue : addressed.regs (rv control) = sourceCallee.eval result := by
    have hne : rv control ≠ ra control := by simp [rv, ra]
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hrValue
  have haReturn : addressed.regs (ra control) = returnWord := by
    simp only [addressed, execInstr, State.next_regs, State.setReg_same]
    rw [hrSP, hrMem]
    exact hreturn
  have haMem : addressed.mem = start.mem := hc.memory
  have haInput : addressed.input = start.input := hc.input
  have haOutput : addressed.outputRev = start.outputRev := hc.output
  have haStatus : addressed.status = start.status := hc.status
  have haAbove : RegsPreservedAbove control locals start addressed := by
    intro r _ hhi
    have hrScratch : r < scratch control :=
      Nat.lt_of_lt_of_le hhi (returnLocals_scratch_bound control)
    have hrRV : r ≠ rv control := by unfold rv; omega
    have hrSP : r ≠ sp control := by unfold sp; omega
    have hrTmp : r ≠ tmp control := by unfold tmp; omega
    have hrRA : r ≠ ra control := by unfold ra; omega
    have he : evaluated.regs r = start.regs r := hc.below r hrScratch
    have hb : buffered.regs r = start.regs r := by
      simpa only [buffered, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hrRV] using he
    have hr : retreated.regs r = start.regs r :=
      (retreatLocals_regs control locals buffered r hrSP hrTmp).trans hb
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hrRA] using hr
  have haFrame : FrameSaved locals (addressed.regs (sp control)) savedRegs addressed.mem := by
    rw [haSP, haMem]
    exact hframe
  have hfinish : execBlock (returnPrefixLocals control locals result) start =
      execBlock (restoreLocals control locals) addressed := by
    simp only [returnPrefixLocals, execBlock_append, execBlock_cons, execBlock_nil]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    execBlock_pc _ start (returnPrefixLocals_linear control locals result)⟩
  · rw [hfinish]
    exact (restoreLocals_sp addressed hlocals).trans haSP
  · rw [hfinish]
    exact restoreLocals_frame addressed hlocals savedRegs haFrame
  · intro r hlo hhi
    rw [hfinish]
    have hrAddr : r ≠ addr control := by unfold addr; omega
    have hrTmp : r ≠ tmp control := by unfold tmp; omega
    exact (restoreLocals_regs control locals addressed r hlo hrAddr hrTmp).trans
      (haAbove r hlo hhi)
  · rw [hfinish]
    exact (restoreLocals_rv addressed hlocals).trans haValue
  · rw [hfinish]
    exact (restoreLocals_ra addressed hlocals).trans haReturn
  · rw [hfinish]
    exact (restoreLocals_mem control locals addressed).trans haMem
  · rw [hfinish]
    exact (restoreLocals_input control locals addressed).trans haInput
  · rw [hfinish]
    exact (restoreLocals_output control locals addressed).trans haOutput
  · rw [hfinish]
    exact (restoreLocals_status control locals addressed).trans haStatus

/-- The restored address controls the actual indirect-jump instruction. -/
theorem ReturnRestoredLocals.jump_step {code : Code} {control locals returnPC : Nat}
    {result : Expr} {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start finish : State w}
    (h : ReturnRestoredLocals control locals result sourceCallee savedRegs
      baseWord returnWord start finish)
    (hrun : start.status = .running)
    (hfetch : code[finish.pc]? = some (.jumpReg (ra control)))
    (hreturnPC : returnWord.toNat = returnPC) :
    step code finish = some (finish.atPC returnPC) := by
  have hs := step_of_fetch (h.status.trans hrun) hfetch
  simpa only [execInstr, h.address, hreturnPC, State.atPC] using hs

/-- Complete execution, including the indirect jump, with exact emitted-code
length as its number of machine transitions. -/
theorem returnCodeLocals_exec {code : Code} {control locals returnPC : Nat} {result : Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (h : ReturnRestoredLocals control locals result sourceCallee savedRegs baseWord returnWord start
      (execBlock (returnPrefixLocals control locals result) start))
    (hcode : CodeAt code start.pc (returnCodeLocals control locals result))
    (hrun : start.status = .running) (hreturnPC : returnWord.toNat = returnPC) :
    Exec code (returnCodeLocals control locals result).length start
      ((execBlock (returnPrefixLocals control locals result) start).atPC returnPC) := by
  change CodeAt code start.pc
    (returnPrefixLocals control locals result ++ [.jumpReg (ra control)]) at hcode
  have hp := returnPrefixLocals_exec hcode.append_left hrun
  have hfetch : code[(execBlock (returnPrefixLocals control locals result) start).pc]? =
      some (.jumpReg (ra control)) := by
    rw [h.pc]
    exact hcode.append_right.head
  have hj := Exec.single (h.jump_step hrun hfetch hreturnPC)
  simpa only [returnCodeLocals, List.length_append, List.length_singleton] using hp.trans hj

end Ram.ABI
