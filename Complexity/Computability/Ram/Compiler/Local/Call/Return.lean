/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Call.Results

/-!
# Returning through a callee-sized frame

The reserved register base is independent of the number of locals saved by the
callee. The return code restores just those locals and preserves every user
register above them. Its cost is the length of the actual instruction sequence,
including the indirect jump to the saved return address.
-/

namespace Ram.ABI

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
  have h := returnPrefixResultsLocals_correct (results := [result]) hlocals hmatch
    (by simp) (by simpa using hbounded) (by simpa using hreads) hfit hsp hframe hreturn
  refine ⟨h.sp, h.locals, h.preservedAbove, ?_, h.address, h.memory,
    h.input, h.output, h.status, h.pc⟩
  simpa using h.values 0 (by simp)

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
