/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.ABI.Basic
import Complexity.Computability.Ram.Compiler.Local.Effects

/-!
# Returning multiple fields through a callee-sized frame

Every return expression is evaluated in the original callee state before the
saved caller locals are restored. The resulting words survive frame restoration
in the return registers. Empty returns still restore the frame and jump to the
saved return address, without evaluating or moving a dummy result.

The complete return executes the emitted prefix and its actual indirect jump;
its transition count is the length of that instruction sequence.
-/

namespace Ram.ABI

/-- Retreating the stack pointer preserves every buffered return field. -/
theorem retreatLocals_resultReg (control locals : Nat) (s : State w) (i : Nat) :
    (execBlock (retreatLocals control locals) s).regs (resultReg control i) =
      s.regs (resultReg control i) := by
  apply retreatLocals_regs
  · exact Nat.ne_of_gt (lt_resultReg control i)
  · cases i with
    | zero =>
        change control + 1 ≠ control + 4
        omega
    | succ i =>
        change control + 5 + i ≠ control + 4
        omega

/-- Restoring the caller's locals leaves the return-field bank unchanged. -/
theorem restoreLocals_resultReg {control locals : Nat} (s : State w)
    (hlocals : locals ≤ control) (i : Nat) :
    (execBlock (restoreLocals control locals) s).regs (resultReg control i) =
      s.regs (resultReg control i) := by
  cases i with
  | zero => exact restoreLocals_rv s hlocals
  | succ i => exact restoreLocals_arg s hlocals i

/-- State before the final indirect jump. The return fields contain their
callee-local expression values; the caller's saved locals have been restored. -/
structure ReturnResultsRestoredLocals (control localBound : Nat) (results : List Expr)
    (sourceCallee : Source.State w) (savedRegs : Reg → Word w)
    (baseWord returnWord : Word w) (start finish : State w) : Prop where
  sp : finish.regs (ABI.sp control) = baseWord
  locals : ∀ i, i < localBound → finish.regs i = savedRegs i
  preservedAbove : RegsPreservedAbove control localBound start finish
  values : ∀ (i : Nat) (hi : i < results.length),
    finish.regs (resultReg control i) = sourceCallee.eval results[i]
  address : finish.regs (ra control) = returnWord
  memory : finish.mem = start.mem
  input : finish.input = start.input
  output : finish.outputRev = start.outputRev
  status : finish.status = start.status
  pc : finish.pc = start.pc + (returnPrefixResultsLocals control localBound results).length

/-- Evaluate every return field before restoring the saved locals. User
registers outside the callee's frame survive the entire return prefix. -/
theorem returnPrefixResultsLocals_correct {control locals heapLimit : Nat}
    {results : List Expr} {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (hlocals : locals ≤ control)
    (hmatch : sourceCallee.Matches heapLimit locals start)
    (hfitResults : results.length - 1 ≤ control)
    (hbounded : ∀ e ∈ results, e.Bounded locals)
    (hreads : ∀ e ∈ results, e.ReadsBelow heapLimit sourceCallee.regs sourceCallee.mem)
    (hfit : baseWord.toNat + frameSize locals < 2 ^ w)
    (hsp : (start.regs (sp control)).toNat = baseWord.toNat + frameSize locals)
    (hframe : FrameSaved locals baseWord savedRegs start.mem)
    (hreturn : start.mem baseWord = returnWord) :
    ReturnResultsRestoredLocals control locals results sourceCallee savedRegs
      baseWord returnWord start
      (execBlock (returnPrefixResultsLocals control locals results) start) := by
  let buffered := execBlock (evalResults control results) start
  let retreated := execBlock (retreatLocals control locals) buffered
  let addressed := execInstr (.load (ra control) (sp control)) retreated
  have hb := evalResults_correct hfitResults (fun e he => (hbounded e he).mono hlocals) start
  have hbSP : buffered.regs (sp control) = start.regs (sp control) :=
    hb.preserved (sp control) (by simp [sp]) (by simp [sp, rv])
  have hrSP : retreated.regs (sp control) = baseWord :=
    retreatLocals_sp control locals buffered baseWord (by rw [hbSP]; exact hsp) hfit
  have hrValues : ∀ (i : Nat) (hi : i < results.length),
      retreated.regs (resultReg control i) = sourceCallee.eval results[i] := by
    intro i hi
    exact (retreatLocals_resultReg control locals buffered i).trans
      (hb.source_values hmatch hbounded hreads i hi)
  have hrMem : retreated.mem = start.mem := hb.memory
  have haSP : addressed.regs (sp control) = baseWord := by
    have hne : sp control ≠ ra control := by simp [sp, ra]
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hrSP
  have haValues : ∀ (i : Nat) (hi : i < results.length),
      addressed.regs (resultReg control i) = sourceCallee.eval results[i] := by
    intro i hi
    have hne : resultReg control i ≠ ra control := by
      cases i with
      | zero =>
          change control + 1 ≠ control + 2
          omega
      | succ i =>
          change control + 5 + i ≠ control + 2
          omega
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using
      hrValues i hi
  have haReturn : addressed.regs (ra control) = returnWord := by
    simp only [addressed, execInstr, State.next_regs, State.setReg_same]
    rw [hrSP, hrMem]
    exact hreturn
  have haMem : addressed.mem = start.mem := hb.memory
  have haInput : addressed.input = start.input := hb.input
  have haOutput : addressed.outputRev = start.outputRev := hb.output
  have haStatus : addressed.status = start.status := hb.status
  have haAbove : RegsPreservedAbove control locals start addressed := by
    intro r _ hhi
    have hrSP : r ≠ sp control := by unfold sp; omega
    have hrTmp : r ≠ tmp control := by unfold tmp; omega
    have hrRA : r ≠ ra control := by unfold ra; omega
    have hr : retreated.regs r = start.regs r :=
      (retreatLocals_regs control locals buffered r hrSP hrTmp).trans (hb.locals r hhi)
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hrRA] using hr
  have haFrame : FrameSaved locals (addressed.regs (sp control)) savedRegs addressed.mem := by
    rw [haSP, haMem]
    exact hframe
  have hfinish : execBlock (returnPrefixResultsLocals control locals results) start =
      execBlock (restoreLocals control locals) addressed := by
    simp only [returnPrefixResultsLocals, execBlock_append, execBlock_cons, execBlock_nil]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    execBlock_pc _ start (returnPrefixResultsLocals_linear control locals results)⟩
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
  · intro i hi
    rw [hfinish]
    exact (restoreLocals_resultReg addressed hlocals i).trans (haValues i hi)
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

/-- The restored address controls the same indirect-jump instruction for any
return arity, including an empty result list. -/
theorem ReturnResultsRestoredLocals.jump_step {code : Code} {control locals returnPC : Nat}
    {results : List Expr} {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start finish : State w}
    (h : ReturnResultsRestoredLocals control locals results sourceCallee savedRegs
      baseWord returnWord start finish)
    (hrun : start.status = .running)
    (hfetch : code[finish.pc]? = some (.jumpReg (ra control)))
    (hreturnPC : returnWord.toNat = returnPC) :
    step code finish = some (finish.atPC returnPC) := by
  have hs := step_of_fetch (h.status.trans hrun) hfetch
  simpa only [execInstr, h.address, hreturnPC, State.atPC] using hs

/-- Execute the return prefix and its fetched indirect jump, charging exactly
the actual emitted code length. -/
theorem returnCodeResultsLocals_exec {code : Code} {control locals returnPC : Nat}
    {results : List Expr} {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (h : ReturnResultsRestoredLocals control locals results sourceCallee savedRegs
      baseWord returnWord start
      (execBlock (returnPrefixResultsLocals control locals results) start))
    (hcode : CodeAt code start.pc (returnCodeResultsLocals control locals results))
    (hrun : start.status = .running) (hreturnPC : returnWord.toNat = returnPC) :
    Exec code (returnCodeResultsLocals control locals results).length start
      ((execBlock (returnPrefixResultsLocals control locals results) start).atPC returnPC) := by
  change CodeAt code start.pc
    (returnPrefixResultsLocals control locals results ++ [.jumpReg (ra control)]) at hcode
  have hp := returnPrefixResultsLocals_exec hcode.append_left hrun
  have hfetch : code[(execBlock (returnPrefixResultsLocals control locals results) start).pc]? =
      some (.jumpReg (ra control)) := by
    rw [h.pc]
    exact hcode.append_right.head
  have hj := Exec.single (h.jump_step hrun hfetch hreturnPC)
  simpa only [returnCodeResultsLocals, List.length_append, List.length_singleton] using hp.trans hj

end Ram.ABI
