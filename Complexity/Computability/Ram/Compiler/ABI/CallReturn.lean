/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Basic
import Complexity.Computability.Ram.Compiler.Effects
import Complexity.Computability.Ram.Compiler.Local.Call.Results

/-!
# Returning from a compiled function

The return prefix evaluates the result before restoring caller locals, then
subtracts the concrete frame size from SP, loads the saved return address, and
restores each saved local separately. No source return operation or bulk frame
restoration is assigned a cost. The execution theorem counts the emitted RAM
instructions, including the final indirect jump.
-/

namespace Ram.ABI

private theorem return_scratch_bound (n : Nat) : n ≤ scratch n := by
  change n ≤ 2 * n + 5
  omega

private theorem return_sp_lt_scratch (n : Nat) : sp n < scratch n := by
  change n < 2 * n + 5
  omega

private theorem return_retreat_linear (n : Nat) : ∀ i ∈ retreat n, i.Linear := by
  simp [retreat, Instr.Linear]

private theorem return_retreat_regs (n : Nat) (s : State w) (r : Reg)
    (hs : r ≠ sp n) (ht : r ≠ tmp n) :
    (execBlock (retreat n) s).regs r = s.regs r := by
  simp [retreat, execBlock, execInstr, State.setReg, State.next, hs, ht]

/-- Recover the exact old SP from a non-wrapping frame increment. The proof
uses the actual word subtraction result, not natural subtraction by fiat. -/
private theorem return_retreat_sp {n : Nat} (s : State w) (base : Word w)
    (hsp : (s.regs (sp n)).toNat = base.toNat + frameSize n)
    (hfit : base.toNat + frameSize n < 2 ^ w) :
    (execBlock (retreat n) s).regs (sp n) = base := by
  have hc : (BitVec.ofNat w (frameSize n)).toNat = frameSize n :=
    Word.ofNat_toNat_of_lt
      (Nat.lt_of_le_of_lt (Nat.le_add_left (frameSize n) base.toNat) hfit)
  have hle :
      (BitVec.ofNat w (frameSize n)).toNat ≤ (s.regs (sp n)).toNat := by
    rw [hc, hsp]
    exact Nat.le_add_left _ _
  have hv :
      BinOp.eval .sub (s.regs (sp n)) (BitVec.ofNat w (frameSize n)) = base := by
    apply BitVec.eq_of_toNat_eq
    rw [BinOp.eval_sub_toNat_of_le _ _ hle, hc, hsp, Nat.add_sub_cancel]
  have hst : sp n ≠ tmp n := by simp [sp, tmp]
  simpa [retreat, execBlock, execInstr, State.setReg, State.next, hst] using hv

/-- The caller frame and result after the prefix, immediately before jumping
to the saved return address. `start` is the callee's final-body state. -/
structure ReturnRestored (n : Nat) (result : Expr) (sourceCallee : Source.State w)
    (savedRegs : Reg → Word w) (baseWord returnWord : Word w)
    (start finish : State w) : Prop where
  sp : finish.regs (ABI.sp n) = baseWord
  locals : ∀ i, i < n → finish.regs i = savedRegs i
  value : finish.regs (rv n) = sourceCallee.eval result
  address : finish.regs (ra n) = returnWord
  memory : finish.mem = start.mem
  input : finish.input = start.input
  output : finish.outputRev = start.outputRev
  status : finish.status = start.status
  pc : finish.pc = start.pc + (returnPrefix n result).length

theorem returnPrefix_linear (n : Nat) (result : Expr) :
    ∀ i ∈ returnPrefix n result, i.Linear := by
  intro i hi
  simp only [returnPrefix, returnPrefixResults, evalResults_singleton,
    List.mem_append, List.mem_singleton] at hi
  rcases hi with (((he | rfl) | ht) | rfl) | hl
  · exact result.compile_linear (scratch n) i he
  · trivial
  · exact return_retreat_linear n i ht
  · trivial
  · exact restoreLocals_linear n n i hl

/-- The return prefix preserves the callee's heap and I/O while restoring the
saved caller register frame and retaining the correctly computed result. -/
theorem returnPrefix_correct {n heapLimit : Nat} {result : Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (hmatch : sourceCallee.Matches heapLimit n start)
    (hbounded : result.Bounded n)
    (hreads : result.ReadsBelow heapLimit sourceCallee.regs sourceCallee.mem)
    (hfit : baseWord.toNat + frameSize n < 2 ^ w)
    (hsp : (start.regs (sp n)).toNat = baseWord.toNat + frameSize n)
    (hframe : FrameSaved n baseWord savedRegs start.mem)
    (hreturn : start.mem baseWord = returnWord) :
    ReturnRestored n result sourceCallee savedRegs baseWord returnWord start
      (execBlock (returnPrefix n result) start) := by
  let evaluated := execBlock (result.compile (scratch n)) start
  let buffered := execInstr (.move (rv n) (scratch n)) evaluated
  let retreated := execBlock (retreat n) buffered
  let addressed := execInstr (.load (ra n) (sp n)) retreated
  have hc := Expr.compile_correct (hbounded.mono (return_scratch_bound n)) start
  have heSP : evaluated.regs (sp n) = start.regs (sp n) :=
    hc.below (sp n) (return_sp_lt_scratch n)
  have hbSP : buffered.regs (sp n) = start.regs (sp n) := by
    have hne : sp n ≠ rv n := by simp [sp, rv]
    simpa only [buffered, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using heSP
  have hbValue : buffered.regs (rv n) = sourceCallee.eval result := by
    simpa only [buffered, execInstr, State.next_regs, State.setReg_same] using
      hc.value.trans (hmatch.eval_eq hbounded hreads).symm
  have hrSP : retreated.regs (sp n) = baseWord :=
    return_retreat_sp buffered baseWord (by rw [hbSP]; exact hsp) hfit
  have hrValue : retreated.regs (rv n) = sourceCallee.eval result :=
    (return_retreat_regs n buffered (rv n) (by simp [rv, sp])
      (by simp [rv, tmp])).trans hbValue
  have hrMem : retreated.mem = start.mem := hc.memory
  have haSP : addressed.regs (sp n) = baseWord := by
    have hne : sp n ≠ ra n := by simp [sp, ra]
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hrSP
  have haValue : addressed.regs (rv n) = sourceCallee.eval result := by
    have hne : rv n ≠ ra n := by simp [rv, ra]
    simpa only [addressed, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hrValue
  have haReturn : addressed.regs (ra n) = returnWord := by
    simp only [addressed, execInstr, State.next_regs, State.setReg_same]
    rw [hrSP, hrMem]
    exact hreturn
  have haMem : addressed.mem = start.mem := hc.memory
  have haInput : addressed.input = start.input := hc.input
  have haOutput : addressed.outputRev = start.outputRev := hc.output
  have haStatus : addressed.status = start.status := hc.status
  have haFrame : FrameSaved n (addressed.regs (sp n)) savedRegs addressed.mem := by
    rw [haSP, haMem]
    exact hframe
  have hfinish : execBlock (returnPrefix n result) start =
      execBlock (restoreLocals n n) addressed := by
    simp only [returnPrefix, returnPrefixResults, evalResults_singleton,
      execBlock_append, execBlock_cons, execBlock_nil]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    execBlock_pc _ start (returnPrefix_linear n result)⟩
  · rw [hfinish]
    exact (restoreLocals_sp addressed (Nat.le_refl n)).trans haSP
  · rw [hfinish]
    exact restoreLocals_frame addressed (Nat.le_refl n) savedRegs haFrame
  · rw [hfinish]
    exact (restoreLocals_rv addressed (Nat.le_refl n)).trans haValue
  · rw [hfinish]
    exact (restoreLocals_ra addressed (Nat.le_refl n)).trans haReturn
  · rw [hfinish]
    exact (restoreLocals_mem n n addressed).trans haMem
  · rw [hfinish]
    exact (restoreLocals_input n n addressed).trans haInput
  · rw [hfinish]
    exact (restoreLocals_output n n addressed).trans haOutput
  · rw [hfinish]
    exact (restoreLocals_status n n addressed).trans haStatus

/-- The restoration prefix executes exactly the generated instruction block. -/
theorem returnPrefix_exec {code : Code} {n : Nat} {result : Expr} {start : State w}
    (hcode : CodeAt code start.pc (returnPrefix n result))
    (hrun : start.status = .running) :
    Exec code (returnPrefix n result).length start (execBlock (returnPrefix n result) start) :=
  execBlock_exec hcode (returnPrefix_linear n result) hrun

/-- The saved address is used by the actual indirect-jump instruction. -/
theorem ReturnRestored.jump_step {code : Code} {n returnPC : Nat} {result : Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start finish : State w}
    (h : ReturnRestored n result sourceCallee savedRegs baseWord returnWord start finish)
    (hrun : start.status = .running)
    (hfetch : code[finish.pc]? = some (.jumpReg (ra n)))
    (hreturnPC : returnWord.toNat = returnPC) :
    step code finish = some (finish.atPC returnPC) := by
  have hs := step_of_fetch (h.status.trans hrun) hfetch
  simpa only [execInstr, h.address, hreturnPC, State.atPC] using hs

/-- The complete return code reaches the decoded saved return PC. Its count
includes the final indirect jump and is the length of the emitted return code. -/
theorem returnCode_exec {code : Code} {n returnPC : Nat} {result : Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (h : ReturnRestored n result sourceCallee savedRegs baseWord returnWord start
      (execBlock (returnPrefix n result) start))
    (hcode : CodeAt code start.pc (returnCode n result))
    (hrun : start.status = .running) (hreturnPC : returnWord.toNat = returnPC) :
    Exec code (returnCode n result).length start
      ((execBlock (returnPrefix n result) start).atPC returnPC) := by
  change CodeAt code start.pc (returnPrefix n result ++ [.jumpReg (ra n)]) at hcode
  have hp := returnPrefix_exec hcode.append_left hrun
  have hfetch : code[(execBlock (returnPrefix n result) start).pc]? = some (.jumpReg (ra n)) := by
    rw [h.pc]
    exact hcode.append_right.head
  have hj := Exec.single (h.jump_step hrun hfetch hreturnPC)
  simpa only [returnCode, List.length_append, List.length_singleton] using hp.trans hj

/-- The global-frame return is the callee-sized return with both bounds equal.
Every result is evaluated before restoring caller locals, including when the
result list is empty or two result expressions use the same callee register. -/
theorem returnPrefixResults_correct {n heapLimit : Nat} {results : List Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (hmatch : sourceCallee.Matches heapLimit n start)
    (hfitResults : results.length - 1 ≤ n)
    (hbounded : ∀ e ∈ results, e.Bounded n)
    (hreads : ∀ e ∈ results, e.ReadsBelow heapLimit sourceCallee.regs sourceCallee.mem)
    (hfit : baseWord.toNat + frameSize n < 2 ^ w)
    (hsp : (start.regs (sp n)).toNat = baseWord.toNat + frameSize n)
    (hframe : FrameSaved n baseWord savedRegs start.mem)
    (hreturn : start.mem baseWord = returnWord) :
    ReturnResultsRestoredLocals n n results sourceCallee savedRegs baseWord returnWord start
      (execBlock (returnPrefixResults n results) start) :=
  returnPrefixResultsLocals_correct (Nat.le_refl n) hmatch hfitResults hbounded hreads
    hfit hsp hframe hreturn

/-- Execute the global multi-result return, including its actual indirect jump,
by specializing the verified callee-sized return execution. -/
theorem returnCodeResults_exec {code : Code} {n returnPC : Nat} {results : List Expr}
    {sourceCallee : Source.State w} {savedRegs : Reg → Word w}
    {baseWord returnWord : Word w} {start : State w}
    (h : ReturnResultsRestoredLocals n n results sourceCallee savedRegs
      baseWord returnWord start (execBlock (returnPrefixResults n results) start))
    (hcode : CodeAt code start.pc (returnCodeResults n results))
    (hrun : start.status = .running) (hreturnPC : returnWord.toNat = returnPC) :
    Exec code (returnCodeResults n results).length start
      ((execBlock (returnPrefixResults n results) start).atPC returnPC) :=
  returnCodeResultsLocals_exec h hcode hrun hreturnPC

end Ram.ABI
