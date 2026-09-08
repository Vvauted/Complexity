/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic
import Complexity.Computability.Ram.Compiler.Program

/-!
# Complete checked executables for the callee-local compiler

The closed local-frame simulation is started after one real stack-header
read and followed by one real halt instruction. The complete exact count is
therefore the source's compiler-derived count plus two. No unproved call
simulation premise is retained, including for recursive programs.

The current stack-fit hypothesis is a sufficient global-depth bound; actual
frame sizes and execution counts still use each callee's own local bound.
The source-visible heap is carried all the way to the halted machine state.
-/

namespace Ram.LocalCompiler

/-- The prologue is unchanged: reuse its already defined concrete machine
state, including the consumed header and zero-initialized source registers. -/
abbrev mainStart (control heapLimit : Nat) (input : List (Word w)) : State w :=
  Compiler.mainStart control heapLimit input

@[simp] theorem mainStart_pc (control heapLimit : Nat) (input : List (Word w)) :
    (mainStart control heapLimit input).pc = 1 := Compiler.mainStart_pc _ _ _

@[simp] theorem mainStart_sp (control heapLimit : Nat) (input : List (Word w)) :
    (mainStart control heapLimit input).regs (ABI.sp control) = BitVec.ofNat w heapLimit :=
  Compiler.mainStart_sp _ _ _

@[simp] theorem mainStart_input (control heapLimit : Nat) (input : List (Word w)) :
    (mainStart control heapLimit input).input = input := rfl

theorem mainStart_matches (control heapLimit : Nat) (input : List (Word w)) :
    Source.State.Matches heapLimit control (Source.State.initial input)
      (mainStart control heapLimit input) := Compiler.mainStart_matches _ _ _

/-- The new linked program performs the same header read, at its actual
instruction zero; this is not an external uncounted initialization. -/
theorem prologue_exec (control : Nat) (program : Program) (main : Stmt)
    (heapLimit : Nat) (input : List (Word w)) :
    Exec (rawLink control program main) 1
      (State.initial (BitVec.ofNat w heapLimit :: input))
      (mainStart control heapLimit input) :=
  Exec.single (step_of_fetch rfl (rawLink_prologue control program main))

/-- Execute the main block using the closed recursive-call simulation and its
exact local-frame instruction count. -/
theorem main_run_measured {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    StatementRunExact control control heapLimit (rawLink control program main)
      (calleeLocals program) (entry control program main) main steps sourceFinal
      (mainStart control heapLimit input) := by
  have hh : heapLimit < 2 ^ w := by omega
  have hsp : ((mainStart control heapLimit input).regs (ABI.sp control)).toNat =
      heapLimit := by
    rw [mainStart_sp, Word.ofNat_toNat_of_lt hh]
  apply simulate_measured hvalid hcodefit hx hvalid.1 (Nat.le_refl control)
    (mainStart control heapLimit input) (mainStart_matches control heapLimit input)
  · simpa only [hsp] using Nat.le_refl heapLimit
  · change ((mainStart control heapLimit input).regs (ABI.sp control)).toNat +
      depth * ABI.frameSize control < 2 ^ w
    rw [hsp]
    exact hstackfit
  · simpa only [mainStart_pc] using rawLink_main control program main

/-- Exact execution of the entire linked program, retaining its source heap
and I/O observations after the actual final halt transition. -/
theorem rawLink_runs_measured_heap {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec (rawLink control program main) steps (mainStart control heapLimit input) bodyFinish ∧
      Exec (rawLink control program main) (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      HeapEqBelow heapLimit sourceFinal.mem (execInstr .halt bodyFinish).mem ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨bodyFinish, hbody, hmatch, _, _, hpc⟩ :=
    main_run_measured hvalid hcodefit hstackfit hx
  have hfetch : (rawLink control program main)[bodyFinish.pc]? = some .halt := by
    rw [hpc, mainStart_pc]
    exact rawLink_halt control program main
  have hhalt : Exec (rawLink control program main) 1 bodyFinish (execInstr .halt bodyFinish) :=
    Exec.single (step_of_fetch hmatch.running hfetch)
  have hfull := ((prologue_exec control program main heapLimit input).trans hbody).trans hhalt
  refine ⟨bodyFinish, hbody, ?_, rfl, hmatch.heap, ?_, hmatch.input.symm⟩
  · have hcount : 1 + steps + 1 = steps + 2 := by omega
    simpa only [hcount] using hfull
  · change bodyFinish.outputRev.reverse = sourceFinal.outputRev.reverse
    exact congrArg List.reverse hmatch.output.symm

/-- I/O-only projection for clients that do not observe the final heap. -/
theorem rawLink_runs_measured {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec (rawLink control program main) steps (mainStart control heapLimit input) bodyFinish ∧
      Exec (rawLink control program main) (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨finish, hbody, hfull, halt, _, hout, hin⟩ :=
    rawLink_runs_measured_heap hvalid hcodefit hstackfit hx
  exact ⟨finish, hbody, hfull, halt, hout, hin⟩

/-- The checked entry point derives static validity from successful
compilation. All runtime observations refer to the same halted target state. -/
theorem compileChecked_runs_measured_heap {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec code steps (mainStart control heapLimit input) bodyFinish ∧
      Exec code (steps + 2) (State.initial (BitVec.ofNat w heapLimit :: input))
        (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      HeapEqBelow heapLimit sourceFinal.mem (execInstr .halt bodyFinish).mem ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_runs_measured_heap hvalid hcodefit hstackfit hx

theorem compileChecked_runs_measured {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec code steps (mainStart control heapLimit input) bodyFinish ∧
      Exec code (steps + 2) (State.initial (BitVec.ofNat w heapLimit :: input))
        (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_runs_measured hvalid hcodefit hstackfit hx

/-- A source-derived budget becomes a real machine termination bound,
including header read and halt, with the source-visible heap retained. -/
theorem compileChecked_terminatesWithin_heap {control heapLimit depth steps budget : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal)
    (hbudget : steps + 2 ≤ budget) :
    ∃ finish, TerminatesWithin code budget
        (State.initial (BitVec.ofNat w heapLimit :: input)) finish ∧
      HeapEqBelow heapLimit sourceFinal.mem finish.mem ∧
      finish.output = sourceFinal.output ∧ finish.input = sourceFinal.input := by
  obtain ⟨bodyFinish, _, hfull, halt, heap, hout, hin⟩ :=
    compileChecked_runs_measured_heap hcompile hcodefit hstackfit hx
  exact ⟨_, ⟨steps + 2, hbudget, hfull, halt⟩, heap, hout, hin⟩

theorem compileChecked_terminatesWithin {control heapLimit depth steps budget : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal)
    (hbudget : steps + 2 ≤ budget) :
    ∃ finish, TerminatesWithin code budget
        (State.initial (BitVec.ofNat w heapLimit :: input)) finish ∧
      finish.output = sourceFinal.output ∧ finish.input = sourceFinal.input := by
  obtain ⟨finish, ht, _, hout, hin⟩ :=
    compileChecked_terminatesWithin_heap hcompile hcodefit hstackfit hx hbudget
  exact ⟨finish, ht, hout, hin⟩

end Ram.LocalCompiler
