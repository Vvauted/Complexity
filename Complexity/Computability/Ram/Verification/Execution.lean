/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Contract

/-!
# Source-visible observations of a completed machine execution

The compiler relates source registers only below the declared local bound and
source memory only below the heap boundary. Its stack pointer, scratch
registers, and private stack words are not part of that agreement.

`Source.State.Observes` retains those data observations without requiring the
machine to be running. The complete-execution theorems therefore expose local
register results on the same halted state as the heap and I/O results, while
preserving the existing compiler and contract APIs.
-/

namespace Ram.Source.State

/-- Data agreement with a target state, independent of its execution status. -/
structure Observes (heapLimit locals : Nat) (s : Source.State w) (t : Ram.State w) : Prop where
  regs : ∀ r, r < locals → s.regs r = t.regs r
  heap : HeapEqBelow heapLimit s.mem t.mem
  input : s.input = t.input
  output : s.outputRev = t.outputRev

/-- Forgetting the running-state requirement retains all visible data. -/
theorem Matches.observes {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) : Observes heapLimit locals s t :=
  ⟨h.regs, h.heap, h.input, h.output⟩

/-- The actual halt instruction changes status, not the observed data. -/
theorem Observes.halt {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Observes heapLimit locals s t) : Observes heapLimit locals s (execInstr .halt t) :=
  ⟨h.regs, h.heap, h.input, h.output⟩

theorem Observes.output_eq {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Observes heapLimit locals s t) : t.output = s.output :=
  congrArg List.reverse h.output.symm

end Ram.Source.State

namespace Ram.LocalCompiler

/-- Execute a checked main block from a matching preloaded state at PC 1,
including its actual halt. No input-loading or prologue transition is assumed
to have happened for free: the theorem explicitly starts after that prologue.
Recursive calls use the same stack-fit condition as ordinary simulation. -/
theorem compileChecked_block_runs_observed {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code}
    {sourceStart sourceFinal : Source.State w} {start : State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      sourceStart sourceFinal)
    (hmatch : Source.State.Matches heapLimit control sourceStart start)
    (hpc : start.pc = 1)
    (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hstackfit : Compiler.StackFits control depth start) :
    ∃ finish, Exec code (steps + 1) start finish ∧ finish.status = .halted ∧
      Source.State.Observes heapLimit control sourceFinal finish ∧
      FramePreserved control heapLimit start finish := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  have hcode : CodeAt (rawLink control program main) start.pc
      (compileStmt control (calleeLocals program) (entry control program main)
        main start.pc) := by
    rw [hpc]
    exact rawLink_main control program main
  obtain ⟨bodyFinish, he, hm, hf, _, hp⟩ :=
    simulate_measured hvalid hcodefit hx hvalid.1 (Nat.le_refl control)
      start hmatch hheap hstackfit hcode
  have hfetch : (rawLink control program main)[bodyFinish.pc]? = some .halt := by
    rw [hp, hpc]
    exact rawLink_halt control program main
  have hhalt : Exec (rawLink control program main) 1 bodyFinish (execInstr .halt bodyFinish) :=
    Exec.single (step_of_fetch hm.running hfetch)
  exact ⟨execInstr .halt bodyFinish, he.trans hhalt, rfl, hm.observes.halt,
    ⟨hf.sp, hf.older⟩⟩

/-- Checked compilation retains the local registers, heap, and I/O after the
complete execution, including the actual prologue and halt transitions. -/
theorem compileChecked_runs_observed {control heapLimit depth steps : Nat}
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
      Source.State.Observes heapLimit control sourceFinal (execInstr .halt bodyFinish) := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  obtain ⟨bodyFinish, hbody, hmatch, _, _, hpc⟩ :=
    main_run_measured hvalid hcodefit hstackfit hx
  have hfetch : (rawLink control program main)[bodyFinish.pc]? = some .halt := by
    rw [hpc, mainStart_pc]
    exact rawLink_halt control program main
  have hhalt : Exec (rawLink control program main) 1 bodyFinish (execInstr .halt bodyFinish) :=
    Exec.single (step_of_fetch hmatch.running hfetch)
  have hfull := ((prologue_exec control program main heapLimit input).trans hbody).trans hhalt
  refine ⟨bodyFinish, hbody, ?_, rfl, hmatch.observes.halt⟩
  have hcount : 1 + steps + 1 = steps + 2 := by omega
  simpa only [hcount] using hfull

/-- A body budget yields a whole-program termination bound without discarding
the register observations needed to state the result directly on the machine. -/
theorem compileChecked_terminatesWithin_observed
    {control heapLimit depth steps budget : Nat}
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
      Source.State.Observes heapLimit control sourceFinal finish := by
  obtain ⟨bodyFinish, _, hfull, hhalt, hobs⟩ :=
    compileChecked_runs_observed hcompile hcodefit hstackfit hx
  exact ⟨_, ⟨steps + 2, hbudget, hfull, hhalt⟩, hobs⟩

end Ram.LocalCompiler

namespace Ram.Source.Contract

/-- Transfer a source contract to the actual halted machine state, retaining
the declared local-register prefix as well as the source heap and I/O. -/
theorem compile_observed {w n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat} {code : Code} {input : List (Word w)}
    (h : Contract n program heapLimit depth stmt P Q bound)
    (hcompile : LocalCompiler.compileChecked n program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal, Q sourceFinal ∧
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) targetFinal ∧
      State.Observes heapLimit n sourceFinal targetFinal := by
  obtain ⟨steps, sourceFinal, hx, hq, hb⟩ := h (State.initial input) hp
  obtain ⟨targetFinal, ht, hobs⟩ := LocalCompiler.compileChecked_terminatesWithin_observed
    hcompile hcodefit hstackfit hx (Nat.add_le_add_right hb 2)
  exact ⟨sourceFinal, targetFinal, hq, ht, hobs⟩

end Ram.Source.Contract

namespace Ram.Source.RelContract

/-- Export an entry-related contract to a preloaded checked main block and its
halt. The postcondition, local registers, heap, I/O and older stack words are
all witnessed by the same terminating run; the budget adds exactly one halt. -/
theorem compile_block_observed {w n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop} {bound : State w → Nat}
    {code : Code} {sourceStart : State w} {start : Ram.State w}
    (h : RelContract n program heapLimit depth stmt P Q bound)
    (hcompile : LocalCompiler.compileChecked n program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hp : P sourceStart)
    (hmatch : State.Matches heapLimit n sourceStart start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp n)).toNat)
    (hstackfit : Compiler.StackFits n depth start) :
    ∃ sourceFinal finish,
      Ram.TerminatesWithin code (bound sourceStart + 1) start finish ∧
      Q sourceStart sourceFinal ∧ State.Observes heapLimit n sourceFinal finish ∧
      FramePreserved n heapLimit start finish := by
  obtain ⟨steps, sourceFinal, hx, hq, hb⟩ := h sourceStart hp
  obtain ⟨finish, he, hh, ho, hf⟩ := LocalCompiler.compileChecked_block_runs_observed
    hcompile hcodefit hx hmatch hpc hheap hstackfit
  exact ⟨sourceFinal, finish, ⟨steps + 1, Nat.add_le_add_right hb 1, he, hh⟩, hq, ho, hf⟩

end Ram.Source.RelContract
