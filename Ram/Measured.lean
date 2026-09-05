import Ram.Program

/-!
# Compositional source judgments with exact compiled execution counts

`MeasuredExec` records the same computations and safety premises as `SafeExec`.
Its count is fixed by generated instruction blocks and executed subderivations;
there are no user-supplied ticks, operation prices, or opaque host computations.
The count is an index of a proposition, not a function extracted from a proof
of `SafeExec`. Every safe execution has such an indexed derivation.

The simulation theorem connects each constructor to the already proved exact
machine-execution rules, including recursive calls through the concrete ABI.
Whole-program bounds consequently refer to actual `Ram.Exec` transitions.
-/

namespace Ram.Source

/-- Source execution indexed by its compiler-derived exact machine step count.
The depth index bounds nested calls, independently of the transition count. -/
inductive MeasuredExec (n : Nat) (program : Program) (heapLimit : Nat) {w : Nat} :
    Nat → Stmt → Nat → State w → State w → Prop where
  | skip : MeasuredExec n program heapLimit d .skip 0 s s
  | assign (reads : value.ReadsBelow heapLimit s.regs s.mem) :
      MeasuredExec n program heapLimit d (.assign dst value)
        (Compiler.stmtSize n (.assign dst value)) s (s.setReg dst (s.eval value))
  | store (addressReads : address.ReadsBelow heapLimit s.regs s.mem)
      (valueReads : value.ReadsBelow heapLimit s.regs s.mem)
      (destination : (s.eval address).toNat < heapLimit) :
      MeasuredExec n program heapLimit d (.store address value)
        (Compiler.stmtSize n (.store address value)) s
        (s.setMem (s.eval address) (s.eval value))
  | seq (first : MeasuredExec n program heapLimit d a na s middle)
      (second : MeasuredExec n program heapLimit d b nb middle t) :
      MeasuredExec n program heapLimit d (.seq a b) (na + nb) s t
  | iteTrue (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c ≠ 0)
      (body : MeasuredExec n program heapLimit d yes nb s t) :
      MeasuredExec n program heapLimit d (.ite c yes no)
        ((c.compile (ABI.scratch n)).length + 1 + nb + 1) s t
  | iteFalse (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c = 0)
      (body : MeasuredExec n program heapLimit d no nb s t) :
      MeasuredExec n program heapLimit d (.ite c yes no)
        ((c.compile (ABI.scratch n)).length + 1 + nb) s t
  | whileFalse (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c = 0) :
      MeasuredExec n program heapLimit d (.while c body)
        ((c.compile (ABI.scratch n)).length + 1) s s
  | whileTrue (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c ≠ 0)
      (body : MeasuredExec n program heapLimit d b nb s middle)
      (rest : MeasuredExec n program heapLimit d (.while c b) nr middle t) :
      MeasuredExec n program heapLimit d (.while c b)
        ((c.compile (ABI.scratch n)).length + 1 + nb + 1 + nr) s t
  | read (available : s.input = value :: rest) :
      MeasuredExec n program heapLimit d (.read dst)
        (Compiler.stmtSize n (.read dst)) s
        { s.setReg dst value with input := rest }
  | write (reads : value.ReadsBelow heapLimit s.regs s.mem) :
      MeasuredExec n program heapLimit d (.write value)
        (Compiler.stmtSize n (.write value)) s
        { s with outputRev := s.eval value :: s.outputRev }
  | call (lookup : program[fn]? = some f) (arity : args.length = f.params)
      (frame : f.params ≤ f.locals)
      (arguments : ∀ arg ∈ args, arg.ReadsBelow heapLimit s.regs s.mem)
      (body : MeasuredExec n program heapLimit d f.body bodySteps
        (s.enter (args.map s.eval)) callee)
      (result : f.result.ReadsBelow heapLimit callee.regs callee.mem) :
      MeasuredExec n program heapLimit (d + 1) (.call dst fn args)
        ((ABI.callPrefix n args 0).length + 1 + bodySteps +
          (ABI.returnCode n f.result).length + 1)
        s (s.leave callee dst f.result)

namespace MeasuredExec

/-- Forgetting the count preserves all source semantics and safety guarantees. -/
theorem erase {n heapLimit depth steps : Nat} {program : Program} {stmt : Stmt}
    {s t : State w} (h : MeasuredExec n program heapLimit depth stmt steps s t) :
    SafeExec program heapLimit depth stmt s t := by
  induction h with
  | skip => exact .skip
  | assign reads => exact .assign reads
  | store addressReads valueReads destination =>
      exact .store addressReads valueReads destination
  | seq _ _ first second => exact .seq first second
  | iteTrue reads condition _ body => exact .iteTrue reads condition body
  | iteFalse reads condition _ body => exact .iteFalse reads condition body
  | whileFalse reads condition => exact .whileFalse reads condition
  | whileTrue reads condition _ _ body rest =>
      exact .whileTrue reads condition body rest
  | read available => exact .read available
  | write reads => exact .write reads
  | call lookup arity frame arguments _ result body =>
      exact .call lookup arity frame arguments body result

/-- Increasing the allowed call depth does not change the measured execution. -/
theorem depth_add {n heapLimit depth steps : Nat} {program : Program} {stmt : Stmt}
    {s t : State w} (h : MeasuredExec n program heapLimit depth stmt steps s t)
    (extra : Nat) : MeasuredExec n program heapLimit (depth + extra) stmt steps s t := by
  induction h with
  | skip => exact .skip
  | assign reads => exact .assign reads
  | store addressReads valueReads destination =>
      exact .store addressReads valueReads destination
  | seq _ _ first second => exact .seq first second
  | iteTrue reads condition _ body => exact .iteTrue reads condition body
  | iteFalse reads condition _ body => exact .iteFalse reads condition body
  | whileFalse reads condition => exact .whileFalse reads condition
  | whileTrue reads condition _ _ body rest =>
      exact .whileTrue reads condition body rest
  | read available => exact .read available
  | write reads => exact .write reads
  | call lookup arity frame arguments _ result body =>
      simpa only [Nat.add_right_comm _ 1 extra] using
        (MeasuredExec.call lookup arity frame arguments body result)

theorem mono {n heapLimit depth depth' steps : Nat} {program : Program} {stmt : Stmt}
    {s t : State w} (h : MeasuredExec n program heapLimit depth stmt steps s t)
    (hle : depth ≤ depth') : MeasuredExec n program heapLimit depth' stmt steps s t := by
  have h' := h.depth_add (depth' - depth)
  simpa only [Nat.add_sub_of_le hle] using h'

end MeasuredExec

/-- Every safe source execution has a compiler-derived count. Both the premise
and the existential conclusion are propositions; no proof is eliminated into a
runtime natural number. -/
theorem SafeExec.exists_measured {program : Program} {heapLimit depth : Nat}
    {stmt : Stmt} {s t : State w}
    (h : SafeExec program heapLimit depth stmt s t) (n : Nat) :
    ∃ steps, MeasuredExec n program heapLimit depth stmt steps s t := by
  induction h with
  | skip => exact ⟨_, .skip⟩
  | assign reads => exact ⟨_, .assign reads⟩
  | store addressReads valueReads destination =>
      exact ⟨_, .store addressReads valueReads destination⟩
  | seq _ _ first second =>
      obtain ⟨na, ha⟩ := first
      obtain ⟨nb, hb⟩ := second
      exact ⟨_, .seq ha hb⟩
  | iteTrue reads condition _ body =>
      obtain ⟨nb, hb⟩ := body
      exact ⟨_, .iteTrue reads condition hb⟩
  | iteFalse reads condition _ body =>
      obtain ⟨nb, hb⟩ := body
      exact ⟨_, .iteFalse reads condition hb⟩
  | whileFalse reads condition => exact ⟨_, .whileFalse reads condition⟩
  | whileTrue reads condition _ _ body rest =>
      obtain ⟨nb, hb⟩ := body
      obtain ⟨nr, hr⟩ := rest
      exact ⟨_, .whileTrue reads condition hb hr⟩
  | read available => exact ⟨_, .read available⟩
  | write reads => exact ⟨_, .write reads⟩
  | call lookup arity frame arguments _ result body =>
      obtain ⟨nb, hb⟩ := body
      exact ⟨_, .call lookup arity frame arguments hb result⟩

theorem measured_iff_safe {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {s t : State w} :
    (∃ steps, MeasuredExec n program heapLimit depth stmt steps s t) ↔
      SafeExec program heapLimit depth stmt s t :=
  ⟨fun ⟨_, h⟩ => h.erase, fun h => h.exists_measured n⟩

end Ram.Source

namespace Ram.Compiler

/-- Every measured constructor refines to the same exact number of actual RAM
transitions. Recursive bodies use the induction hypothesis directly; there is
no outstanding call-simulation premise. -/
theorem simulate_measured {n heapLimit depth steps : Nat} {program : Program}
    {main stmt : Stmt} {s s' : Source.State w} (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hx : Source.MeasuredExec n program heapLimit depth stmt steps s s')
    (hwf : stmt.WellFormed n) :
    SimulationExact n heapLimit (rawLink n program main) (entry n program main)
      depth stmt steps s s' := by
  induction hx with
  | skip => exact simulation_skip_exact
  | assign reads => exact simulation_assign_exact hwf reads
  | store addressReads valueReads destination =>
      exact simulation_store_exact hwf addressReads valueReads destination
  | seq _ _ first second => exact simulation_seq_exact (first hwf.1) (second hwf.2)
  | iteTrue reads condition _ body =>
      exact simulation_iteTrue_exact hwf.1 reads condition (body hwf.2.1)
  | iteFalse reads condition _ body =>
      exact simulation_iteFalse_exact hwf.1 reads condition (body hwf.2.2)
  | whileFalse reads condition => exact simulation_whileFalse_exact hwf.1 reads condition
  | whileTrue reads condition _ _ body rest =>
      exact simulation_whileTrue_exact hwf.1 reads condition (body hwf.2) (rest hwf)
  | read available => exact simulation_read_exact hwf available
  | write reads => exact simulation_write_exact hwf reads
  | call lookup arity frame arguments _ result body =>
      have hf := hvalid.2.2 _ (List.mem_of_getElem? lookup)
      have hbodyWF := hf.1.2.1.mono hf.2.1
      have hcount : _ ≤ n := Nat.le_trans frame hf.2.1
      rw [← arity] at hcount
      exact simulate_call_exact hwf.1 hwf.2 arguments hcount
        (hf.1.2.2.mono hf.2.1) result (rawLink_function lookup) hcodefit (body hbodyWF)

/-- A safe source execution has one measured count that works uniformly for
every matching target frame, not a separately chosen count for each frame. -/
theorem simulate_safe_measured {n heapLimit depth : Nat} {program : Program}
    {main stmt : Stmt} {s s' : Source.State w} (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth stmt s s') (hwf : stmt.WellFormed n) :
    ∃ steps, Source.MeasuredExec n program heapLimit depth stmt steps s s' ∧
      SimulationExact n heapLimit (rawLink n program main) (entry n program main)
        depth stmt steps s s' := by
  obtain ⟨steps, hsteps⟩ := hx.exists_measured n
  exact ⟨steps, hsteps, simulate_measured hvalid hcodefit hsteps hwf⟩

/-- Run the main block with the source judgment's fixed exact transition count. -/
theorem main_run_measured {n heapLimit depth steps : Nat} {program : Program} {main : Stmt}
    {input : List (Word w)} {sourceFinal : Source.State w}
    (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.MeasuredExec n program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    StatementRunExact n heapLimit (rawLink n program main) (entry n program main)
      main steps sourceFinal (mainStart n heapLimit input) := by
  have hh : heapLimit < 2 ^ w := by omega
  have hsp : ((mainStart n heapLimit input).regs (ABI.sp n)).toNat = heapLimit := by
    rw [mainStart_sp, Word.ofNat_toNat_of_lt hh]
  apply simulate_measured hvalid hcodefit hx hvalid.1 (mainStart n heapLimit input)
    (mainStart_matches n heapLimit input)
  · simpa only [hsp] using Nat.le_refl heapLimit
  · change ((mainStart n heapLimit input).regs (ABI.sp n)).toNat +
      depth * ABI.frameSize n < 2 ^ w
    rw [hsp]
    exact hstackfit
  · simpa only [mainStart_pc] using rawLink_main n program main

/-- The entire linked program takes the measured main count plus the actual
header-read and halt transitions. It produces the specified source output. -/
theorem rawLink_runs_measured {n heapLimit depth steps : Nat} {program : Program}
    {main : Stmt} {input : List (Word w)} {sourceFinal : Source.State w}
    (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.MeasuredExec n program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec (rawLink n program main) steps (mainStart n heapLimit input) bodyFinish ∧
      Exec (rawLink n program main) (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨bodyFinish, hbody, hmatch, _, hpc⟩ :=
    main_run_measured hvalid hcodefit hstackfit hx
  have hfetch : (rawLink n program main)[bodyFinish.pc]? = some .halt := by
    rw [hpc, mainStart_pc]
    exact rawLink_halt n program main
  have hhalt : Exec (rawLink n program main) 1 bodyFinish (execInstr .halt bodyFinish) :=
    Exec.single (step_of_fetch hmatch.running hfetch)
  have hfull := ((prologue_exec n program main heapLimit input).trans hbody).trans hhalt
  refine ⟨bodyFinish, hbody, ?_, rfl, ?_, hmatch.input.symm⟩
  · have hcount : 1 + steps + 1 = steps + 2 := by omega
    simpa only [hcount] using hfull
  · change bodyFinish.outputRev.reverse = sourceFinal.outputRev.reverse
    exact congrArg List.reverse hmatch.output.symm

/-- Checked whole-program exact execution, with no unresolved call premise. -/
theorem compileChecked_runs_measured {n heapLimit depth steps : Nat} {program : Program}
    {main : Stmt} {code : Code} {input : List (Word w)} {sourceFinal : Source.State w}
    (hcompile : compileChecked n program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.MeasuredExec n program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ bodyFinish,
      Exec code steps (mainStart n heapLimit input) bodyFinish ∧
      Exec code (steps + 2) (State.initial (BitVec.ofNat w heapLimit :: input))
        (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_runs_measured hvalid hcodefit hstackfit hx

/-- A bound proved on the measured source count is a bound on actual machine
execution, including the complete program's prologue and halt. -/
theorem compileChecked_terminatesWithin {n heapLimit depth steps budget : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked n program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.MeasuredExec n program heapLimit depth main steps
      (Source.State.initial input) sourceFinal)
    (hbudget : steps + 2 ≤ budget) :
    ∃ finish, TerminatesWithin code budget
        (State.initial (BitVec.ofNat w heapLimit :: input)) finish ∧
      finish.output = sourceFinal.output ∧ finish.input = sourceFinal.input := by
  obtain ⟨bodyFinish, _, hfull, hhalt, hout, hin⟩ :=
    compileChecked_runs_measured hcompile hcodefit hstackfit hx
  exact ⟨_, ⟨steps + 2, hbudget, hfull, hhalt⟩, hout, hin⟩

end Ram.Compiler
