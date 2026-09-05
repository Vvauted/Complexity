import Ram.Call

/-!
# Whole-program simulation and execution

Strong induction on the source call-depth bound closes the call-composition
premise, including self and mutual recursion. No call-correctness hypothesis
is retained by the linked-program theorems.

The generated code depends only on the source program and its static local
bound. A separately supplied first input word initializes the stack boundary;
reading that word and executing the final halt each contribute one real step.
The theorems establish finite, result-preserving machine execution. They do not
claim that existence of its step count is an asymptotic complexity bound.
-/

namespace Ram.Compiler

/-- All valid linked source statements simulate without an unresolved call
premise. A recursive body's derivation has strictly smaller call depth. -/
theorem simulate_linked {n heapLimit depth : Nat} {program : Program} {main stmt : Stmt}
    {s s' : Source.State w} (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth stmt s s')
    (hwf : stmt.WellFormed n) :
    Simulation n heapLimit (rawLink n program main) (entry n program main)
      depth stmt s s' := by
  induction depth using Nat.strongRecOn generalizing stmt s s' with
  | ind depth ih =>
      apply simulate hx hwf
      intro dst fn args caller final hcall hwfCall
      cases hcall with
      | call lookup arity frame arguments body result =>
          have hf := hvalid.2.2 _ (List.mem_of_getElem? lookup)
          have hbodyWF := hf.1.2.1.mono hf.2.1
          have hbody := ih _ (Nat.lt_succ_self _) body hbodyWF
          have hcount : args.length ≤ n := by
            rw [arity]
            exact Nat.le_trans frame hf.2.1
          exact simulate_call hwfCall.1 hwfCall.2 arguments hcount
            (hf.1.2.2.mono hf.2.1) result (rawLink_function lookup) hcodefit hbody

/-- The actual machine state after reading the extra boundary word. -/
def mainStart (n heapLimit : Nat) (input : List (Word w)) : State w :=
  execInstr (.read (ABI.sp n)) (State.initial (BitVec.ofNat w heapLimit :: input))

@[simp] theorem mainStart_pc (n heapLimit : Nat) (input : List (Word w)) :
    (mainStart n heapLimit input).pc = 1 := rfl

@[simp] theorem mainStart_sp (n heapLimit : Nat) (input : List (Word w)) :
    (mainStart n heapLimit input).regs (ABI.sp n) = BitVec.ofNat w heapLimit := by
  simp [mainStart, execInstr, State.initial, State.setReg, State.next]

@[simp] theorem mainStart_input (n heapLimit : Nat) (input : List (Word w)) :
    (mainStart n heapLimit input).input = input := rfl

/-- SP lies outside all source locals, so the prologue preserves the source's
zero-initialized registers and heap while consuming only the extra header. -/
theorem mainStart_matches (n heapLimit : Nat) (input : List (Word w)) :
    Source.State.Matches heapLimit n (Source.State.initial input)
      (mainStart n heapLimit input) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro r hr
    simp [Source.State.initial, mainStart, execInstr, State.initial, State.setReg,
      State.next, ABI.sp, Nat.ne_of_lt hr]
  · intro address _
    rfl

/-- The stack-boundary header is read by a real, counted RAM instruction. -/
theorem prologue_exec (n : Nat) (program : Program) (main : Stmt)
    (heapLimit : Nat) (input : List (Word w)) :
    Exec (rawLink n program main) 1
      (State.initial (BitVec.ofNat w heapLimit :: input)) (mainStart n heapLimit input) :=
  Exec.single (step_of_fetch rfl (rawLink_prologue n program main))

/-- Execute the main block from the state reached by the prologue. The stack
space inequality also guarantees exact encoding of the boundary word. -/
theorem main_run {n heapLimit depth : Nat} {program : Program} {main : Stmt}
    {input : List (Word w)} {sourceFinal : Source.State w}
    (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth main
      (Source.State.initial input) sourceFinal) :
    StatementRun n heapLimit (rawLink n program main) (entry n program main)
      main sourceFinal (mainStart n heapLimit input) := by
  have hh : heapLimit < 2 ^ w := by omega
  have hsp : ((mainStart n heapLimit input).regs (ABI.sp n)).toNat = heapLimit := by
    rw [mainStart_sp, Word.ofNat_toNat_of_lt hh]
  apply simulate_linked hvalid hcodefit hx hvalid.1 (mainStart n heapLimit input)
    (mainStart_matches n heapLimit input)
  · simpa only [hsp] using Nat.le_refl heapLimit
  · change ((mainStart n heapLimit input).regs (ABI.sp n)).toNat +
      depth * ABI.frameSize n < 2 ^ w
    rw [hsp]
    exact hstackfit
  · simpa only [mainStart_pc] using rawLink_main n program main

/-- The complete run has exactly the main body's actual transition count plus
the prologue read and final halt. Observable output and remaining input agree
with the source execution; the final target state is successfully halted. -/
theorem rawLink_runs {n heapLimit depth : Nat} {program : Program} {main : Stmt}
    {input : List (Word w)} {sourceFinal : Source.State w}
    (hvalid : Valid n program main)
    (hcodefit : (rawLink n program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth main
      (Source.State.initial input) sourceFinal) :
    ∃ bodySteps bodyFinish,
      Exec (rawLink n program main) bodySteps (mainStart n heapLimit input) bodyFinish ∧
      Exec (rawLink n program main) (bodySteps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨bodySteps, bodyFinish, hbody, hmatch, _, hpc⟩ :=
    main_run hvalid hcodefit hstackfit hx
  have hfetch : (rawLink n program main)[bodyFinish.pc]? = some .halt := by
    rw [hpc, mainStart_pc]
    exact rawLink_halt n program main
  have hhalt : Exec (rawLink n program main) 1 bodyFinish (execInstr .halt bodyFinish) :=
    Exec.single (step_of_fetch hmatch.running hfetch)
  have hfull := ((prologue_exec n program main heapLimit input).trans hbody).trans hhalt
  refine ⟨bodySteps, bodyFinish, hbody, ?_, rfl, ?_, hmatch.input.symm⟩
  · have hcount : 1 + bodySteps + 1 = bodySteps + 2 := by omega
    simpa only [hcount] using hfull
  · change bodyFinish.outputRev.reverse = sourceFinal.outputRev.reverse
    exact congrArg List.reverse hmatch.output.symm

/-- The checked compiler's public whole-program theorem. Static validity is
obtained from successful compilation, and recursive calls have no remaining
external correctness assumption. Runtime safety and word-fit premises remain
explicit rather than being claimed by the static checker. -/
theorem compileChecked_runs {n heapLimit depth : Nat} {program : Program} {main : Stmt}
    {code : Code} {input : List (Word w)} {sourceFinal : Source.State w}
    (hcompile : compileChecked n program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth main
      (Source.State.initial input) sourceFinal) :
    ∃ bodySteps bodyFinish,
      Exec code bodySteps (mainStart n heapLimit input) bodyFinish ∧
      Exec code (bodySteps + 2) (State.initial (BitVec.ofNat w heapLimit :: input))
        (execInstr .halt bodyFinish) ∧
      (execInstr .halt bodyFinish).status = .halted ∧
      (execInstr .halt bodyFinish).output = sourceFinal.output ∧
      (execInstr .halt bodyFinish).input = sourceFinal.input := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_runs hvalid hcodefit hstackfit hx

end Ram.Compiler
