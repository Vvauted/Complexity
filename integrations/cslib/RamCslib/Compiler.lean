import Ram.LocalProgram
import RamCslib.Execution

/-!
# Optimized checked source programs with CSLib execution certificates

These export the proved callee-local compiler simulation, not new price annotations.
Calls use the actual callee's local frame and compiler-derived transition count.
The exact count includes the complete program's stack-boundary header read and
halt. The source result and remaining input are preserved at the same endpoint.
-/

namespace Ram.Cslib

/-- Checked compilation exports the full, exact measured execution through
CSLib's own relation, preserving both successful termination and the result. -/
theorem compileChecked_relatesInSteps {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : LocalCompiler.compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    ∃ finish,
      Relation.RelatesInSteps (transition code)
        (State.initial (BitVec.ofNat w heapLimit :: input)) finish (steps + 2) ∧
      finish.status = .halted ∧
      finish.output = sourceFinal.output ∧ finish.input = sourceFinal.input := by
  obtain ⟨bodyFinish, _, hfull, hhalt, hout, hin⟩ :=
    LocalCompiler.compileChecked_runs_measured hcompile hcodefit hstackfit hx
  exact ⟨execInstr .halt bodyFinish, exec_iff_relatesInSteps.mp hfull,
    hhalt, hout, hin⟩

/-- A proved source budget becomes an upstream CSLib machine-step bound, with
success and the functional postcondition retained rather than weakened away. -/
theorem compileChecked_relatesWithinSteps {control heapLimit depth steps budget : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : LocalCompiler.compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal)
    (hbudget : steps + 2 ≤ budget) :
    ∃ finish,
      Relation.RelatesWithinSteps (transition code)
        (State.initial (BitVec.ofNat w heapLimit :: input)) finish budget ∧
      finish.status = .halted ∧
      finish.output = sourceFinal.output ∧ finish.input = sourceFinal.input := by
  obtain ⟨finish, hrun, hout, hin⟩ :=
    LocalCompiler.compileChecked_terminatesWithin hcompile hcodefit hstackfit hx hbudget
  obtain ⟨hsteps, hhalt⟩ := terminatesWithin_iff_relatesWithinSteps.mp hrun
  exact ⟨finish, hsteps, hhalt, hout, hin⟩

end Ram.Cslib
