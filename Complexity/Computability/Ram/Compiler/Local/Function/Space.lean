/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function
import Complexity.Computability.Ram.Compiler.Local.Measured.Space
import Complexity.Computability.Ram.Source.Linking
import Mathlib.Data.Finset.Card

/-!
# Separate heap and high stack regions for function invocations

The existing recursive memory simulation also applies to the fixed function
trampoline. Its heap-access envelope includes every actual call-frame access,
all source memory accesses and the final halt, at the same measured count as
the function runner. No additional cost semantics is used.

`heapLimit` includes represented input and output arrays and runtime metadata.
The enclosing stack interval adds a sufficient depth-times-frame allowance.
This is a bound on the physical memory addresses used by this invocation, not
an exact peak-live-object count. Registers, code and the input/output streams
are separate resources; arbitrary preloaded environment memory outside the
envelope is preserved, not counted as this invocation's workspace.
-/

namespace Ram.Source.FunctionMeasuredExec

/-- Increasing a safety limit retains the exact invocation, fields, effects
and measured count. It does not move the target stack or alter the program. -/
theorem mono_heap {control heapLimit larger depth bodySteps : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : State w} {value : List (Word w)}
    (execution : FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) (bound : heapLimit ≤ larger) :
    FunctionMeasuredExec control program larger depth f args bodySteps entry value finish := by
  obtain ⟨arity, frame, callee, body, reads, returned, shared⟩ := execution
  exact ⟨arity, frame, callee, body.mono_heap bound,
    fun result member => (reads result member).mono_heap bound, returned, shared⟩

end Ram.Source.FunctionMeasuredExec

namespace Ram.LocalCompiler

/-- A preloaded checked block and its actual final halt access only the same
address envelope as the existing recursive compiler simulation. -/
theorem compileChecked_block_heapAccesses_regions
    {control heapLimit depth steps : Nat} {program : Program} {main : Stmt}
    {code : Code} {source finish : Source.State w} {target : State w}
    (compiled : compileChecked control program main = some code)
    (codeCapacity : code.length < 2 ^ w)
    (execution : Source.LocalMeasuredExec control program heapLimit depth main steps source finish)
    (matched : Source.State.Matches heapLimit control source target)
    (pc : target.pc = 1)
    (heapBelow : heapLimit ≤ (target.regs (ABI.sp control)).toNat)
    (stackCapacity : Compiler.StackFits control depth target)
    {address : Word w} (member : address ∈ heapAccesses code (steps + 1) target) :
    address.toNat < heapLimit ∨
      (target.regs (ABI.sp control)).toNat ≤ address.toNat ∧
        address.toNat < (target.regs (ABI.sp control)).toNat + depth * ABI.frameSize control := by
  obtain ⟨valid, rfl⟩ := compileChecked_some_iff.mp compiled
  have atMain : CodeAt (rawLink control program main) target.pc
      (compileStmt control (calleeLocals program) (entry control program main) main target.pc) := by
    simpa only [pc] using rawLink_main control program main
  have simulation := simulate_measured_regions valid codeCapacity execution valid.1
  obtain ⟨last, run, lastMatched, _, _, lastPC⟩ :=
    simulation.1 (Nat.le_refl control) target matched heapBelow stackCapacity atMain
  have fetch : (rawLink control program main)[last.pc]? = some .halt := by
    rw [lastPC, pc]
    exact rawLink_halt control program main
  rw [heapAccesses_add run 1, heapAccesses_one,
    stepHeapAccesses_of_fetch lastMatched.running fetch] at member
  simp only [Instr.heapAccesses, Finset.union_empty] at member
  exact simulation.2 (Nat.le_refl control) target matched heapBelow stackCapacity atMain
    address member

namespace Function

private theorem trampoline_measured
    {control heapLimit depth bodySteps fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w}
    {value : List (Word w)} (lookup : program[fn]? = some f)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    ∃ final, Source.LocalMeasuredExec control program heapLimit (depth + 1)
      (trampoline fn f.params f.results.length) (callSteps control f bodySteps)
      (entry.enter args) final := by
  obtain ⟨arity, frame, callee, body, reads, rfl, rfl⟩ := execution
  have evaluated : (arguments f.params).map (entry.enter args).eval = args := by
    rw [← arity]
    apply List.ext_getElem
    · simp [arguments]
    · intro i hi hj
      simp [arguments, Source.State.eval, Expr.eval, Source.State.enter,
        List.getElem?_eq_getElem hj]
  have argumentReads : ∀ expr ∈ arguments f.params,
      expr.ReadsBelow heapLimit (entry.enter args).regs (entry.enter args).mem := by
    intro expr member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    trivial
  refine ⟨(entry.enter args).leave callee (List.range f.results.length) f.results, ?_⟩
  simpa only [trampoline, callSteps, List.length_range] using
    (Source.LocalMeasuredExec.call (dsts := List.range f.results.length) lookup
      (by simp [arguments]) List.length_range frame argumentReads
      (by simpa only [evaluated] using body) reads)

variable {control heapLimit stackBase depth bodySteps fn : Nat} {program : Program}
variable {f : Func} {args : List (Word w)} {entry finish : Source.State w}
variable {value : List (Word w)} {code : Code}

/-- The source heap bound and the actual stack base are independent. Every
actual access lies in the heap prefix or the high stack interval, not the gap. -/
theorem heapAccesses_in_regions
    (compiled : compile control program fn f.params = some code)
    (lookup : program[fn]? = some f) (codeCapacity : code.length < 2 ^ w)
    (separated : heapLimit ≤ stackBase)
    (stackCapacity : stackBase + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    {address : Word w}
    (member : address ∈ heapAccesses code (callSteps control f bodySteps + 1)
      (start control stackBase args entry)) :
    address.toNat < heapLimit ∨ stackBase ≤ address.toNat ∧
      address.toNat < stackBase + (depth + 1) * ABI.frameSize control := by
  have checked : compileChecked control program
      (trampoline fn f.params f.results.length) = some code := by
    simpa only [compile, resultArity_lookup lookup] using compiled
  obtain ⟨final, call⟩ := trampoline_measured lookup execution
  have heapFits : stackBase < 2 ^ w := by omega
  have sp : ((start control stackBase args entry).regs (ABI.sp control)).toNat =
      stackBase := by
    rw [start_sp, Word.ofNat_toNat_of_lt heapFits]
  have stackFits : Compiler.StackFits control (depth + 1)
      (start control stackBase args entry) := by
    change ((start control stackBase args entry).regs (ABI.sp control)).toNat +
      (depth + 1) * ABI.frameSize control < 2 ^ w
    simpa only [sp] using stackCapacity
  simpa only [sp] using compileChecked_block_heapAccesses_regions checked codeCapacity call
    (by
      refine ⟨?_, ?_, rfl, rfl, rfl⟩
      · intro register below
        simp [start, ABI.sp, Nat.ne_of_lt below]
      · intro address below
        rfl) rfl (by rw [sp]; exact separated) stackFits member


end Function
end Ram.LocalCompiler
