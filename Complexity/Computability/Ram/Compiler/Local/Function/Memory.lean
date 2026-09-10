/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function
import Complexity.Computability.Ram.Compiler.Local.Measured.Memory
import Mathlib.Data.Finset.Card

/-!
# Address-space bounds for preloaded function invocations

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

namespace Ram.LocalCompiler

/-- A preloaded checked block and its actual final halt access only the same
address envelope as the existing recursive compiler simulation. -/
theorem compileChecked_block_heapAccesses_below
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
    address.toNat < (target.regs (ABI.sp control)).toNat + depth * ABI.frameSize control := by
  obtain ⟨valid, rfl⟩ := compileChecked_some_iff.mp compiled
  have atMain : CodeAt (rawLink control program main) target.pc
      (compileStmt control (calleeLocals program) (entry control program main) main target.pc) := by
    simpa only [pc] using rawLink_main control program main
  have simulation := simulate_measured_memory valid codeCapacity execution valid.1
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

variable {control heapLimit depth bodySteps fn : Nat} {program : Program}
variable {f : Func} {args : List (Word w)} {entry finish : Source.State w}
variable {value : List (Word w)} {code : Code}

/-- Every actual address used by a complete preloaded call, including nested
calls, lies in the sufficient shared-heap-plus-stack interval. -/
theorem heapAccesses_below
    (compiled : compile control program fn f.params = some code)
    (lookup : program[fn]? = some f) (codeCapacity : code.length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    {address : Word w}
    (member : address ∈ heapAccesses code (callSteps control f bodySteps + 1)
      (start control heapLimit args entry)) :
    address.toNat < heapLimit + (depth + 1) * ABI.frameSize control := by
  have checked : compileChecked control program
      (trampoline fn f.params f.results.length) = some code := by
    simpa only [compile, resultArity_lookup lookup] using compiled
  obtain ⟨final, call⟩ := trampoline_measured lookup execution
  have heapFits : heapLimit < 2 ^ w := by omega
  have sp : ((start control heapLimit args entry).regs (ABI.sp control)).toNat =
      heapLimit := by
    rw [start_sp, Word.ofNat_toNat_of_lt heapFits]
  have stackFits : Compiler.StackFits control (depth + 1)
      (start control heapLimit args entry) := by
    change ((start control heapLimit args entry).regs (ABI.sp control)).toNat +
      (depth + 1) * ABI.frameSize control < 2 ^ w
    simpa only [sp] using stackCapacity
  simpa only [sp] using compileChecked_block_heapAccesses_below checked codeCapacity call
    (start_matches control heapLimit args entry) rfl (by rw [sp]) stackFits member

/-- The address envelope includes temporary and same-value writes, not only
cells whose final value differs from their entry value. -/
theorem heapWrites_below
    (compiled : compile control program fn f.params = some code)
    (lookup : program[fn]? = some f) (codeCapacity : code.length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    {address : Word w}
    (member : address ∈ heapWrites code (callSteps control f bodySteps + 1)
      (start control heapLimit args entry)) :
    address.toNat < heapLimit + (depth + 1) * ABI.frameSize control :=
  heapAccesses_below compiled lookup codeCapacity stackCapacity execution
    (heapWrites_subset_accesses _ _ _ member)

/-- The invocation touches at most this many physical memory words. Reusing
an address does not add another word; this is not a count of allocation events
or a claim that every touched object remains live. -/
theorem heapAccesses_card_le
    (compiled : compile control program fn f.params = some code)
    (lookup : program[fn]? = some f) (codeCapacity : code.length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    (heapAccesses code (callSteps control f bodySteps + 1)
      (start control heapLimit args entry)).card ≤
        heapLimit + (depth + 1) * ABI.frameSize control := by
  simpa only [Finset.card_range] using
    (Finset.card_le_card_of_injOn
      (s := heapAccesses code (callSteps control f bodySteps + 1)
        (start control heapLimit args entry))
      (t := Finset.range (heapLimit + (depth + 1) * ABI.frameSize control))
      BitVec.toNat
      (fun address member => Finset.mem_range.mpr
        (heapAccesses_below compiled lookup codeCapacity stackCapacity execution member))
      (fun _ _ _ _ same => BitVec.toNat_inj.mp same))

/-- No execution prefix changes environment memory above the invocation's
sufficient address envelope, even if the final invocation restores a cell. -/
theorem prefix_mem_above
    (compiled : compile control program fn f.params = some code)
    (lookup : program[fn]? = some f) (codeCapacity : code.length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    {k : Nat} {current : State w} (hk : k ≤ callSteps control f bodySteps + 1)
    (prefixRun : Exec code k (start control heapLimit args entry) current)
    {address : Word w}
    (above : heapLimit + (depth + 1) * ABI.frameSize control ≤ address.toNat) :
    current.mem address = entry.mem address := by
  apply prefixRun.prefix_mem_eq_of_not_written hk
  intro member
  exact Nat.not_lt_of_ge above
    (heapWrites_below compiled lookup codeCapacity stackCapacity execution member)

end Function
end Ram.LocalCompiler
