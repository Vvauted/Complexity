/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Verification.Execution
import Complexity.Computability.Ram.Execution.Runner
import Complexity.Computability.Ram.Execution.Unbounded

/-!
# Executable function calls without a stream driver

`Ram.LocalCompiler.Function.compile` prepares a fixed call-and-halt trampoline.
Its arguments are variables, never constants specialized to an input.
`Ram.LocalCompiler.Function.run` supplies argument values and shared state to
the existing RAM runner. Neither the trampoline nor its launch consumes an
input stream or writes the returned value to an output stream.

The launch is explicitly preloaded at PC 1, with the stack pointer at the heap
boundary. It skips the linker's input-header instruction. The measured execution
includes the actual call setup, function body, return sequence and final halt;
it does not count host-side preparation as a RAM loader. General function bodies
may still have their own input/output effects.

`runs` obtains an actual terminating machine execution from function correctness
without a time budget. `runUntil` executes that call without an operational limit;
`run` remains available for interruptible exploration. The corresponding result
theorems connect both interfaces to the same execution. Code and stack
representability remain explicit.
Shared memory is observed only below the heap boundary: private target stack
words are not identified with the source function's memory.
-/

namespace Ram.LocalCompiler.Function

/-- Runtime parameters occupy consecutive caller registers. -/
def arguments (arity : Nat) : List Expr :=
  (List.range arity).map Expr.var

/-- A fixed source call returns in register zero; the linker supplies the halt. -/
def trampoline (fn arity : Nat) : Stmt :=
  .call 0 fn (arguments arity)

/-- Checked compilation depends on the function table and arity, not argument values. -/
def compile (control : Nat) (program : Program) (fn arity : Nat) : Option Code :=
  compileChecked control program (trampoline fn arity)

/-- A preloaded function launch preserves shared data and binds actual parameters.
The reserved stack pointer is initialized separately from source registers. -/
def start (control heapLimit : Nat) (args : List (Word w))
    (entry : Source.State w) : Ram.State w where
  pc := 1
  regs := fun r => if r = ABI.sp control then BitVec.ofNat w heapLimit
    else (entry.enter args).regs r
  mem := entry.mem
  input := entry.input
  outputRev := entry.outputRev
  status := .running

/-- Run the checked fixed function trampoline with an operational step limit.
An arity mismatch or failed static compilation returns `none`; exhaustion is
reported by the existing runner's `outOfFuel`, retaining its state and count. -/
def run (control : Nat) (program : Program) (fn arity heapLimit budget : Nat)
    (args : List (Word w)) (entry : Source.State w) : Option (RunResult (Ram.State w)) :=
  if args.length = arity then
    (compile control program fn arity).map fun code =>
      Ram.run code budget (start control heapLimit args entry)
  else none

/-- Execute the fixed function call without choosing a transition limit.
Static rejection returns `none`. For accepted code the least-fixed-point runner
returns a normal stopping result when reached, and a diverging computation does
not return. Use `run` to explore a function with an operational limit. -/
def runUntil (control : Nat) (program : Program) (fn arity heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) : Option (RunResult (Ram.State w)) :=
  if args.length = arity then
    (compile control program fn arity).bind fun code =>
      Ram.runUntil code (start control heapLimit args entry)
  else none

/-- The enclosing call count comes from its actual generated instruction blocks. -/
def callSteps (control : Nat) (f : Func) (bodySteps : Nat) : Nat :=
  (ABI.callPrefixLocals control f.locals (arguments f.params) 0).length + 1 + bodySteps +
    (ABI.returnCodeLocals control f.locals f.result).length + 1

private theorem arguments_eval (args : List (Word w)) (entry : Source.State w) :
    (arguments args.length).map (entry.enter args).eval = args := by
  apply List.ext_getElem
  · simp [arguments]
  · intro i hi hj
    simp [arguments, Source.State.eval, Expr.eval, Source.State.enter,
      List.getElem?_eq_getElem hj]

theorem start_matches (control heapLimit : Nat) (args : List (Word w))
    (entry : Source.State w) :
    Source.State.Matches heapLimit control (entry.enter args)
      (start control heapLimit args entry) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro r hr
    simp [start, ABI.sp, Nat.ne_of_lt hr]
  · intro a ha
    rfl

@[simp] theorem start_sp (control heapLimit : Nat) (args : List (Word w))
    (entry : Source.State w) :
    (start control heapLimit args entry).regs (ABI.sp control) =
      BitVec.ofNat w heapLimit := by
  simp [start]

/-- The actual call and halt return the function's value and shared observations.
No input/output main or externally selected instruction budget is required. -/
theorem runs_measured {control heapLimit depth bodySteps fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    ∃ target, Ram.Exec code (callSteps control f bodySteps + 1)
        (start control heapLimit args entry) target ∧
      target.status = .halted ∧ target.regs 0 = value ∧
      Source.State.Observes heapLimit 0 finish target := by
  have hvalid := (compileChecked_some_iff.mp hcompile).1
  have hcontrol : 0 < control := hvalid.1.1
  obtain ⟨arity, frame, callee, body, reads, rfl, rfl⟩ := execution
  have hargs : (arguments f.params).map (entry.enter args).eval = args := by
    simpa only [arity] using arguments_eval args entry
  have call : Source.LocalMeasuredExec control program heapLimit (depth + 1)
      (trampoline fn f.params) (callSteps control f bodySteps) (entry.enter args)
      ((entry.enter args).leave callee 0 f.result) := by
    apply Source.LocalMeasuredExec.call hlookup
    · simp [arguments]
    · exact frame
    · intro expr hmem
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
      trivial
    · rw [hargs]
      exact body
    · exact reads
  have hheap : heapLimit < 2 ^ w := by omega
  have hsp : ((start control heapLimit args entry).regs (ABI.sp control)).toNat =
      heapLimit := by
    rw [start_sp, Word.ofNat_toNat_of_lt hheap]
  obtain ⟨target, run, halted, observed, _⟩ :=
    compileChecked_block_runs_observed hcompile hcode call
      (start_matches control heapLimit args entry) rfl (by rw [hsp]) (by
        change ((start control heapLimit args entry).regs (ABI.sp control)).toNat +
          (depth + 1) * ABI.frameSize control < 2 ^ w
        simpa only [hsp] using hstack)
  refine ⟨target, run, halted, ?_, ?_⟩
  · simpa only [Source.State.leave, if_pos rfl] using (observed.regs 0 hcontrol).symm
  · exact ⟨fun r hr => False.elim (Nat.not_lt_zero r hr), observed.heap,
      observed.input, observed.output⟩

/-- Safe function termination produces a halted target call before any time
bound is chosen. Its result and body count agree with the semantic observations. -/
theorem runs {control heapLimit depth fn : Nat} {program : Program} {f : Func}
    {args : List (Word w)} {entry finish : Source.State w} {value : Word w} {code : Code}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    f.eval program heapLimit args entry = Part.some (value, finish) ∧
      ∃ bodySteps target, f.bodyTime program heapLimit args entry = Part.some bodySteps ∧
        Ram.Exec code (callSteps control f bodySteps + 1)
          (start control heapLimit args entry) target ∧
        target.status = .halted ∧ target.regs 0 = value ∧
        Source.State.Observes heapLimit 0 finish target := by
  obtain ⟨bodySteps, measured⟩ := execution.exists_measured control
  obtain ⟨target, run, halted, result, observed⟩ :=
    runs_measured hcompile hlookup hcode hstack measured
  exact ⟨execution.eval_eq_some, bodySteps, target, measured.bodyTime_eq_some,
    run, halted, result, observed⟩

/-- The executable runner returns the same value and exact count whenever its
operational limit permits the actual call and final halt. -/
theorem run_eq_of_measured {control heapLimit depth bodySteps fn budget : Nat}
    {program : Program} {f : Func} {args : List (Word w)}
    {entry finish : Source.State w} {value : Word w} {code : Code}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    (hbudget : callSteps control f bodySteps + 1 ≤ budget) :
    ∃ target, run control program fn f.params heapLimit budget args entry =
        some ⟨target, callSteps control f bodySteps + 1, .halted⟩ ∧
      target.regs 0 = value ∧ Source.State.Observes heapLimit 0 finish target := by
  obtain ⟨target, executed, halted, returned, observed⟩ :=
    runs_measured hcompile hlookup hcode hstack execution
  refine ⟨target, ?_, returned, observed⟩
  simp only [run, execution.1, ↓reduceIte, hcompile, Option.map_some,
    Ram.run_of_exec executed halted hbudget]

/-- A measured invocation determines the unbounded executable call's complete
result and exact count. No proposed runtime limit occurs in this statement. -/
theorem runUntil_eq_of_measured {control heapLimit depth bodySteps fn : Nat}
    {program : Program} {f : Func} {args : List (Word w)}
    {entry finish : Source.State w} {value : Word w} {code : Code}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    ∃ target, runUntil control program fn f.params heapLimit args entry =
        some ⟨target, callSteps control f bodySteps + 1, .halted⟩ ∧
      target.regs 0 = value ∧ Source.State.Observes heapLimit 0 finish target := by
  obtain ⟨target, executed, halted, returned, observed⟩ :=
    runs_measured hcompile hlookup hcode hstack execution
  refine ⟨target, ?_, returned, observed⟩
  simp only [runUntil, execution.1, ↓reduceIte, hcompile, Option.bind_some,
    Ram.runUntil_of_exec executed halted]

/-- Functional correctness alone ensures an actual returned executable value.
The observed body count and full call count describe that same invocation;
neither a cost certificate nor an operational limit is needed to call it. -/
theorem runUntil_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    ∃ bodySteps target, runUntil control program fn f.params heapLimit args entry =
        some ⟨target, callSteps control f bodySteps + 1, .halted⟩ ∧
      target.regs 0 = value ∧ Source.State.Observes heapLimit 0 finish target ∧
      f.bodyTime program heapLimit args entry = Part.some bodySteps := by
  obtain ⟨bodySteps, measured⟩ := execution.exists_measured control
  obtain ⟨target, returned, value, observed⟩ :=
    runUntil_eq_of_measured hcompile hlookup hcode hstack measured
  exact ⟨bodySteps, target, returned, value, observed, measured.bodyTime_eq_some⟩

end Ram.LocalCompiler.Function
