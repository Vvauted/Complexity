/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Executable results of terminating function calls

`Halts` asserts that the existing executable function runner returns normally.
`runTotal` extracts that actual run result, and `apply` reads its returned word.
The termination proof is erased during execution: neither a mathematical answer
nor a time budget is an input to the implementation.

The result retains its machine state and measured steps. Correctness identifies
the returned word and shared state of this same run; a separate time equation
identifies its full call-and-halt count. Shared memory is observed below the heap
boundary, without equating private target stack words with source memory.

`applyState` additionally returns usable source shared state. Its heap words and
I/O come from the actual run; caller registers and out-of-heap source memory are
retained from the entry. Safe execution proves that this is exactly the source
function's final state, not an independently supplied mathematical result.
-/

namespace Ram.LocalCompiler.Function

/-- The actual executable call returns normally, not with a fault or invalid PC. -/
def Halts (control : Nat) (program : Program) (fn arity heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) : Prop :=
  ∃ result, runUntil control program fn arity heapLimit args entry = some result ∧
    result.reason = .halted

/-- Normal termination supplies the proof needed to extract the runner's result. -/
theorem Halts.isSome {control fn arity heapLimit : Nat} {program : Program}
    {args : List (Word w)} {entry : Source.State w}
    (h : Halts control program fn arity heapLimit args entry) :
    (runUntil control program fn arity heapLimit args entry).isSome := by
  obtain ⟨result, returned, _⟩ := h
  simp only [returned, Option.isSome_some]

/-- Execute a normally terminating call and return its actual state and count.
The proof only permits `Option.get`; it does not compute the result. -/
def runTotal (control : Nat) (program : Program) (fn arity heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w)
    (h : Halts control program fn arity heapLimit args entry) : RunResult (Ram.State w) :=
  (runUntil control program fn arity heapLimit args entry).get h.isSome

/-- Return the word produced by the actual executable function call.
Use `runTotal` when the resulting shared state or instruction count is also needed. -/
def «apply» (control : Nat) (program : Program) (fn arity heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w)
    (h : Halts control program fn arity heapLimit args entry) : Word w :=
  (runTotal control program fn arity heapLimit args entry h).state.regs 0

/-- Recover source shared state without exposing the compiler's private stack.
This is a host-side state projection, not a RAM loader or memory-copy operation. -/
def returnState (heapLimit : Nat) (entry : Source.State w) (target : Ram.State w) :
    Source.State w where
  regs := entry.regs
  mem := fun address =>
    if address.toNat < heapLimit then target.mem address else entry.mem address
  input := target.input
  outputRev := target.outputRev

/-- Execute one call and return its value together with reusable shared state.
The state retains the actual heap and I/O effects, with caller locals restored. -/
def applyState (control : Nat) (program : Program) (fn arity heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w)
    (h : Halts control program fn arity heapLimit args entry) : Word w × Source.State w :=
  let result := runTotal control program fn arity heapLimit args entry h
  (result.state.regs 0, returnState heapLimit entry result.state)

/-- Both application interfaces return the same word from the same run. -/
@[simp] theorem applyState_fst (control : Nat) (program : Program)
    (fn arity heapLimit : Nat) (args : List (Word w)) (entry : Source.State w)
    (h : Halts control program fn arity heapLimit args entry) :
    (applyState control program fn arity heapLimit args entry h).1 =
      «apply» control program fn arity heapLimit args entry h := rfl

/-- Safe source execution identifies the projected state, including unchanged
source memory outside the heap. No equality with the private target stack is used. -/
theorem returnState_eq_of_execution {heapLimit depth : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {target : Ram.State w}
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish)
    (observed : Source.State.Observes heapLimit 0 finish target) :
    returnState heapLimit entry target = finish := by
  have memory : (returnState heapLimit entry target).mem = finish.mem := by
    funext address
    change (if address.toNat < heapLimit then target.mem address else entry.mem address) = _
    by_cases below : address.toNat < heapLimit
    · exact (if_pos below).trans (observed.heap address below).symm
    · exact (if_neg below).trans
        (execution.mem_eq_of_le address (Nat.le_of_not_lt below)).symm
  cases finish
  simp only [returnState, Source.State.mk.injEq]
  exact ⟨execution.regs_eq.symm, memory, observed.input.symm, observed.output.symm⟩

/-- Extracting the runner's result does not change it. -/
theorem runTotal_eq_of_runUntil {control fn arity heapLimit : Nat} {program : Program}
    {args : List (Word w)} {entry : Source.State w} {result : RunResult (Ram.State w)}
    (h : Halts control program fn arity heapLimit args entry)
    (returned : runUntil control program fn arity heapLimit args entry = some result) :
    runTotal control program fn arity heapLimit args entry h = result := by
  apply Option.some.inj
  exact (Option.some_get h.isSome).trans returned

/-- The total interface retains both the actual runner equation and normal termination. -/
theorem runTotal_spec {control fn arity heapLimit : Nat} {program : Program}
    {args : List (Word w)} {entry : Source.State w}
    (h : Halts control program fn arity heapLimit args entry) :
    runUntil control program fn arity heapLimit args entry =
        some (runTotal control program fn arity heapLimit args entry h) ∧
      (runTotal control program fn arity heapLimit args entry h).reason = .halted := by
  have termination := h
  obtain ⟨result, returned, halted⟩ := termination
  rw [runTotal_eq_of_runUntil h returned]
  exact ⟨returned, halted⟩

/-- Safe source termination implies normal termination of its compiled call.
No cost certificate or operational limit is required. -/
theorem halts_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    Halts control program fn f.params heapLimit args entry := by
  obtain ⟨bodySteps, target, returned, _⟩ :=
    runUntil_of_execution hcompile hlookup hcode hstack execution
  exact ⟨⟨target, callSteps control f bodySteps + 1, .halted⟩, returned, rfl⟩

/-- Existence of a safe result suffices; the implementation need not receive that result. -/
theorem halts_of_exists_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry : Source.State w} {code : Code}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : ∃ value finish,
      Source.FunctionExec program heapLimit depth f args entry value finish) :
    Halts control program fn f.params heapLimit args entry := by
  obtain ⟨value, finish, execution⟩ := execution
  exact halts_of_execution hcompile hlookup hcode hstack execution

/-- A reusable function contract establishes normal termination of the actual
compiled call. Its postcondition and any separate time bound are not runtime inputs. -/
theorem halts_of_contract {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry : Source.State w} {code : Code}
    {P : List (Word w) → Source.State w → Prop}
    {Q : List (Word w) → Source.State w → Word w → Source.State w → Prop}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (contract : Source.FunctionContract program heapLimit depth f P Q) (pre : P args entry) :
    Halts control program fn f.params heapLimit args entry := by
  obtain ⟨value, finish, execution, _⟩ := contract args entry pre
  exact halts_of_execution hcompile hlookup hcode hstack execution

/-- The actual total run returns the source value and observes its shared final state. -/
theorem runTotal_correct_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    (runTotal control program fn f.params heapLimit args entry h).state.regs 0 = value ∧
      Source.State.Observes heapLimit 0 finish
        (runTotal control program fn f.params heapLimit args entry h).state := by
  obtain ⟨bodySteps, target, returned, value, observed, _⟩ :=
    runUntil_of_execution hcompile hlookup hcode hstack execution
  rw [runTotal_eq_of_runUntil h returned]
  exact ⟨value, observed⟩

/-- A source correctness proof identifies the ordinary executable returned word. -/
theorem apply_eq_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    «apply» control program fn f.params heapLimit args entry h = value :=
  (runTotal_correct_of_execution h hcompile hlookup hcode hstack execution).1

/-- The executable stateful application returns exactly the source invocation's
value and final shared state, suitable as the entry of another call. -/
theorem applyState_eq_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish) :
    applyState control program fn f.params heapLimit args entry h = (value, finish) := by
  obtain ⟨returned, observed⟩ :=
    runTotal_correct_of_execution h hcompile hlookup hcode hstack execution
  exact Prod.ext returned (returnState_eq_of_execution execution observed)

/-- An existing function contract proves any mathematical postcondition about
the executable returned value and state, without another implementation proof. -/
theorem applyState_spec {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry : Source.State w} {code : Code}
    {P : List (Word w) → Source.State w → Prop}
    {Q : List (Word w) → Source.State w → Word w → Source.State w → Prop}
    (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (contract : Source.FunctionContract program heapLimit depth f P Q) (pre : P args entry) :
    Q args entry (applyState control program fn f.params heapLimit args entry h).1
      (applyState control program fn f.params heapLimit args entry h).2 := by
  obtain ⟨value, finish, execution, post⟩ := contract args entry pre
  rw [applyState_eq_of_execution h hcompile hlookup hcode hstack execution]
  exact post

/-- A separate body-time theorem gives the full call-and-halt count of this same run. -/
theorem runTotal_steps_eq_of_execution {control heapLimit depth bodySteps fn : Nat}
    {program : Program} {f : Func} {args : List (Word w)}
    {entry finish : Source.State w} {value : Word w} {code : Code}
    (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish)
    (time : f.bodyTime program heapLimit args entry = Part.some bodySteps) :
    (runTotal control program fn f.params heapLimit args entry h).steps =
      callSteps control f bodySteps + 1 := by
  obtain ⟨target, returned, _⟩ :=
    runUntil_eq_of_execution hcompile hlookup hcode hstack execution time
  rw [runTotal_eq_of_runUntil h returned]

/-- A separate conditional body-time bound controls the actual complete call.
Correctness supplies termination; the bound adds no premise to the implementation. -/
theorem runTotal_steps_le_of_timeBound {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : Source.State w} {value : Word w}
    {code : Code} {P : List (Word w) → Source.State w → Prop}
    {bound : List (Word w) → Source.State w → Nat}
    (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry value finish)
    (time : Source.FunctionTimeBound control program heapLimit depth f P bound)
    (pre : P args entry) :
    (runTotal control program fn f.params heapLimit args entry h).steps ≤
      callSteps control f (bound args entry) + 1 := by
  obtain ⟨steps, measured⟩ := execution.exists_measured control
  have bounded := time args entry pre steps value finish measured
  rw [runTotal_steps_eq_of_execution h hcompile hlookup hcode hstack execution
    measured.bodyTime_eq_some]
  simp only [callSteps_eq]
  omega

end Ram.LocalCompiler.Function
