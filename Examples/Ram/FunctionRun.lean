/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Tactic.Ram.Run
import Examples.Ram.Factorial
import Examples.Ram.FactorialFunction

/-!
# Running an intermediate function

The factorial implementation is reused without its optional input/output main.
The runtime adapter takes an ordinary argument value, launches a checked fixed
call trampoline, and returns the machine's result, exact count and stopping
reason. `runFactorialUntil` runs without an operational limit; `runFactorial`
retains a limit for exploration. Both execute the same code, and the result
theorem derives termination and the exact count from that implementation.

The ordinary `factorial` function uses the generated `apply` entry after proving
normal termination. It computes by executing that same compiled call, not by
evaluating mathlib's specification. Its stack-capacity proof is erased at runtime;
no time estimate is needed to define or call it. The separate full-run count is
still obtained from the implementation's body-time theorem.
`ram_run_apply` handles static compilation and lookup premises for these bridges;
stack capacity and the function's correctness and time proofs remain explicit.
-/

namespace Ram.Examples.FunctionRun

/-- Execute the existing factorial function on 32-bit words. Argument preparation
is explicit preloading; the reported count includes call setup, return and halt. -/
def runFactorial (n : Word 32) (limit : Nat) : Option (Nat × Nat × StopReason) :=
  (LocalCompiler.Function.run Factorial.functions.registers Factorial.functions.program
    Factorial.functions.functionIndex.factorial Factorial.factorial.params 0 limit
    (Factorial.functions.arguments.factorial n) (Source.State.initial [])).map fun result =>
      ((result.state.regs 0).toNat, result.steps, result.reason)

-- The returned value is a function result, not a word written to an output stream.
#eval runFactorial (BitVec.ofNat 32 5) 300

/-- The same compiled factorial application, with no supplied time budget.
The function is still word-valued: this observation decodes its returned word. -/
def runFactorialUntil (n : Word 32) : Option (Nat × Nat × StopReason) :=
  (Factorial.functions.run.factorial n 0 (Source.State.initial [])).map fun result =>
      ((result.state.regs 0).toNat, result.steps, result.reason)

private theorem factorial_execution (n : Word 32) :
    Source.FunctionExec Factorial.functions.program 0 n.toNat Factorial.factorial
      (Factorial.functions.arguments.factorial n) (Source.State.initial [])
      (Factorial.value 32 n.toNat) (Source.State.initial []) := by
  simpa only [Word.ofNat_toNat_self] using
    Factorial.function_runs 0 n.toNat n.isLt (Source.State.initial [])

private theorem factorial_call_steps (bodySteps : Nat) :
    LocalCompiler.Function.callSteps Factorial.functions.registers
      Factorial.factorial bodySteps + 1 = bodySteps + 29 := by
  simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
  decide

/-- Correctness of the executable application, with its full call and halt count.
The premise is address-space capacity for the real stack, not a time budget.
Overflow of the mathematical factorial retains the established modular result. -/
theorem runFactorialUntil_eq (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) :
    runFactorialUntil n =
      some (Nat.factorial n.toNat % 2 ^ 32, 37 * n.toNat + 33, .halted) := by
  have run := by
    ram_run_apply (LocalCompiler.Function.runUntil_eq_of_execution
      (control := Factorial.functions.registers)
      (fn := Factorial.functions.functionIndex.factorial)
      (execution := factorial_execution n) (time := FactorialFunction.bodyTime_eq n))
      [Factorial.functions.function_lookup.factorial]
    simpa using hstack
  obtain ⟨target, returned, value, _⟩ := run
  have steps : LocalCompiler.Function.callSteps Factorial.functions.registers
      Factorial.factorial (37 * n.toNat + 4) + 1 = 37 * n.toNat + 33 := by
    rw [factorial_call_steps]
  simp only [Factorial.factorial] at returned steps
  simp only [runFactorialUntil, Factorial.functions.run.factorial,
    max_eq_right (by decide : 1 ≤ Factorial.functions.registers), returned,
    Option.map_some, value, Factorial.value_toNat, steps]

#eval runFactorialUntil (BitVec.ofNat 32 5)

/-- Normal termination follows from the function's budget-free correctness
proof and the compiled code's representability, before any cost formula is used. -/
theorem factorial_halts (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts Factorial.functions.registers Factorial.functions.program
      Factorial.functions.functionIndex.factorial Factorial.factorial.params 0
      (Factorial.functions.arguments.factorial n) (Source.State.initial []) := by
  ram_run_apply (LocalCompiler.Function.halts_of_execution
    (execution := factorial_execution n)) [Factorial.functions.function_lookup.factorial]
  simpa using hstack

/-- An ordinary executable function returning a decoded word. Its only runtime
argument is `n`; the erased proof ensures sufficient stack capacity. The value
comes from the actual recursive program, retaining word overflow semantics. -/
def factorial (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) : Nat :=
  (Factorial.functions.apply.factorial n 0 (Source.State.initial [])
    (factorial_halts n hstack)).toNat

/-- Correctness is an ordinary value equation about the executable function. -/
theorem factorial_eq_mod (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) :
    factorial n hstack = Nat.factorial n.toNat % 2 ^ 32 := by
  have returned := by
    ram_run_apply (LocalCompiler.Function.apply_eq_of_execution (factorial_halts n hstack)
      (execution := factorial_execution n)) [Factorial.functions.function_lookup.factorial]
    simpa using hstack
  exact congrArg BitVec.toNat returned

/-- When the mathematical result fits, the ordinary executable value is exactly
mathlib's factorial, not just its residue modulo the word range. -/
theorem factorial_eq (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32)
    (hfit : Nat.factorial n.toNat < 2 ^ 32) :
    factorial n hstack = Nat.factorial n.toNat := by
  rw [factorial_eq_mod, Nat.mod_eq_of_lt hfit]

/-- Ordinary mathematical properties reuse mathlib without a `Part` membership
premise, a machine state, or a proposed execution budget in the statement. -/
theorem factorial_pos (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32)
    (hfit : Nat.factorial n.toNat < 2 ^ 32) : 0 < factorial n hstack := by
  rw [factorial_eq n hstack hfit]
  exact Nat.factorial_pos _

/-- The same total call reports its actual full count. The cost equation is
proved separately and is not an argument to the executable function. -/
theorem factorial_steps (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) :
    (Factorial.functions.runTotal.factorial n 0 (Source.State.initial [])
      (factorial_halts n hstack)).steps = 37 * n.toNat + 33 := by
  have counted := by
    ram_run_apply (LocalCompiler.Function.runTotal_steps_eq_of_execution
      (factorial_halts n hstack) (execution := factorial_execution n)
      (time := FactorialFunction.bodyTime_eq n)) [Factorial.functions.function_lookup.factorial]
    simpa using hstack
  rw [factorial_call_steps] at counted
  simpa only [Factorial.functions.runTotal.factorial, Nat.add_assoc] using counted

#eval factorial (BitVec.ofNat 32 5) (by decide)

end Ram.Examples.FunctionRun
