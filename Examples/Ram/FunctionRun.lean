/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function
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
  (LocalCompiler.Function.runUntil Factorial.functions.registers Factorial.functions.program
    Factorial.functions.functionIndex.factorial Factorial.factorial.params 0
    (Factorial.functions.arguments.factorial n) (Source.State.initial [])).map fun result =>
      ((result.state.regs 0).toNat, result.steps, result.reason)

/-- Correctness of the executable application, with its full call and halt count.
The premise is address-space capacity for the real stack, not a time budget.
Overflow of the mathematical factorial retains the established modular result. -/
theorem runFactorialUntil_eq (n : Word 32)
    (hstack : (n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32) :
    runFactorialUntil n =
      some (Nat.factorial n.toNat % 2 ^ 32, 37 * n.toNat + 33, .halted) := by
  let code := LocalCompiler.rawLink Factorial.functions.registers Factorial.functions.program
    (LocalCompiler.Function.trampoline Factorial.functions.functionIndex.factorial
      Factorial.factorial.params)
  have hcompile : LocalCompiler.Function.compile Factorial.functions.registers
      Factorial.functions.program Factorial.functions.functionIndex.factorial
      Factorial.factorial.params = some code := by decide
  have hcode : code.length < 2 ^ 32 := by decide
  have execution := Factorial.function_runs 0 n.toNat n.isLt (Source.State.initial [])
  simp only [Word.ofNat_toNat_self] at execution
  obtain ⟨bodySteps, target, returned, value, _, bodyCount⟩ :=
    LocalCompiler.Function.runUntil_of_execution hcompile
      Factorial.functions.function_lookup.factorial hcode (by simpa using hstack) execution
  change FactorialFunction.bodyTime n = Part.some bodySteps at bodyCount
  have count := Part.some_injective ((FactorialFunction.bodyTime_eq n).symm.trans bodyCount)
  have callCount : LocalCompiler.Function.callSteps Factorial.functions.registers
      Factorial.factorial bodySteps = bodySteps + 28 := Factorial.initial_call_steps bodySteps
  have steps : LocalCompiler.Function.callSteps Factorial.functions.registers
      Factorial.factorial bodySteps + 1 = 37 * n.toNat + 33 := by
    rw [callCount, ← count]
  simp only [runFactorialUntil, returned, Option.map_some, value, Factorial.value_toNat, steps]

#eval runFactorialUntil (BitVec.ofNat 32 5)

end Ram.Examples.FunctionRun
