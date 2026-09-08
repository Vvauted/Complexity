/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function
import Examples.Ram.Factorial

/-!
# Running an intermediate function

The factorial implementation is reused without its optional input/output main.
The runtime adapter takes an ordinary argument value, launches a checked fixed
call trampoline, and returns the machine's result, exact count and stopping
reason. The operational limit makes exploratory execution interruptible; the
function's correctness and termination theorems require no time budget.
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

end Ram.Examples.FunctionRun
