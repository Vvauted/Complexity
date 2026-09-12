/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayFunction
import Complexity.Computability.Ram.Compiler.Language.Program.Input

/-!
# Preserve array-task RAM certificates through the general program interface

The existing `ArrayFunction` and its `toProgram` view select the same source
function, emitted code, fixed array input and logarithmic width policy. Their
runtime certificates quantify over the same `FunctionArenaExecution` values
and use the same array-length measure. No wrapper executes and no instruction
count, capacity obligation or input is added or removed by this conversion.
-/

namespace Complexity.Language.ArrayFunction

/-- The general program view emits exactly the original instruction list. -/
@[simp] theorem toProgram_code (f : ArrayFunction) : f.toProgram.code = f.code := rfl

/-- Both interfaces launch the same trampoline on the same preloaded array. -/
@[simp] theorem toProgram_start (f : ArrayFunction) (xs : Array Nat) (w : Nat) :
    f.toProgram.start xs w = f.start xs w := rfl

/-- The execution evidence itself is unchanged, including the actual machine
result, source evaluation and complete final arena. -/
theorem toProgram_execution (f : ArrayFunction) (xs : Array Nat) (w depth : Nat) :
    f.toProgram.Execution xs w depth = f.Execution xs w depth := rfl

/-- The old array-time certificate is exactly the general certificate at array
length, with identical bounds, width overhead and actual halted executions. -/
theorem timeO_iff_toProgram (f : ArrayFunction) (valid : Array Nat → Prop)
    (growth : Nat → Nat) :
    f.TimeO valid growth ↔ f.toProgram.TimeO valid Array.size growth := Iff.rfl

end Complexity.Language.ArrayFunction
