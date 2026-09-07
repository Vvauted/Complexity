/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalExact
import Ram.Execution.MemoryBounds

/-!
# Exact compiler simulation with a target-address bound

`SimulationMemory` adds a bound on the existing actual heap-access set to
`SimulationExact`. It does not introduce another execution relation or cost.
The address envelope is relative to the real entry SP, not the source-heap
boundary: an arbitrary matching target may have older frames between them.

The global frame size is a sufficient envelope for callee-sized frames. This
is not a tight live-space bound, nor does it count registers or I/O streams.
-/

namespace Ram.LocalCompiler

/-- Existing exact simulation together with a bound on every actually accessed
heap address, including private stack accesses made by the compiled code. -/
def SimulationMemory (control locals heapLimit : Nat) (code : Code)
    (localsTable entries : Nat → Nat) (depth : Nat) (stmt : Stmt) (steps : Nat)
    (s s' : Source.State w) : Prop :=
  SimulationExact control locals heapLimit code localsTable entries depth stmt steps s s' ∧
    ∀ (_ : locals ≤ control) (t : State w), Source.State.Matches heapLimit locals s t →
      heapLimit ≤ (t.regs (ABI.sp control)).toNat → Compiler.StackFits control depth t →
      CodeAt code t.pc (compileStmt control localsTable entries stmt t.pc) →
      ∀ address ∈ heapAccesses code steps t,
        address.toNat < (t.regs (ABI.sp control)).toNat + depth * ABI.frameSize control

end Ram.LocalCompiler
