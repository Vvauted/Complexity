/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalExact
import Ram.Execution.MemoryBounds

/-!
# Exact compiler simulation with protected older frames

`SimulationWrites` bounds the existing cumulative write set, retaining the
same exact simulation, source safety premises and compiler-derived step count.
Writes belong to the source heap or the stack region at/above the real entry
SP. The intervening older frames are protected throughout execution, not just
restored at its endpoint.
-/

namespace Ram.LocalCompiler

/-- Exact simulation whose actual writes exclude the interval between the
source heap boundary and the real target entry SP. -/
def SimulationWrites (control locals heapLimit : Nat) (code : Code)
    (localsTable entries : Nat → Nat) (depth : Nat) (stmt : Stmt) (steps : Nat)
    (s s' : Source.State w) : Prop :=
  SimulationExact control locals heapLimit code localsTable entries depth stmt steps s s' ∧
    ∀ (_ : locals ≤ control) (t : State w), Source.State.Matches heapLimit locals s t →
      heapLimit ≤ (t.regs (ABI.sp control)).toNat → Compiler.StackFits control depth t →
      CodeAt code t.pc (compileStmt control localsTable entries stmt t.pc) →
      ∀ address ∈ heapWrites code steps t,
        address.toNat < heapLimit ∨ (t.regs (ABI.sp control)).toNat ≤ address.toNat

end Ram.LocalCompiler
