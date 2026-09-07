/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Frame.StackBasic
import Ram.LocalExact.Frame

/-!
# Retained frame stacks throughout recursive execution

The existing recursive write-region simulation preserves a whole newest-first
list of older saved frames at every actual prefix. All frames refer to the
same intermediate memory; their original saved values and ordered extents
are retained together. No sum of separately timed peaks is used.
-/

namespace Ram.LocalCompiler.SimulationWrites

/-- Every older frame in a supplied retained stack survives the same actual
execution prefix, including nested calls and loops. The bound on the saved
areas may be smaller than the executing statement's entry SP. -/
theorem prefix_savedFrames {control locals heapLimit depth steps top k : Nat}
    {code : Code} {localsTable entries : Nat → Nat} {stmt : Stmt}
    {s s' : Source.State w} {start current : State w}
    (simulation : SimulationWrites control locals heapLimit code localsTable entries
      depth stmt steps s s')
    (hlocals : locals ≤ control) (matched : Source.State.Matches heapLimit locals s start)
    (lower : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (fits : Compiler.StackFits control depth start)
    (atStmt : CodeAt code start.pc (compileStmt control localsTable entries stmt start.pc))
    {frames : List (ABI.SavedFrame w)} (retained : ABI.SavedFrames heapLimit top frames start.mem)
    (topBound : top ≤ (start.regs (ABI.sp control)).toNat)
    (hk : k ≤ steps) (execution : Exec code k start current) :
    ABI.SavedFrames heapLimit top frames current.mem := by
  refine ⟨retained.lower, retained.upper, retained.ordered, ?_⟩
  intro frame member
  exact simulation.prefix_savedFrame hlocals matched lower fits atStmt
    (retained.lower frame member) ((retained.upper frame member).trans topBound)
    (retained.saved frame member).2 (retained.saved frame member).1 hk execution

end Ram.LocalCompiler.SimulationWrites
