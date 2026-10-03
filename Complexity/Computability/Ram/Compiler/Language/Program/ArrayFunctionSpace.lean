/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ArrayFunction.Space

/-!
# Preserve array space certificates through the general program view

These are definitional equivalences over the same compiled invocation and the
same input-seeded cumulative physical footprint. No capacity is reinterpreted
as space, no peak-live bound is claimed, and no conversion code is executed.
-/

namespace Complexity.Language.ArrayFunction

/-- The general view observes the same input-seeded physical footprint. -/
theorem toProgram_spaceFootprint (f : ArrayFunction) {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) :
    Complexity.Program.Execution.spaceFootprint (program := f.toProgram) execution =
      Execution.spaceFootprint execution := rfl

/-- The observed physical-word count is identical through either view. -/
theorem toProgram_spaceWords (f : ArrayFunction) {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) :
    Complexity.Program.Execution.spaceWords (program := f.toProgram) execution =
      Execution.spaceWords execution := rfl

/-- Fixed-width space admission, existence and budgets are unchanged. -/
theorem spaceBound_iff_toProgram (f : ArrayFunction) (valid : Array Nat → Prop)
    (w : Nat) (budget : Array Nat → Nat) :
    f.SpaceBound valid w budget ↔ f.toProgram.SpaceBound valid w budget := Iff.rfl

/-- Array-length-indexed asymptotic space is exactly the general certificate. -/
theorem spaceO_iff_toProgram (f : ArrayFunction) (valid : Array Nat → Prop)
    (growth : Nat → Nat) :
    f.SpaceO valid growth ↔ f.toProgram.SpaceO valid Array.size growth := Iff.rfl

/-- Input-indexed space likewise adds neither a new run nor a new cost. -/
theorem spaceOOn_iff_toProgram (f : ArrayFunction) (valid : Array Nat → Prop)
    (growth : Array Nat → Nat) :
    f.SpaceOOn valid growth ↔ f.toProgram.SpaceOOn valid growth := Iff.rfl

end Complexity.Language.ArrayFunction
