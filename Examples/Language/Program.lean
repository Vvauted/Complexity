/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Input
import Examples.Language.Scalar

/-!
# A typed mathematical contract for an existing source program

The existing bounded-increment implementation is presented as a
`Complexity.Program (Nat × Nat) Nat`. Its fixed input convention passes two
natural arguments, and its correctness theorem uses the existing generated
source contract and ordinary mathematical minimum equation. No second algorithm,
argument adapter or machine proof is supplied. Time and backend realization
remain independent of this source correctness statement.
-/

namespace Complexity.Examples.TypedProgram

open Language.Examples

/-- Select the existing source function with its two ordinary natural inputs. -/
def boundedIncrement : Complexity.Program (Nat × Nat) Nat :=
  Complexity.Program.ofProgram Scalar.Implementation.program
    Scalar.Implementation.boundedIncrementId rfl

/-- The generated source correspondence and existing mathematical equation
establish successful source correctness for every pair of natural inputs. -/
theorem boundedIncrement_correct :
    boundedIncrement.Correct (fun _ => True)
      (fun input result => result = min (input.1 + 1) input.2) := by
  apply Complexity.Program.Correct.of_functionTotal Scalar.Implementation.boundedIncrement_total
  · intro _ _
    trivial
  · intro input _ value heap property
    exact ⟨value, rfl, property.1.trans (Scalar.boundedIncrement_eq input.1 input.2)⟩

end Complexity.Examples.TypedProgram
