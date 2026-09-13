/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Buffer.Copy
import Examples.Language.Scalar

/-!
# Typed mathematical contracts for existing source programs

The existing bounded-increment implementation is presented as a
`Complexity.Program (Nat × Nat) Nat`. Its fixed input convention passes two
natural arguments, and its correctness theorem uses the existing generated
source contract and ordinary mathematical minimum equation. No second algorithm,
argument adapter or machine proof is supplied. Time and backend realization
remain independent of this source correctness statement.

The array-append consumer uses ordinary closed input and output records with
derived fixed interfaces. It selects the existing allocating append source and
reuses its contents theorem. These records describe the mathematical invocation
boundary; they are not registered as native source-language record operations.
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

/-- Two ordinary arrays, using the shared derived source and RAM input layout. -/
structure AppendInput where
  left : Array Nat
  right : Array Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

/-- Observe the returned array's actual contents through an ordinary record. -/
structure AppendOutput where
  values : Array Nat
  deriving Complexity.Program.Output

/-- Select the existing allocating append implementation without a wrapper body. -/
def append : Complexity.Program AppendInput AppendOutput :=
  Complexity.Program.ofProgram Language.Buffer.Copy.program Language.Buffer.Copy.appendId rfl

/-- The library's append contract supplies successful execution and the actual
result contents; the record boundary needs no private heap or machine adapter. -/
theorem append_correct :
    append.Correct (fun _ => True)
      (fun input output => output.values = input.left ++ input.right) := by
  apply Complexity.Program.Correct.of_total
  intro input _
  apply (Language.Buffer.append_total input.left input.right).consequence
  · intro args heap represented
    exact represented
  · intro args initial value finish _ property
    exact ⟨⟨input.left ++ input.right⟩, property.1, rfl⟩

end Complexity.Examples.TypedProgram
