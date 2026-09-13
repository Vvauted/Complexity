/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Buffer.Copy
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax
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
derived fixed interfaces. Its native source reads record fields and returns a
record containing the appended array. `program%` selects that same source through
an executable packing entry, and `program_correct` transports the ordinary
mathematical equation through its generated source correspondence.
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

/- The same library append selected through ordinary record fields. The native
equation and the actual buffer call are generated from this single declaration. -/
source_program (native) NativeAppend where
  def append (input : AppendInput) : AppendOutput :=
    { values := input.left ++ input.right }

/-- Mathematical reasoning uses the ordinary generated record-valued function. -/
theorem nativeAppend_eq (input : AppendInput) :
    (NativeAppend.append input).values = input.left ++ input.right := rfl

/-- Select the native record-valued function through the fixed input interface. -/
def append : Complexity.Program AppendInput AppendOutput :=
  program% NativeAppend.append

/-- The ordinary mathematical equation and generated source correspondence
establish the contract without a private heap or machine adapter. -/
theorem append_correct :
    append.Correct (fun _ => True)
      (fun input output => output.values = input.left ++ input.right) := by
  program_correct NativeAppend.append using nativeAppend_eq

end Complexity.Examples.TypedProgram
