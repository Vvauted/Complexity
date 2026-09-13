/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Buffer.Copy
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax
import Examples.Language.Allocation
import Examples.Language.Scalar

/-!
# Typed mathematical contracts for existing source programs

The existing bounded-increment implementation is presented as a
`Complexity.Program (Nat × Nat) Nat`. Its fixed input convention passes two
natural arguments, and its correctness theorem uses the existing generated
source correspondence and ordinary mathematical minimum equation. `program%` directly
selects that source function's unchanged entry, and `program_correct` reuses its
generated represented mathematical model. No second algorithm, packing entry or additional
correspondence declaration is supplied. Time and backend realization remain
independent of this source correctness statement.

The same selector also selects the original effectful allocating `make` without
requiring a pure model. Its standard state contract proves the ordinary
`Array.replicate` result through `Correct.of_triple` at the same fixed interface.

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
  program% Scalar.Implementation.boundedIncrement

/-- The generated source correspondence and existing mathematical equation
establish successful source correctness for every pair of natural inputs. -/
theorem boundedIncrement_correct :
    boundedIncrement.Correct (fun _ => True)
      (fun input result => result = min (input.1 + 1) input.2) := by
  program_correct Scalar.Implementation.boundedIncrement using Scalar.boundedIncrement_eq

/-- Select an allocating source function without first deriving a total pure
model. The fixed output observes the returned buffer as an ordinary array. -/
def replicate : Complexity.Program (Nat × Nat) (Array Nat) :=
  program% Allocation.Named.make

open scoped Part.TotalCorrectness in
/-- A standard state contract proves the same mathematical program boundary.
No separate native implementation, input adapter or heap decoder is supplied. -/
theorem replicate_correct :
    replicate.Correct (fun _ => True)
      (fun input result => result = Array.replicate input.1 input.2) := by
  apply Complexity.Program.Correct.of_triple (pre := fun _ _ => True)
  · intro input _
    apply (Allocation.named_make_spec input.1 input.2).mono
    · exact Std.Do.SPred.entails.refl _
    · exact ⟨fun _ _ observed => ⟨_, observed, rfl⟩, Std.Do.ExceptConds.entails.refl _⟩
  · intro _ _
    trivial

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
source_program (native) NativeAppend importing Scalar.Implementation where
  def appendInOrder (input : Bool × AppendInput) : AppendOutput := do
    let arrays : AppendInput ← if input.1 then do
      return { left := input.2.right, right := input.2.left }
    else do
      return input.2
    let result ← append arrays
    return result

  def append (input : AppendInput) : AppendOutput :=
    { values := input.left ++ input.right }

  def boundedLength (input : AppendInput) : Nat := do
    let limit ← Scalar.Implementation.boundedIncrement input.left.size input.right.size
    return limit

  def shorterFirst (input : AppendInput) : AppendOutput := do
    if input.left.size ≤ input.right.size then
      let result ← append input
      return result
    else
      let swapped : AppendInput := { left := input.right, right := input.left }
      let result ← append swapped
      return result

/-- Mathematical reasoning uses the ordinary generated record-valued function. -/
theorem nativeAppend_eq (input : AppendInput) :
    (NativeAppend.append input).values = input.left ++ input.right := rfl

/-- A previously verified pure function is called directly on represented data
without another implementation or a caller-written correspondence lemma. -/
theorem nativeBoundedLength_eq (input : AppendInput) :
    NativeAppend.boundedLength input = min (input.left.size + 1) input.right.size := by
  exact Scalar.boundedIncrement_eq input.left.size input.right.size

/-- Ordinary conditions and tail branches use the same represented call path. -/
theorem nativeShorterFirst_eq (input : AppendInput) :
    (NativeAppend.shorterFirst input).values =
      if input.left.size ≤ input.right.size then input.left ++ input.right
        else input.right ++ input.left := by
  unfold NativeAppend.shorterFirst
  split <;> simp_all [NativeAppend.append, Id.run, Id.instMonad]

/-- Select the native record-valued function through the fixed input interface. -/
def append : Complexity.Program AppendInput AppendOutput :=
  program% NativeAppend.append

/-- The ordinary mathematical equation and generated source correspondence
establish the contract without a private heap or machine adapter. -/
theorem append_correct :
    append.Correct (fun _ => True)
      (fun input output => output.values = input.left ++ input.right) := by
  program_correct NativeAppend.append using nativeAppend_eq

/-- Branches select actual array-valued records before one common append call. -/
theorem nativeAppendInOrder_eq (input : Bool × AppendInput) :
    (NativeAppend.appendInOrder input).values =
      if input.1 then input.2.right ++ input.2.left else input.2.left ++ input.2.right := by
  cases input with
  | mk reverse arrays => cases reverse <;> rfl

/-- The same fixed input and output interfaces apply to a structured branch. -/
def appendInOrder : Complexity.Program (Bool × AppendInput) AppendOutput :=
  program% NativeAppend.appendInOrder

/-- Generated branch correspondence supplies the source proof, including the
selected record's heap-backed fields and their subsequent use by append. -/
theorem appendInOrder_correct :
    appendInOrder.Correct (fun _ => True) (fun input output =>
      output.values = if input.1 then input.2.right ++ input.2.left
        else input.2.left ++ input.2.right) := by
  program_correct NativeAppend.appendInOrder using nativeAppendInOrder_eq

end Complexity.Examples.TypedProgram
