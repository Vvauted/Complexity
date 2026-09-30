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
import Examples.Language.LinkedList
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
The existing allocating singleton is selected with an ordinary `List Nat`
result, using the fixed linked-node output representation.

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

/-- Select the existing allocating list constructor with its mathematical result type. -/
def singleton : Complexity.Program Nat (List Nat) :=
  program% LinkedList.NativeConstruction.singleton

/-- The generated source correspondence observes the newly allocated linked node. -/
theorem singleton_correct :
    singleton.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct LinkedList.NativeConstruction.singleton using LinkedList.singleton_eq

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

/-- Two observed arrays and ordinary lookup parameters; the Boolean mask may
have a different length from the values array. -/
structure LookupInput where
  values : Array Nat
  enabled : Array Bool
  index : Nat
  fallback : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program (native) NativeLookup where
  def lookup (input : LookupInput) : Nat := do
    let enabled ← input.enabled.getD input.index false
    let selected ← Array.getD input.values input.index input.fallback
    if enabled then
      return selected
    else
      return input.fallback

/-- Defaulted reads use ordinary array mathematics, including missing mask
entries and out-of-bounds value indices. -/
theorem nativeLookup_eq (input : LookupInput) :
    NativeLookup.lookup input =
      if input.enabled.getD input.index false then input.values.getD input.index input.fallback
      else input.fallback := rfl

/-- The fixed interface selects the same two real buffer reads. -/
def lookup : Complexity.Program LookupInput Nat := program% NativeLookup.lookup

/-- No index bound or private heap adapter is needed in the mathematical contract.
The generated correspondence preserves the first read's heap for the second. -/
theorem lookup_correct :
    lookup.Correct (fun _ => True) (fun input result => result =
      if input.enabled.getD input.index false then input.values.getD input.index input.fallback
      else input.fallback) := by
  program_correct NativeLookup.lookup using nativeLookup_eq

/-- Pair-valued arrays remain ordinary fields; their fixed layout has two real
columns per array, including when an array is empty. -/
structure PairLookupInput where
  values : Array (Nat × Nat)
  flags : Array (Bool × Bool)
  index : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program (native) NativePairLookup where
  def lookup (input : PairLookupInput) : Nat := do
    let selected ← input.values.getD input.index (0, 0)
    let flags ← Array.getD input.flags input.index (false, false)
    if flags.1 && flags.2 then
      return selected.1 + selected.2 + input.values.size
    else
      return 0

  def natBool (values : Array (Nat × Bool)) : Nat := do
    let selected ← values.getD 0 (0, false)
    if selected.2 then
      return selected.1
    else
      return 0

  def boolNat (values : Array (Bool × Nat)) : Nat := do
    let selected ← values.getD 0 (false, 0)
    if selected.1 then
      return selected.2
    else
      return 0

  def retain (values : Array (Nat × Nat)) : Array (Nat × Nat) := values

/-- Both heap-backed column pairs survive successive reads and record packing. -/
def pairLookup : Complexity.Program PairLookupInput Nat := program% NativePairLookup.lookup

/-- The contract mentions only the original ordinary arrays, not their columns. -/
theorem pairLookup_correct :
    pairLookup.Correct (fun _ => True) (fun input result => result =
      if (input.flags.getD input.index (false, false)).1 &&
          (input.flags.getD input.index (false, false)).2 then
        (input.values.getD input.index (0, 0)).1 +
          (input.values.getD input.index (0, 0)).2 + input.values.size
      else 0) := by
  program_correct NativePairLookup.lookup using fun _ => rfl

/-- Mixed scalar column kinds use the same fixed input selection. -/
def firstEnabled : Complexity.Program (Array (Nat × Bool)) Nat :=
  program% NativePairLookup.natBool

/-- Column order is preserved, including when the Boolean column comes first. -/
def enabledFirst : Complexity.Program (Array (Bool × Nat)) Nat :=
  program% NativePairLookup.boolNat

/-- Returned pair arrays are observed from their actual two-column handles. -/
def retainPairs : Complexity.Program (Array (Nat × Nat)) (Array (Nat × Nat)) :=
  program% NativePairLookup.retain

/-- Returning an input view preserves the complete ordinary array value. -/
theorem retainPairs_correct :
    retainPairs.Correct (fun _ => True) (fun values result => result = values) := by
  program_correct NativePairLookup.retain using fun _ => rfl

/-- Nested mathematical arrays retain separate row boundaries and raw payload.
The fallback arrays are ordinary independently preloaded fields. -/
structure RaggedLookupInput where
  values : Array (Array Nat)
  flags : Array (Array Bool)
  fallback : Array Nat
  fallbackFlags : Array Bool
  row : Nat
  column : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program (native) NativeRaggedLookup where
  def lookup (input : RaggedLookupInput) : Nat := do
    let row ← input.values.getD input.row input.fallback
    let flags ← input.flags.getD input.row input.fallbackFlags
    let enabled ← flags.getD input.column false
    let result ← row.getD input.column 0
    if enabled then
      return result + input.values.size + row.size
    else
      return 0

  def retain (values : Array (Array Nat)) : Array (Array Nat) := values

/-- Row selection followed by cell access uses the same typed program boundary. -/
def raggedLookup : Complexity.Program RaggedLookupInput Nat :=
  program% NativeRaggedLookup.lookup

/-- Correctness states ordinary nested-array access, with no storage descriptors. -/
theorem raggedLookup_correct :
    raggedLookup.Correct (fun _ => True) (fun input result => result =
      if (input.flags.getD input.row input.fallbackFlags).getD input.column false then
        (input.values.getD input.row input.fallback).getD input.column 0 +
          input.values.size + (input.values.getD input.row input.fallback).size
      else 0) := by
  program_correct NativeRaggedLookup.lookup using fun _ => rfl

/-- Nested outputs observe the actual returned boundary and payload buffers. -/
def retainRows : Complexity.Program (Array (Array Nat)) (Array (Array Nat)) :=
  program% NativeRaggedLookup.retain

theorem retainRows_correct :
    retainRows.Correct (fun _ => True) (fun rows result => result = rows) := by
  program_correct NativeRaggedLookup.retain using fun _ => rfl

/-- An ordinary record element with a scalar and an array field. -/
structure Reading where
  tag : Nat
  values : Array Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

/-- The default is a genuine represented record, including its backing array. -/
structure ReadingInput where
  readings : Array Reading
  fallback : Reading
  index : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program RecordLookup where
  def lookup (input : ReadingInput) : Nat := do
    let selected ← input.readings.getD input.index input.fallback
    let first ← selected.values.getD 0 0
    return selected.tag + first + input.readings.size

/-- Record-array reading reuses the same fixed program input, not a task codec. -/
def recordLookup : Complexity.Program ReadingInput Nat := program% RecordLookup.lookup

/-- The statement retains ordinary record selection and nested array lookup. -/
theorem recordLookup_correct :
    recordLookup.Correct (fun _ => True) (fun input result => result =
      (input.readings.getD input.index input.fallback).tag +
        (input.readings.getD input.index input.fallback).values.getD 0 0 +
          input.readings.size) := by
  program_correct RecordLookup.lookup using fun _ => rfl

end Complexity.Examples.TypedProgram
