/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax

/-!
# Character programs with ordinary mathematical contracts

Unicode characters retain their standard scalar codes. Real array allocation,
defaulted reads and scalar comparison have checked ordinary `Char` observations;
no task-specific alphabet encoding or additional input is needed. Nested grids
retain their actual row boundaries, including empty rows. These are source
correctness results, not complete caller RAM time bounds.
-/

namespace Complexity.Examples.Characters

structure GridInput where
  rows : Array (Array Char)
  row : Nat
  column : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program Character where
  def replicate (length : Nat) (initial : Char) : Array Char := do
    return Array.replicate length initial

  def lookup (values : Array Char) (index : Nat) : Char := do
    return values.getD index 'λ'

  def different (left : Char) (right : Char) : Bool := do
    return left != right

  def atMarker (input : GridInput) : Bool := do
    let fallback := Array.replicate 0 'λ'
    let row := input.rows.getD input.row fallback
    let cell := row.getD input.column 'λ'
    if cell != '🦉' then
      return false
    else
      return true

def repeated : Complexity.Program (Nat × Char) (Array Char) :=
  program% Character.replicate

theorem repeated_correct :
    repeated.Correct (fun _ => True)
      (fun input result => result = Array.replicate input.1 input.2) := by
  program_correct Character.replicate using fun _ _ => rfl

def lookup : Complexity.Program (Array Char × Nat) Char := program% Character.lookup

theorem lookup_correct :
    lookup.Correct (fun _ => True) (fun input result => result = input.1.getD input.2 'λ') := by
  program_correct Character.lookup using fun _ _ => rfl

def different : Complexity.Program (Char × Char) Bool := program% Character.different

theorem different_correct :
    different.Correct (fun _ => True) (fun input result => result = decide (input.1 ≠ input.2)) := by
  program_correct Character.different using fun _ _ => rfl

def atMarker : Complexity.Program GridInput Bool := program% Character.atMarker

theorem atMarker_correct :
    atMarker.Correct (fun _ => True)
      (fun input result => result = decide
        (((input.rows.getD input.row #[]).getD input.column 'λ') = '🦉')) := by
  program_correct Character.atMarker using fun _ => by simp [Character.atMarker_model]

end Complexity.Examples.Characters
