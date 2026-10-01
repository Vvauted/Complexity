/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax

/-!
# Enumeration programs with ordinary mathematical contracts

The fixed interfaces retain the original constructors. Reads and initialized
arrays use actual natural-cell operations, while their contracts mention enums.
The source and RAM inputs share the same canonical constructor-index embedding.
These examples establish source correctness, not whole-program RAM time bounds.
-/

namespace Complexity.Examples.Enumerations

inductive Mode where
  | idle | running | finished
  deriving DecidableEq, Complexity.Program.Input, Complexity.Program.Output,
    Complexity.Program.RamInput

/-- A layout and identity program need no equality decision procedure. -/
inductive Phase where
  | before | after
  deriving Complexity.Program.Input, Complexity.Program.Output, Complexity.Program.RamInput

structure History where
  values : Array Mode
  index : Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

source_program Status where
  def keepPhase (phase : Phase) : Phase := do
    return phase

  def replicate (count : Nat) (mode : Mode) : Array Mode := do
    return Array.replicate count mode

  def lookup (input : History) : Mode := do
    return input.values.getD input.index .idle

  def different (left : Mode) (right : Mode) : Bool := do
    return left != right

  def isRunning (input : History) : Bool := do
    let current := input.values.getD input.index Mode.idle
    if current == .running then
      return true
    else
      return false

def keepPhase : Complexity.Program Phase Phase := program% Status.keepPhase

theorem keepPhase_correct : keepPhase.Correct (fun _ => True) (fun input result => result = input) := by
  program_correct Status.keepPhase using fun _ => rfl

def repeated : Complexity.Program (Nat × Mode) (Array Mode) := program% Status.replicate

theorem repeated_correct : repeated.Correct (fun _ => True)
    (fun input result => result = Array.replicate input.1 input.2) := by
  program_correct Status.replicate using fun _ _ => rfl

def lookup : Complexity.Program History Mode := program% Status.lookup

theorem lookup_correct : lookup.Correct (fun _ => True)
    (fun input result => result = input.values.getD input.index .idle) := by
  program_correct Status.lookup using fun _ => rfl

def different : Complexity.Program (Mode × Mode) Bool := program% Status.different

theorem different_correct : different.Correct (fun _ => True)
    (fun input result => result = decide (input.1 ≠ input.2)) := by
  program_correct Status.different using fun _ _ => rfl

def isRunning : Complexity.Program History Bool := program% Status.isRunning

theorem isRunning_correct : isRunning.Correct (fun _ => True)
    (fun input result => result = decide (input.values.getD input.index .idle = .running)) := by
  program_correct Status.isRunning using fun _ => by simp [Status.isRunning_model]

end Complexity.Examples.Enumerations
