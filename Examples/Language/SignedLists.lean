/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax

/-!
# Ordinary integer lists with actual linked storage

Constructors and matches use the same signed-node operations as their source
contracts. Mathematical proofs mention ordinary lists; allocation and reads
retain old array contents. These are source correctness statements, not complete
caller RAM time bounds or a fixed list-input interface.
-/

namespace Complexity.Examples.SignedLists

source_program Signed where
  def singleton (head : Int) : List Int := do
    return head :: []

  def empty (_unit : Unit) : List Int := do
    return []

  def positive (_unit : Unit) : List Int := do
    return 1 :: []

  def prepend (head : Int) (tail : List Int) : List Int := do
    return head :: tail

  def headOr (values : List Int) (fallback : Int) : Int := do
    match values with
    | [] => return fallback
    | head :: tail => return head

  def retain (input : Array Int × Nat) : Int := do
    let values := input.1
    let index := input.2
    let selected := values.getD index (-1)
    let list := selected :: []
    match list with
    | [] => return -1
    | head :: tail =>
        return values.getD index head

/-- The returned nodes observe the ordinary singleton, including negative heads. -/
def singleton : Complexity.Program Int (List Int) := program% Signed.singleton

theorem singleton_correct :
    singleton.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct Signed.singleton using fun _ => rfl

/-- Empty lists use absent roots, with no fictitious allocated node. -/
def empty : Complexity.Program Unit (List Int) := program% Signed.empty

theorem empty_correct : empty.Correct (fun _ => True) (fun _ result => result = []) := by
  program_correct Signed.empty using fun _ => rfl

/-- The declared result type determines the type of a positive numeric head. -/
def positive : Complexity.Program Unit (List Int) := program% Signed.positive

theorem positive_correct :
    positive.Correct (fun _ => True) (fun _ result => result = [1]) := by
  program_correct Signed.positive using fun _ => rfl

/-- Construction and decomposition preserve the original array observation. -/
def retain : Complexity.Program (Array Int × Nat) Int := program% Signed.retain

theorem retain_correct :
    retain.Correct (fun _ => True)
      (fun input result => result = input.1.getD input.2 (-1)) := by
  program_correct Signed.retain using fun input => by
    by_cases bounded : input.2 < input.1.size <;>
      simp [Signed.retain_model, Array.getD, bounded]

end Complexity.Examples.SignedLists
