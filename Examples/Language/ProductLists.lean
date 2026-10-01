/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Deriving
import Complexity.Language.Syntax.Represented
import Complexity.Program.Syntax
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.List.Prod

/-!
# Ordinary products in linked lists

Product constructors and matches compose actual field-chain operations. The
source contracts retain shared tails and old array contents; ordinary proofs
use Lean lists. These contracts do not supply list RAM-input encodings or
complete caller time bounds.
-/

namespace Complexity.Examples.ProductLists

source_program Linked where
  def singleton (head : Int × Nat) : List (Int × Nat) := do
    return head :: []

  def prepend (head : Int × Nat) (tail : List (Int × Nat)) : List (Int × Nat) := do
    return head :: tail

  def headOr (values : List (Int × Nat)) (fallback : Int × Nat) : Int × Nat := do
    match values with
    | [] => return fallback
    | head :: tail => return head

  def naturalPair (head : Nat × Nat) : List (Nat × Nat) := do
    return head :: []

  def nested (head : (Nat × Nat) × Int) : List ((Nat × Nat) × Int) := do
    let values := head :: []
    match values with
    | [] => return []
    | first :: rest => return first :: rest

  def retain (input : Array Int × Nat) : Int := do
    let values := input.1
    let index := input.2
    let selected := values.getD index (-1)
    let list := (selected, index) :: []
    match list with
    | [] => return -1
    | head :: tail => return values.getD head.2 head.1

def singleton : Complexity.Program (Int × Nat) (List (Int × Nat)) :=
  program% Linked.singleton

theorem singleton_correct :
    singleton.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct Linked.singleton using fun _ => rfl

def naturalPair : Complexity.Program (Nat × Nat) (List (Nat × Nat)) :=
  program% Linked.naturalPair

theorem naturalPair_correct :
    naturalPair.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct Linked.naturalPair using fun _ => rfl

def nested : Complexity.Program ((Nat × Nat) × Int) (List ((Nat × Nat) × Int)) :=
  program% Linked.nested

theorem nested_correct :
    nested.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct Linked.nested using fun _ => rfl

def retain : Complexity.Program (Array Int × Nat) Int := program% Linked.retain

theorem retain_correct : retain.Correct (fun _ => True)
    (fun input result => result = input.1.getD input.2 (-1)) := by
  program_correct Linked.retain using fun input => by
    by_cases bounded : input.2 < input.1.size <;>
      simp [Linked.retain_model, Array.getD, bounded]

open Complexity.Language Ram.LanguageCompiler
open Linked.Operations.productList0

/-- A constant bound inferred from the real three-node constructor and its
wrapper instructions. Readiness, ranges and capacity are separate premises. -/
def pairConsBodyCost : { bound : Nat // ∀ w heapLimit depth initial,
    StmtArenaCostBound program w heapLimit (depth + 1)
      (program.body consId) initial bound } := by
  ram_source_arena_cost [
    (Ram.LanguageCompiler.List.Prod.consBoolNat_arenaCostBound _ _ _)
      at (_, _) via imports.Complexity.Language.List.Prod.Operations.embedding,
    (Ram.LanguageCompiler.List.Cons.arenaCostBound .nat _ _ _)
      via imports.Linked.Operations.consNat.embedding]

end Complexity.Examples.ProductLists
