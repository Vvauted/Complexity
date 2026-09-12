/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Potential bounds for allocating loops

The loop rule bounds the existing `ArenaExecutionCost` of a supplied execution.
Guards and bodies may allocate: each cost observation retains its actual heap
and cursor endpoints. Mathematical indices can track an abstract accumulator or
remaining input without decoding them from machine state.

Normal rounds supply their next index and remaining-budget inequality together.
False guards and early returns have separate exit obligations. No termination
argument, cursor invariance or additional execution semantics is required.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

universe u

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
variable {entry : Complexity.Language.State Γ}

/-- Bound an effectful loop with a mathematically indexed potential.
The actual guard's final state starts the body, and the actual body's final
state starts the next round. A normal round chooses one next index witnessing
both invariant preservation and the budget decrease. The statement bounds only
supplied completed executions; correctness and termination stay independent. -/
theorem «while» {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result} {X : Type u}
    {invariant : X → Complexity.Language.State Γ → Prop}
    {potential guardBound : X → Complexity.Language.State Γ → Nat}
    {bodyBound : X → Complexity.Language.State Γ → Complexity.Language.State Γ → Nat}
    {initialIndex : X}
    (guardCost : ∀ index state, invariant index state →
      StmtArenaCostBound program w heapLimit depth guard state (guardBound index state))
    (bodyCost : ∀ index state afterGuard, invariant index state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      StmtArenaCostBound program w heapLimit depth body afterGuard
        (bodyBound index state afterGuard))
    (falseExit : ∀ index state afterGuard, invariant index state →
      Complexity.Language.Exec program guard state afterGuard (.returned false) →
      guardBound index state + 11 ≤ potential index state)
    (normalStep : ∀ index state afterGuard afterBody, invariant index state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal →
      ∃ nextIndex, invariant nextIndex afterBody ∧
        guardBound index state + bodyBound index state afterGuard +
          potential nextIndex afterBody + 10 ≤ potential index state)
    (returnExit : ∀ index state afterGuard finish value, invariant index state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard finish (.returned value) →
      guardBound index state + bodyBound index state afterGuard + 17 ≤ potential index state)
    (initial : invariant initialIndex entry) :
    StmtArenaCostBound program w heapLimit depth (.while guard body) entry
      (potential initialIndex entry) := by
  intro finish control execution cursor finalCursor ready steps cost
  have loopBound : ∀ n {state finish : Complexity.Language.State Γ} {control : Control result}
      (execution : Complexity.Language.Exec program (.while guard body) state finish control)
      {cursor finalCursor} (ready : ArenaReady execution w heapLimit depth cursor finalCursor),
      ArenaExecutionCost ready n → ∀ index, invariant index state →
        n ≤ potential index state := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro state finish control execution cursor finalCursor ready cost index hstate
        cases cost with
        | @whileFalse Γ result depth next₀ next₁ guard body state finish test ready
            guardSteps testCost =>
            have guardLe := guardCost index state hstate test ready testCost
            have exitLe := falseExit index state finish hstate test
            omega
        | @whileTrue Γ result depth next₀ guardCursor bodyCursor next₁ guard body
            state afterGuard afterBody finish control test iteration rest
            testReady bodyReady restReady guardSteps bodySteps restSteps
            testCost iterationCost restCost =>
            have guardLe := guardCost index state hstate test testReady testCost
            have bodyLe := bodyCost index state afterGuard hstate test
              iteration bodyReady iterationCost
            obtain ⟨nextIndex, nextInvariant, roundLe⟩ :=
              normalStep index state afterGuard afterBody hstate test iteration
            have restLe := ih restSteps (by omega) rest restReady restCost nextIndex nextInvariant
            omega
        | @whileReturn Γ result depth next₀ guardCursor next₁ guard body
            state afterGuard finish value test iteration testReady bodyReady
            guardSteps bodySteps testCost iterationCost =>
            have guardLe := guardCost index state hstate test testReady testCost
            have bodyLe := bodyCost index state afterGuard hstate test
              iteration bodyReady iterationCost
            have exitLe := returnExit index state afterGuard finish value hstate test iteration
            omega
  exact loopBound steps execution ready cost initialIndex initial

end Ram.LanguageCompiler.StmtArenaCostBound
