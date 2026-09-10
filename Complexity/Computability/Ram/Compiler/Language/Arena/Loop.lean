/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization

/-!
# Reusing an arena across a source loop

An independently established finite source execution supplies termination.
Readiness of its actual guards and bodies supplies word ranges, nesting and
capacity, while their boundary cursors stay fixed. A body may allocate inside
reclaiming scopes: fixing its entry and exit cursors does not require a constant
cursor at intermediate execution steps.

The source invariant is shared with the mathematical correctness proof. The
rule neither asks for another descent argument nor introduces a resource
interpreter or a proposed instruction budget.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

/-- Lift a successful finite loop whose actual guard and body rounds reuse
their entry arena extent. The body may return early; a normal body reestablishes
the shared source invariant for the next iteration. -/
theorem while_of_exec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor : Nat} {Γ : List Ty} {result : Ty}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body) entry finish control)
    (guardReady : ∀ current afterGuard decision, invariant current →
      ∀ tested : Complexity.Language.Exec program guard current afterGuard (.returned decision),
        ArenaReady tested w heapLimit depth cursor cursor)
    (bodyReady : ∀ current afterGuard afterBody outcome, invariant current →
      Complexity.Language.Exec program guard current afterGuard (.returned true) →
      ∀ iterated : Complexity.Language.Exec program body afterGuard afterBody outcome,
        ControlFits w outcome → ArenaReady iterated w heapLimit depth cursor cursor)
    (preserve : ∀ current afterGuard afterBody, invariant current →
      Complexity.Language.Exec program guard current afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal → invariant afterBody)
    (initial : invariant entry) (successful : ControlFits w control) :
    ArenaReady execution w heapLimit depth cursor cursor := by
  have lift : ∀ {Δ : List Ty} {σ : Ty}
      {statement : Complexity.Language.Stmt signatures Δ σ}
      {start stop : Complexity.Language.State Δ} {outcome : Control σ},
      ∀ actual : Complexity.Language.Exec program statement start stop outcome,
      ∀ (nextGuard : Complexity.Language.Stmt signatures Δ .bool)
        (nextBody : Complexity.Language.Stmt signatures Δ σ)
        (nextInvariant : Complexity.Language.State Δ → Prop),
        statement = .while nextGuard nextBody →
        (∀ current afterGuard decision, nextInvariant current →
          ∀ tested : Complexity.Language.Exec program nextGuard current afterGuard
            (.returned decision), ArenaReady tested w heapLimit depth cursor cursor) →
        (∀ current afterGuard afterBody outcome, nextInvariant current →
          Complexity.Language.Exec program nextGuard current afterGuard (.returned true) →
          ∀ iterated : Complexity.Language.Exec program nextBody afterGuard afterBody outcome,
            ControlFits w outcome → ArenaReady iterated w heapLimit depth cursor cursor) →
        (∀ current afterGuard afterBody, nextInvariant current →
          Complexity.Language.Exec program nextGuard current afterGuard (.returned true) →
          Complexity.Language.Exec program nextBody afterGuard afterBody .normal →
            nextInvariant afterBody) →
        nextInvariant start → ControlFits w outcome →
          ArenaReady actual w heapLimit depth cursor cursor := by
    intro Δ σ statement start stop outcome actual
    induction actual <;>
      intro nextGuard nextBody nextInvariant same guardReady bodyReady preserve initial
        successful <;> cases same
    case whileFalse test ih =>
      exact .whileFalse (guardReady _ _ _ initial test)
    case whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact .whileTrue (guardReady _ _ _ initial test)
        (bodyReady _ _ _ _ initial test iteration trivial)
        (ihRest _ _ _ rfl guardReady bodyReady preserve
          (preserve _ _ _ initial test iteration) successful)
    case whileReturn test iteration ihTest ihIteration =>
      exact .whileReturn (guardReady _ _ _ initial test)
        (bodyReady _ _ _ _ initial test iteration successful)
    case whileFault => exact False.elim successful
    case whileGuardFault => exact False.elim successful
    case whileGuardMissingReturn => exact False.elim successful
  exact lift execution guard body invariant rfl guardReady bodyReady preserve initial successful

end Ram.LanguageCompiler.ArenaReady
