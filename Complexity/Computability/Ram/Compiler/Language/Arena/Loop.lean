/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization
import Complexity.Language.Verification

/-!
# Reusing an arena across a source loop

An independently established finite source execution supplies termination.
Readiness of its actual guards and bodies supplies word ranges, nesting and
capacity. The fixed-extent rule permits allocation inside reclaiming scopes.
The indexed rule threads changing boundary cursors and mathematical indices
through the same actual guards and iterations, retaining their final heaps.

The source invariant is shared with the mathematical correctness proof. The
rule neither asks for another descent argument nor introduces a resource
interpreter or a proposed instruction budget.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

universe u

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

/-- Lift an existing successful finite loop with a mathematically indexed
invariant and changing arena cursors. Each guard passes its actual final state
and cursor to the body. Normal completion chooses the next index; early return
retains its actual postcondition. Readiness supplies returned-value ranges,
without a separate range premise for the loop's final result or another
termination proof. -/
theorem while_of_exec_indexed
    {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor : Nat} {Γ : List Ty} {result : Ty}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : X → Complexity.Language.State Γ → Nat → Prop}
    {guardPost : X → Complexity.Language.State Γ → Bool → Nat → Prop}
    {post : Complexity.Language.State Γ → Control result → Nat → Prop}
    {initialIndex : X} {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body) entry finish control)
    (guardReady : ∀ index current start, invariant index current start →
      ∀ afterGuard decision
        (tested : Complexity.Language.Exec program guard current afterGuard (.returned decision)),
        ∃ guardCursor, ArenaReady tested w heapLimit depth start guardCursor ∧
          guardPost index afterGuard decision guardCursor)
    (bodyReady : ∀ index afterGuard guardCursor, guardPost index afterGuard true guardCursor →
      ∀ afterBody outcome
        (iterated : Complexity.Language.Exec program body afterGuard afterBody outcome),
        ∃ bodyCursor, ArenaReady iterated w heapLimit depth guardCursor bodyCursor ∧
          match outcome with
          | .normal => ∃ nextIndex, invariant nextIndex afterBody bodyCursor
          | .returned value => post afterBody (.returned value) bodyCursor
          | .fault _ => False)
    (falseExit : ∀ index afterGuard guardCursor,
      guardPost index afterGuard false guardCursor → post afterGuard .normal guardCursor)
    (initial : invariant initialIndex entry cursor)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ∃ finalCursor, ArenaReady execution w heapLimit depth cursor finalCursor ∧
      post finish control finalCursor := by
  have lift : ∀ {Δ : List Ty} {σ : Ty}
      {statement : Complexity.Language.Stmt signatures Δ σ}
      {start stop : Complexity.Language.State Δ} {outcome : Control σ},
      ∀ actual : Complexity.Language.Exec program statement start stop outcome,
      ∀ (nextGuard : Complexity.Language.Stmt signatures Δ .bool)
        (nextBody : Complexity.Language.Stmt signatures Δ σ)
        (nextInvariant : X → Complexity.Language.State Δ → Nat → Prop)
        (nextGuardPost : X → Complexity.Language.State Δ → Bool → Nat → Prop)
        (nextPost : Complexity.Language.State Δ → Control σ → Nat → Prop),
        statement = .while nextGuard nextBody →
        (∀ index current start, nextInvariant index current start →
          ∀ afterGuard decision
            (tested : Complexity.Language.Exec program nextGuard current afterGuard
              (.returned decision)),
            ∃ guardCursor, ArenaReady tested w heapLimit depth start guardCursor ∧
              nextGuardPost index afterGuard decision guardCursor) →
        (∀ index afterGuard guardCursor,
          nextGuardPost index afterGuard true guardCursor →
          ∀ afterBody outcome
            (iterated : Complexity.Language.Exec program nextBody afterGuard afterBody outcome),
            ∃ bodyCursor, ArenaReady iterated w heapLimit depth guardCursor bodyCursor ∧
              match outcome with
              | .normal => ∃ nextIndex, nextInvariant nextIndex afterBody bodyCursor
              | .returned value => nextPost afterBody (.returned value) bodyCursor
              | .fault _ => False) →
        (∀ index afterGuard guardCursor, nextGuardPost index afterGuard false guardCursor →
          nextPost afterGuard .normal guardCursor) →
        ∀ index cursor, nextInvariant index start cursor →
          outcome.Satisfies (fun _ => True) (fun _ _ => True) stop →
          ∃ finalCursor, ArenaReady actual w heapLimit depth cursor finalCursor ∧
            nextPost stop outcome finalCursor := by
    intro Δ σ statement start stop outcome actual
    induction actual <;>
      intro nextGuard nextBody nextInvariant nextGuardPost nextPost same guardReady bodyReady
        falseExit index cursor initial successful <;> cases same
    case whileFalse test ih =>
      obtain ⟨guardCursor, testReady, tested⟩ := guardReady index _ cursor initial _ false test
      exact ⟨guardCursor, .whileFalse testReady, falseExit index _ guardCursor tested⟩
    case whileTrue test iteration rest ihTest ihIteration ihRest =>
      obtain ⟨guardCursor, testReady, tested⟩ := guardReady index _ cursor initial _ true test
      obtain ⟨bodyCursor, iterationReady, nextIndex, nextInput⟩ :=
        bodyReady index _ guardCursor tested _ .normal iteration
      obtain ⟨finalCursor, restReady, finalPost⟩ :=
        ihRest _ _ nextInvariant nextGuardPost nextPost rfl
          guardReady bodyReady falseExit nextIndex bodyCursor nextInput successful
      exact ⟨finalCursor, .whileTrue testReady iterationReady restReady, finalPost⟩
    case whileReturn test iteration ihTest ihIteration =>
      obtain ⟨guardCursor, testReady, tested⟩ := guardReady index _ cursor initial _ true test
      obtain ⟨bodyCursor, iterationReady, returned⟩ :=
        bodyReady index _ guardCursor tested _ _ iteration
      exact ⟨bodyCursor, .whileReturn testReady iterationReady, returned⟩
    case whileFault => exact False.elim successful
    case whileGuardFault => exact False.elim successful
    case whileGuardMissingReturn => exact False.elim successful
  exact lift execution guard body invariant guardPost post rfl
    guardReady bodyReady falseExit initialIndex cursor initial successful

end Ram.LanguageCompiler.ArenaReady
