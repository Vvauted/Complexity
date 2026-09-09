/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Language.Eval.Locals

/-!
# Realizing a loop whose source termination is already proved

The rules below reuse an existing finite source execution or total correctness
proof. A closed round invariant supplies the operation ranges and call nesting
for each actual guard and body. Its preservation may come from the existing
source proof, without proving descent or the mathematical result again.

The guard's actual final state starts its body or false exit. A normal body
restores the invariant; an early return requires no further round. Source
determinism identifies these realized fragments with the existing source trace,
including their actual local values and shared heaps. No instruction budget,
target execution or alternate interpreter is used.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem realized_of_exec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (realizable : RealizationWP program w depth stmt normal returned entry)
    (execution : Complexity.Language.Exec program stmt entry finish control) :
    RealizedExec program w depth stmt entry finish control ∧
      control.Satisfies normal returned finish := by
  obtain ⟨actualFinish, actualControl, actual, post⟩ := realizable
  obtain ⟨rfl, rfl⟩ := execution.deterministic actual.erase
  exact ⟨actual, post⟩

namespace RealizedExec

/-- Realize the same already finite source loop. Each actual guard/body round
must be realizable, and the invariant is preserved by normal source rounds.
Its preservation may reuse an existing source specification; no decreasing
variant or repeated proof of the loop's final result is required. -/
theorem while_of_exec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body) entry finish control)
    (step : ∀ current, invariant current →
      RealizationWP program w depth guard (fun _ => False)
        (fun test afterGuard => if test then
          RealizationWP program w depth body (fun _ => True) (fun _ _ => True) afterGuard
          else True) current)
    (preserve : ∀ current afterGuard afterBody, invariant current →
      Complexity.Language.Exec program guard current afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal → invariant afterBody)
    (initial : invariant entry) :
    RealizedExec program w depth (.while guard body) entry finish control := by
  have lift : ∀ {Δ : List Ty} {σ : Ty}
      {statement : Complexity.Language.Stmt signatures Δ σ}
      {start stop : Complexity.Language.State Δ} {outcome : Control σ},
      Complexity.Language.Exec program statement start stop outcome →
      ∀ (nextGuard : Complexity.Language.Stmt signatures Δ .bool)
        (nextBody : Complexity.Language.Stmt signatures Δ σ)
        (nextInvariant : Complexity.Language.State Δ → Prop),
        statement = .while nextGuard nextBody →
        (∀ current, nextInvariant current →
          RealizationWP program w depth nextGuard (fun _ => False)
            (fun test afterGuard => if test then
              RealizationWP program w depth nextBody (fun _ => True) (fun _ _ => True) afterGuard
              else True) current) →
        (∀ current afterGuard afterBody, nextInvariant current →
          Complexity.Language.Exec program nextGuard current afterGuard (.returned true) →
          Complexity.Language.Exec program nextBody afterGuard afterBody .normal →
            nextInvariant afterBody) →
        nextInvariant start → RealizedExec program w depth statement start stop outcome := by
    intro Δ σ statement start stop outcome actual
    induction actual <;>
      intro nextGuard nextBody nextInvariant same step preserve initial <;> cases same
    case whileFalse test ih =>
      obtain ⟨realized, _⟩ := realized_of_exec (step _ initial) test
      exact .whileFalse realized
    case whileTrue test iteration rest ihTest ihIteration ihRest =>
      obtain ⟨testRealized, bodyRealizable⟩ := realized_of_exec (step _ initial) test
      obtain ⟨bodyRealized, _⟩ := realized_of_exec bodyRealizable iteration
      exact .whileTrue testRealized bodyRealized
        (ihRest _ _ _ rfl step preserve (preserve _ _ _ initial test iteration))
    case whileReturn test iteration ihTest ihIteration =>
      obtain ⟨testRealized, bodyRealizable⟩ := realized_of_exec (step _ initial) test
      obtain ⟨bodyRealized, _⟩ := realized_of_exec bodyRealizable iteration
      exact .whileReturn testRealized bodyRealized
    case whileFault test iteration ihTest ihIteration =>
      obtain ⟨_, bodyRealizable⟩ := realized_of_exec (step _ initial) test
      exact False.elim (realized_of_exec bodyRealizable iteration).2
    case whileGuardFault test ih =>
      exact False.elim (realized_of_exec (step _ initial) test).2
    case whileGuardMissingReturn test ih =>
      exact False.elim (realized_of_exec (step _ initial) test).2
  exact lift execution guard body invariant rfl step preserve initial

end RealizedExec

namespace RealizationWP

/-- Add realization to a separately proved total loop specification. The source
proof supplies termination and its postconditions unchanged. The extra premises
establish only round admissibility and the invariant needed for further rounds. -/
theorem while_of_total
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    (total : Complexity.Language.TotalWP program (.while guard body) normal returned entry)
    (step : ∀ current, invariant current →
      RealizationWP program w depth guard (fun _ => False)
        (fun test afterGuard => if test then
          RealizationWP program w depth body (fun _ => True) (fun _ _ => True) afterGuard
          else True) current)
    (preserve : ∀ current afterGuard afterBody, invariant current →
      Complexity.Language.Exec program guard current afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal → invariant afterBody)
    (initial : invariant entry) :
    RealizationWP program w depth (.while guard body) normal returned entry := by
  obtain ⟨finish, control, execution, post⟩ := total
  exact ⟨finish, control, RealizedExec.while_of_exec execution step preserve initial, post⟩

/-- Reuse loop termination with ordinary local values and heap observations.
Guard/body admissibility and invariant preservation refer to the generated
source block observations. The shared rule performs the conversion to finite
source executions, so consumers do not supply an execution-tree adapter. -/
theorem while_observe_of_total
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w depth : Nat} {Γ : List Ty} {result : Ty} {Locals : Type}
    (view : Env Γ ≃ Locals)
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Locals → Heap → Prop}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {locals : Locals} {heap : Heap}
    (total : Complexity.Language.TotalWP program (.while guard body) normal returned
      ⟨view.symm locals, heap⟩)
    (guardRealizable : ∀ current currentHeap, invariant current currentHeap →
      RealizationWP program w depth guard (fun _ => False) (fun _ _ => True)
        ⟨view.symm current, currentHeap⟩)
    (bodyRealizable : ∀ current currentHeap afterGuard guardHeap,
      invariant current currentHeap →
      Complexity.Language.Stmt.observe view guard program current currentHeap =
        Part.some ((.returned true, afterGuard), guardHeap) →
      RealizationWP program w depth body (fun _ => True) (fun _ _ => True)
        ⟨view.symm afterGuard, guardHeap⟩)
    (preserve : ∀ current currentHeap afterGuard guardHeap afterBody bodyHeap,
      invariant current currentHeap →
      Complexity.Language.Stmt.observe view guard program current currentHeap =
        Part.some ((.returned true, afterGuard), guardHeap) →
      Complexity.Language.Stmt.observe view body program afterGuard guardHeap =
        Part.some ((.normal, afterBody), bodyHeap) → invariant afterBody bodyHeap)
    (initial : invariant locals heap) :
    RealizationWP program w depth (.while guard body) normal returned
      ⟨view.symm locals, heap⟩ := by
  have observation {τ : Ty} {stmt : Complexity.Language.Stmt signatures Γ τ}
      {start finish : Complexity.Language.State Γ} {control : Control τ}
      (execution : Complexity.Language.Exec program stmt start finish control) :
      Complexity.Language.Stmt.observe view stmt program (view start.locals) start.heap =
        Part.some ((control, view finish.locals), finish.heap) := by
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    simpa only [Equiv.symm_apply_apply] using execution
  apply while_of_total (invariant := fun current =>
    invariant (view current.locals) current.heap) total
  · intro current currentInvariant
    have guardProof : RealizationWP program w depth guard (fun _ => False)
        (fun _ _ => True) current := by
      simpa only [Equiv.symm_apply_apply] using
        guardRealizable (view current.locals) current.heap currentInvariant
    obtain ⟨afterGuard, guardControl, test, post⟩ := guardProof
    refine ⟨afterGuard, guardControl, test, ?_⟩
    cases guardControl with
    | normal => exact post
    | fault error => exact post
    | returned decision =>
        cases decision with
        | false => trivial
        | true =>
            simpa only [Equiv.symm_apply_apply] using
              bodyRealizable (view current.locals) current.heap
                (view afterGuard.locals) afterGuard.heap currentInvariant
                (observation test.erase)
  · intro current afterGuard afterBody currentInvariant test iteration
    exact preserve (view current.locals) current.heap (view afterGuard.locals) afterGuard.heap
      (view afterBody.locals) afterBody.heap currentInvariant
      (observation test) (observation iteration)
  · simpa only [Equiv.apply_symm_apply] using initial

end RealizationWP

end Ram.LanguageCompiler
