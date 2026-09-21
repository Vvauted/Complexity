/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Range.Uniform
import Lean.Elab.Tactic

/-!
# Named represented-range arena cost proofs

Select the already proved round contracts by the actual loop `Code` and the
supplied state relation. Their types determine the mathematical transition and
range parameters. Source observation facts may instantiate captured mathematical
inputs; they never reconstruct a value from its runtime handle.

Uniform component certificates supply all operation costs. The shared range
rule supplies loop composition; readiness, capacity and enclosing-function
costs are not consequences of this tactic.
-/

namespace Ram.LanguageCompiler.Arena.RangeCostTactic

open Lean Meta Elab Tactic

private def roundProof (name : Name) (facts : Array (TSyntax `term)) :
    TacticM (TSyntax `term) := do
  let supplied ← facts.mapM fun fact => `(tactic| have := $fact)
  `(by
    $supplied:tactic*
    intros
    apply $(mkCIdent name)
    all_goals assumption)

private def rangeCost (related running : TSyntax `term)
    (facts : Array (TSyntax `term)) (guardCost bodyCost : TSyntax `term) :
    TacticM Unit := focus <| withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  unless target.isAppOf ``StmtArenaCostBound do
    throwError "expected a StmtArenaCostBound goal for a named source range"
  let statement := target.getAppArgs[7]!.consumeMData
  let .const code _ := statement.getAppFn |
    throwError "the goal must retain the source range's Code declaration"
  let some coordinates := Complexity.Language.Syntax.getLoopCoordinates? (← getEnv) code |
    throwError "the goal must retain a registered source range's Code declaration"
  let relatedProof ← Term.elabTermAndSynthesize related none
  let relation := (← instantiateMVars (← inferType relatedProof)).consumeMData
  let some rounds := coordinates.rangeRounds.find? fun rounds =>
      relation.getAppFn.isConstOf rounds.stateRel |
    throwErrorAt related "the supplied relation does not select published round contracts for this range"
  unless rounds.localCompletion do
    throwError "this entry requires a saved local result; use the explicit range rule for normal or function-returning ranges"
  let some completion := coordinates.completion? |
    throwError "the source range has no registered local-completion coordinates"
  let arguments := relation.getAppArgs
  unless arguments.size ≥ 4 do
    throwErrorAt related "expected a range relation applied to index, mathematical state, locals and heap"
  let stateRel ← Term.exprToSyntax
    (mkAppN relation.getAppFn (arguments.extract 0 (arguments.size - 4)))
  let start ← Term.exprToSyntax arguments[arguments.size - 4]!
  let mutable ← Term.exprToSyntax arguments[arguments.size - 3]!
  let locals ← Term.exprToSyntax arguments[arguments.size - 2]!
  let heap ← Term.exprToSyntax arguments[arguments.size - 1]!
  let pendingAtom ← forallTelescope (← getConstInfo completion.pendingEval).type fun _ equation => do
    let some (_, lhs, _) := equation.eq? |
      throwError "the registered pending-coordinate theorem must be an equality"
    unless lhs.isAppOf ``Complexity.Language.Atom.eval do
      throwError "the registered pending-coordinate theorem must expose the actual atom"
    Term.exprToSyntax lhs.getAppArgs[2]!
  let view := mkCIdent completion.view
  let stoppedGuard := mkCIdent completion.stoppedGuard
  let pendingEval := mkCIdent completion.pendingEval
  let guardRel ← roundProof rounds.guardRel facts
  let bodyRel ← roundProof rounds.bodyRel facts
  evalTactic (← `(tactic| apply StmtArenaCostBound.mono))
  evalTactic (← `(tactic|
    apply StmtArenaCostBound.while_range_completion_rel_linear
      (view := $view) (pending := $pendingAtom) (stoppedGuard := $stoppedGuard)
      (stateRel := $stateRel) (guardRel := $guardRel) (bodyRel := $bodyRel)
      (guardCost := by intro locals heap; exact $guardCost ⟨($view).symm locals, heap⟩)
      (bodyCost := by intro locals heap; exact $bodyCost ⟨($view).symm locals, heap⟩)
      (start := $start) (mutable := $mutable) (locals := $locals) (heap := $heap)))
  evalTactic (← `(tactic| case' represented => exact $related))
  evalTactic (← `(tactic| case' running => simpa only [$pendingEval:ident] using $running))
  evalTactic (← `(tactic|
    all_goals try
      simp (config := { failIfUnchanged := false }) only
        [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one] <;> omega))

/-- Compose uniform arena costs for a named represented range using its existing
state relation and empty-pending proof. Optional `facts` supply captured source
observations required by the published rounds. Uniform guard/body certificates
are functions of the actual initial state. Range positivity and a nontrivial
comparison with the requested bound remain goals; no invariant, capacity or
operation price is assumed. -/
syntax (name := sourceRangeArenaCost)
  "ram_source_range_arena_cost" " using " term:max ", " term:max
  ppSpace &"costs" ppSpace term:max ", " term : tactic

@[inherit_doc sourceRangeArenaCost]
syntax (name := sourceRangeArenaCostWithFacts)
  "ram_source_range_arena_cost" " using " term:max ", " term:max
  ppSpace &"facts" ppSpace "[" term,* "]" ppSpace &"costs" ppSpace term:max ", " term : tactic

elab_rules : tactic
  | `(tactic| ram_source_range_arena_cost using $related, $running
      facts [$observations:term,*] costs $guardCost, $bodyCost) =>
    rangeCost related running observations.getElems guardCost bodyCost
  | `(tactic| ram_source_range_arena_cost using $related, $running
      costs $guardCost, $bodyCost) =>
    rangeCost related running #[] guardCost bodyCost

end Ram.LanguageCompiler.Arena.RangeCostTactic
