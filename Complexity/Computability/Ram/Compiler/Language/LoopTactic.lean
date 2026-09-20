/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop.Completion
import Complexity.Computability.Ram.Compiler.Language.CostBound.Locals
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop
import Lean.Elab.Tactic

/-!
# Resource proofs for named source loops

These tactics select the checked capture view and lexical preservation proofs
registered for the actual loop `Code` in the goal. They apply the existing
fixed-capture loop rules to supplied source block contracts. Native and raw
coordinate candidates are checked against those contracts, not selected by
guessing the shape of a mathematical value.

The cost entry consumes uniform guard/body certificates and an explicit remaining
iteration function. It leaves entry into the body, invariant preservation,
decrease, positivity and the initial invariant as mathematical goals.

The realization entry reuses a supplied source loop contract for termination.
Its precondition is separate from the resource invariant; extra frame facts are
not silently discarded. Besides the guard/body word and nesting proofs, callers
retain any nontrivial source postcondition consequences. Neither entry unfolds
callee implementations, assumes operation prices or searches for invariants.

The arena entry connects visible local-completion contracts to the same finite
execution in its goal. It selects only compiler coordinates and checked frames;
the caller supplies the state relation, prepared-body condition and completed
postcondition. Source effects and actual guard/body arena readiness remain goals.
-/

namespace Ram.LanguageCompiler.LoopTactic

open Lean Meta Elab Tactic

private def normalizedTarget : TacticM Lean.Expr := do
  return (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData

private def coordinates (head : Name) (position : Nat) :
    TacticM Complexity.Language.Syntax.LoopCoordinates := withMainContext do
  let target ← normalizedTarget
  unless target.isAppOf head do
    throwError "expected a {head} goal for a named source loop"
  let some statement := target.getAppArgs[position]? |
    throwError "expected a complete {head} goal for a named source loop"
  let statement := statement.consumeMData
  let .const code _ := statement.getAppFn |
    throwError "the goal must retain a registered source loop's Code declaration"
  let some information := Complexity.Language.Syntax.getLoopCoordinates? (← getEnv) code |
    throwError "the goal must retain a registered source loop's Code declaration"
  return information

private def withCaptureView (information : Complexity.Language.Syntax.LoopCoordinates)
    (action : Complexity.Language.Syntax.LoopCaptureCoordinates → TacticM Unit) :
    TacticM Unit := do
  let saved ← Tactic.saveState
  for (captures, index) in information.captures.zipIdx do
    try
      Term.withoutErrToSorry <| withoutRecover (action captures)
      return
    catch error =>
      if index + 1 = information.captures.size then throw error
      saved.restore
  throwError "the source loop has no registered capture view"

private def blockPredicates (specification : TSyntax `term) :
    TacticM (TSyntax `term × TSyntax `term × TSyntax `term) := do
  let proof ← Term.elabTermAndSynthesize specification none
  let some type ← whnfUntil (← inferType proof) ``Complexity.Language.Stmt.BlockSpec |
    throwErrorAt specification "expected a source block contract"
  let arguments := type.getAppArgs
  return (← Term.exprToSyntax arguments[4]!, ← Term.exprToSyntax arguments[5]!,
    ← Term.exprToSyntax arguments[6]!)

private def entryCoordinates (view : TSyntax `ident) (entry : TSyntax `term) :
    TacticM (TSyntax `term × TSyntax `term × TSyntax `term) := do
  let reduce (term : TSyntax `term) : TacticM (TSyntax `term) := do
    Term.exprToSyntax (← whnf (← Term.elabTermAndSynthesize term none))
  return (← reduce (← `(($view ($entry).locals).1)),
    ← reduce (← `(($view ($entry).locals).2)), ← reduce (← `(($entry).heap)))

private def cost (remaining guardSpec bodySpec guardCost bodyCost : TSyntax `term) :
    TacticM Unit := withMainContext do
  let information ← coordinates ``StmtCostBound 4
  let some entry := (← normalizedTarget).getAppArgs[5]? |
    throwError "expected a complete StmtCostBound goal for a named source loop"
  let entry ← Term.exprToSyntax entry
  let (invariant, _, guardPost) ← blockPredicates guardSpec
  let (bodyPre, bodyNormal, bodyReturned) ← blockPredicates bodySpec
  withCaptureView information fun captures => do
    let view := mkCIdent captures.view
    let guardFrame := mkCIdent captures.guardFrame
    let bodyFrame := mkCIdent captures.bodyFrame
    let (mutable, captured, heap) ← entryCoordinates view entry
    evalTactic (← `(tactic|
      apply StmtCostBound.while_contract_fixed_linear $view $guardFrame $bodyFrame
        $captured $guardSpec $bodySpec
        (invariant := $invariant) (guardPost := $guardPost)
        (bodyPre := $bodyPre) (bodyNormal := $bodyNormal) (bodyReturned := $bodyReturned)
        (remaining := $remaining)
        (mutable := $mutable) (heap := $heap)
        (guardCost := by intros; apply $guardCost)
        (bodyCost := by intros; apply $bodyCost)))

private def realize (guardSpec bodySpec specification : TSyntax `term) :
    TacticM Unit := withMainContext do
  let information ← coordinates ``RealizationWP 6
  let some entry := (← normalizedTarget).getAppArgs[9]? |
    throwError "expected a complete RealizationWP goal for a named source loop"
  let entry ← Term.exprToSyntax entry
  let (invariant, _, guardPost) ← blockPredicates guardSpec
  let (bodyPre, bodyNormal, bodyReturned) ← blockPredicates bodySpec
  withCaptureView information fun captures => do
    let view := mkCIdent captures.view
    let guardFrame := mkCIdent captures.guardFrame
    let bodyFrame := mkCIdent captures.bodyFrame
    let (mutable, captured, heap) ← entryCoordinates view entry
    evalTactic (← `(tactic|
      apply RealizationWP.while_contract_fixed_of_total $view $guardFrame $bodyFrame
        $captured $guardSpec $bodySpec
        (invariant := $invariant) (guardPost := $guardPost)
        (bodyPre := $bodyPre) (bodyNormal := $bodyNormal) (bodyReturned := $bodyReturned)
        (mutable := $mutable) (heap := $heap)))
    evalTactic (← `(tactic|
      case' total =>
        apply Complexity.Language.TotalWP.of_blockSpec $view
          (fun mutable => (mutable, $captured)) $specification
          (input := $mutable) (heap := $heap)
        case' normalPost =>
          intros
          first | assumption | trivial | contradiction | skip
        case' returnedPost =>
          intros
          first | assumption | trivial | contradiction | skip))

private def arena (stateRel prepared completed : TSyntax `term) : TacticM Unit :=
    withMainContext do
  let information ← coordinates ``ArenaReady 4
  let some completion := information.completion? |
    throwError "the named source loop has no registered local-completion coordinates"
  let view := mkCIdent completion.view
  let visible := mkCIdent completion.visible
  let entry := mkCIdent completion.entry
  let pending := mkCIdent completion.pending
  let reconstruct := mkCIdent completion.reconstruct
  let reconstructNone := mkCIdent completion.reconstructNone
  let guardFrame := mkCIdent completion.guardFrame
  let bodyFrame := mkCIdent completion.bodyFrame
  let stoppedGuard := mkCIdent completion.stoppedGuard
  let pendingEval := mkCIdent completion.pendingEval
  evalTactic (← `(tactic|
    apply ArenaReady.while_completion_of_exec $view $visible $entry $pending $reconstruct
      $reconstructNone $guardFrame $bodyFrame
      (by
        intro state value stopped
        apply $stoppedGuard state value
        simpa only [← $pendingEval, Equiv.symm_apply_apply] using stopped)
      (stateRel := $stateRel) (prepared := $prepared) (completed := $completed)))

/-- Compose uniform guard/body costs for the named loop in the goal.
The remaining-iteration function is explicit; source invariants are inferred
from the supplied block contracts. Mathematical loop obligations remain goals. -/
syntax (name := sourceLoopCost)
  "ram_source_loop_cost" " (" &"remaining" " := " term ")"
  " using " term:max ", " term:max &"costs" term:max ", " term : tactic

elab_rules : tactic
  | `(tactic| ram_source_loop_cost (remaining := $remaining)
      using $guardSpec, $bodySpec costs $guardCost, $bodyCost) =>
    cost remaining guardSpec bodySpec guardCost bodyCost

/-- Add word/nesting realization to a named loop using its independent source
block contract for totality. The source precondition and the resource invariant
remain separate obligations; routine true/false postconditions are discharged. -/
syntax (name := sourceLoopRealize)
  "ram_source_loop_realize" " using " term:max ", " term:max &"total" term : tactic

elab_rules : tactic
  | `(tactic| ram_source_loop_realize using $guardSpec, $bodySpec total $specification) =>
    realize guardSpec bodySpec specification

/-- Connect visible completion contracts to arena readiness of the actual finite
execution in the goal. Only the named loop's compiler coordinates and frames are
automatic. The supplied mathematical relations determine the remaining source
contract, guard/body readiness, completed-guard readiness and entry obligations;
no new termination proof or inferred effect/capacity premise is introduced. -/
syntax (name := sourceLoopArena)
  "ram_source_loop_arena" " (" &"stateRel" " := " term ")"
  " (" &"prepared" " := " term ")" " (" &"completed" " := " term ")" : tactic

elab_rules : tactic
  | `(tactic| ram_source_loop_arena (stateRel := $stateRel)
      (prepared := $prepared) (completed := $completed)) =>
    arena stateRel prepared completed

end Ram.LanguageCompiler.LoopTactic
