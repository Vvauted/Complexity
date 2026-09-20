/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.While.Models
import Complexity.Language.Eval.Locals.While.Represented

/-!
# Mathematical local contracts for represented while loops

The local model observes every selected source binding at the current heap.
Guard and normal-body correspondence reuse the operation proof trace of that
same named loop. They do not need a total mathematical model of the surrounding
function, emit helper calls, or change the source program.

The generated contract asks for an invariant and well-founded progress of the
mathematical step. Arrays retained between rounds use the actual operation
preservation contracts; fixed source handles alone do not preserve contents.
This pass describes normal rounds, not local completion or function returns.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

def WhileRegistration.site (loop : WhileRegistration) : TermElabM ActualWhileSite := do
  let site ← loop.toWhileLocalRegistration.site
  if site.localReturn then
    throwError "a locally completed while cannot use a normal-round model contract"
  return site

private def WhileRegistration.slots (loop : WhileRegistration) : TermElabM (Array Nat) :=
  loop.toWhileLocalRegistration.slots

private def WhileRegistration.select (loop : WhileRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) :=
  loop.toWhileLocalRegistration.select locals

/-- Prove one actual guard or body observation. Complete source coordinates
remain in the execution equation; only the mathematical relation projects them. -/
private def whileRoundDeclaration (loop : WhileRegistration) (guardRound : Bool)
    (ranges : Array RangeRegistration) : TermElabM Syntax := do
  let site ← loop.site
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let name := member (if guardRound then `guard_model else `body_model)
  let code := member (if guardRound then `Guard else `Body)
  let observed := member (if guardRound then `guard_observe else `body_observe)
  let equation := member (if guardRound then `guard_eq else `body_eq)
  let view := member `View
  let localsType := member `Locals
  let modelType := member `Model
  let modelRel := member `modelRel
  let modelGuard := member `modelGuard
  let modelStep := member `modelStep
  let program := mkIdent (site.name.getPrefix ++ `program)
  let model := loop.state.name
  let related := loop.state.relationName
  let locals := mkIdent (← mkFreshUserName `locals)
  let heap := mkIdent (← mkFreshUserName `heap)
  let output := mkIdent (← mkFreshUserName `output)
  let finish := mkIdent (← mkFreshUserName `finish)
  let finite := mkIdent (← mkFreshUserName `finite)
  let executed := mkIdent (← mkFreshUserName `executed)
  let finalRelated := mkIdent (← mkFreshUserName `finalRelated)
  let selected ← loop.select ⟨locals.raw⟩
  let fields ← sourceFields site.scope.size ⟨locals.raw⟩
  let positions ← loop.slots
  let representation ← termOfExpr loop.state.type.representation
  let stateType ← termOfExpr loop.state.type.nativeType
  let stateCore ← termOfExpr (coreTypeExpr loop.state.type.coreTy)
  let stateValue ← value [loop.state] ⟨model.raw⟩
  let mut initialTactics := #[]
  let mut relations := #[]
  if loop.state.type.isIdentity then
    initialTactics := #[
      ← `(tactic| change $model:ident = $selected at $related:ident),
      ← `(tactic| subst $model:ident),
      ← `(tactic| let $model:ident : $modelType:ident := $selected)]
  else
    relations := #[⟨related.getId, loop.state.type, ⟨related.raw⟩⟩]
  let known := #[(loop.state.rawName.getId, selected)]
  let roundResult := if guardRound then loop.guardResult else loop.returned
  let trace := if guardRound then loop.guard else loop.body
  let control ← if guardRound then
      `(Complexity.Language.Control.returned ($modelGuard:ident $model:ident))
    else `(Complexity.Language.Control.normal)
  let finalModel ← if guardRound then `($model:ident)
    else `($modelStep:ident $model:ident)
  let finiteType ← `(∃ ($output:ident : $localsType:ident) ($finish:ident : Complexity.Language.Heap),
    Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $locals:ident $heap:ident = Part.some (($control, $output:ident), $finish:ident) ∧
    $modelRel:ident $finalModel $output:ident $finish:ident)
  let roundFinish : TraceFinish := fun context => do
    let scalarFacts ← context.scalarEqualities.mapM fun fact =>
      `(Lean.Parser.Tactic.simpLemma| $fact:term)
    if guardRound then
      let guardModel ← loop.guardResult.requireModel
      let rawGuard := resolveRaw guardModel.rawModel context.known
      let guardObserved ← observationAt loop.guardResult context.heap context.relations
      let stateObserved ← observationAt stateValue context.heap context.relations
      let guardEqual := mkIdent (← mkFreshUserName `guardEqual)
      let eta := mkIdent (← mkFreshUserName `localsEta)
      let rebuilt ← sourceTuple fields
      let mut etaProof ← `(Subsingleton.elim _ _)
      for _ in site.scope do etaProof ← `(Prod.ext rfl $etaProof)
      return #[
        ← `(tactic| have $guardEqual:ident : $modelGuard:ident $model:ident = $rawGuard := by
          exact $guardObserved),
        ← `(tactic| have $eta:ident : $rebuilt = $locals:ident := $etaProof),
        ← `(tactic| exact ⟨$locals:ident, $(context.heap),
          (by simp only [← $guardEqual:ident, $eta:ident, $scalarFacts,*]),
          (show ($representation : Complexity.Language.Representation
            $stateType $stateCore).Rel $model:ident $selected $(context.heap) from $stateObserved)⟩)]
    else
      let returned ← loop.returned.requireModel
      let rawState := resolveRaw returned.rawModel context.known
      let returnedObserved ← observationAt loop.returned context.heap context.relations
      let mut afterFields := fields
      for binding in loop.captured, position in positions, index in [:loop.captured.size] do
        if binding.mutable then
          afterFields := afterFields.set! position
            (← fieldProjection loop.captured.size index rawState)
      let after ← sourceTuple afterFields
      let selectedAfter ← loop.select after
      return #[← `(tactic| exact ⟨$after, $(context.heap),
        (by first | rfl | simp only [$scalarFacts,*]),
        (show ($representation : Complexity.Language.Representation
          $stateType $stateCore).Rel ($modelStep:ident $model:ident)
            $selectedAfter $(context.heap) from $returnedObserved)⟩)]
  let proof := initialTactics ++ #[← `(tactic| rw [$observed:ident, $equation:ident])] ++
    (← relationTrace trace roundResult ⟨heap.raw⟩ relations known true ranges (some roundFinish))
  let proof ← proof.mapM fun tactic => `(tactic| all_goals $tactic:tactic)
  let normal ← if guardRound then `(fun _ _ _ _ => False)
    else `(fun _ _ output finish => $modelRel:ident ($modelStep:ident $model:ident) output finish)
  let returned ← if guardRound then
      `(fun _ _ again output finish => again = $modelGuard:ident $model:ident ∧
        $modelRel:ident $model:ident output finish)
    else `(fun _ _ _ _ _ => False)
  let resultProof ← if guardRound then `(And.intro rfl $finalRelated:ident)
    else `($finalRelated:ident)
  return (← `(command|
    /-- The mathematical round describes the actual named source block and its final heap. -/
    theorem $(whileDeclarationName name):ident ($model:ident : $modelType:ident) :
        Complexity.Language.Stmt.BlockSpec
          (fun locals => Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident locals)
          ($modelRel:ident $model:ident) $normal $returned := by
      intro $locals:ident $heap:ident $related:ident
      have $finite:ident : $finiteType := by
        $proof:tactic*
      obtain ⟨$output:ident, $finish:ident, $executed:ident, $finalRelated:ident⟩ := $finite:ident
      exact Part.TotalCorrectness.stateT_triple_of_eq $executed:ident $resultProof)).raw

/-- Generate a mathematical state, its field observations, checked rounds and
the invariant interface for one original named while. -/
def whileDeclarations (loop : WhileRegistration)
    (ranges : Array RangeRegistration) : TermElabM (Array Syntax) := do
  let site ← loop.site
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let modelType := member `Model
  let modelRel := member `modelRel
  let modelGuard := member `modelGuard
  let modelStep := member `modelStep
  let localsType := member `Locals
  let model := loop.state.name
  let mut declarations ← whileModelDeclarations loop.toWhileLocalRegistration
  declarations := declarations ++ #[
    (← `(command|
      /-- The mathematical guard of a single actual loop round. -/
      def $(whileDeclarationName modelGuard):ident : $modelType:ident → Bool := $(loop.guardNative))).raw,
    (← `(command|
      /-- The mathematical local update of a normal actual loop round. -/
      def $(whileDeclarationName modelStep):ident : $modelType:ident → $modelType:ident := $(loop.bodyNative))).raw]
  declarations := declarations.push (← whileRoundDeclaration loop true ranges)
  declarations := declarations.push (← whileRoundDeclaration loop false ranges)
  let contract := member `model_contract
  let spec := member `model_spec
  let view := member `View
  let guard := member `Guard
  let body := member `Body
  let code := member `Code
  let guardModel := member `guard_model
  let bodyModel := member `body_model
  let program := mkIdent (site.name.getPrefix ++ `program)
  let invariant := mkIdent (← mkFreshUserName `invariant)
  let relation := mkIdent (← mkFreshUserName `relation)
  let wellFounded := mkIdent (← mkFreshUserName `wellFounded)
  let preserved := mkIdent (← mkFreshUserName `preserved)
  let decreases := mkIdent (← mkFreshUserName `decreases)
  let initial := mkIdent (← mkFreshUserName `initial)
  let parameters ← pure #[
    ← `(bracketedBinder| ($invariant:ident : $modelType:ident → Prop)),
    ← `(bracketedBinder| {$relation:ident : $modelType:ident → $modelType:ident → Prop}),
    ← `(bracketedBinder| ($wellFounded:ident : WellFounded $relation:ident)),
    ← `(bracketedBinder| ($preserved:ident : ∀ model, $invariant:ident model →
      $modelGuard:ident model = true → $invariant:ident ($modelStep:ident model))),
    ← `(bracketedBinder| ($decreases:ident : ∀ model, $invariant:ident model →
      $modelGuard:ident model = true → $relation:ident ($modelStep:ident model) model)),
    ← `(bracketedBinder| ($model:ident : $modelType:ident)),
    ← `(bracketedBinder| ($initial:ident : $invariant:ident $model:ident))]
  declarations := declarations.push (← `(command|
    /-- Mathematical invariant preservation and descent prove the original named loop. -/
    theorem $(whileDeclarationName contract):ident $parameters:bracketedBinder* :
        Complexity.Language.Stmt.BlockSpec
          (fun locals => Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident locals)
          ($modelRel:ident $model:ident)
          (fun _ _ output finish => ∃ finalModel,
            $modelRel:ident finalModel output finish ∧ $invariant:ident finalModel ∧
              $modelGuard:ident finalModel = false)
          (fun _ _ _ _ _ => False) := by
      exact Complexity.Language.Stmt.observe_while_model_contract
        $view:ident $program:ident $guard:ident $body:ident $modelRel:ident
        $modelGuard:ident $modelStep:ident $guardModel:ident (fun model _ => $bodyModel:ident model)
        $invariant:ident $wellFounded:ident $preserved:ident $decreases:ident
        $model:ident $initial:ident)).raw
  let mut arguments : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut values : Array (TSyntax `term) := #[]
  for binding in site.scope do
    let name := binding.proofName
    let type ← actualTypeTerm binding.type
    arguments := arguments.push (← `(bracketedBinder| ($name:ident : $type)))
    values := values.push ⟨name.raw⟩
  let entry ← sourceTuple values
  let action := Lean.Syntax.mkApp ⟨(mkIdent site.name).raw⟩ values
  let post := mkIdent (← mkFreshUserName `post)
  let resultType ← termOfExpr (coreTypeExpr site.result)
  declarations := declarations.push (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Use the mathematical loop contract with the actual source continuation. -/
    theorem $(whileDeclarationName spec):ident $parameters:bracketedBinder* $arguments:bracketedBinder*
        ($post:ident : Std.Do.PostCond
          (Complexity.Language.Control $resultType × $localsType:ident)
          (.arg Complexity.Language.Heap .pure)) :
        Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
          $action
          (fun heap => ⟨$modelRel:ident $model:ident $entry heap ∧
            ∀ finalModel output finish, $modelRel:ident finalModel output finish →
              $invariant:ident finalModel → $modelGuard:ident finalModel = false →
                (($post:ident).1 (.normal, output) finish).down⟩) $post:ident := by
      change Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
        (Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident $entry) _ _
      apply (Complexity.Language.Stmt.BlockSpec.spec
        ($contract:ident $invariant:ident $wellFounded:ident $preserved:ident $decreases:ident
          $model:ident $initial:ident) $entry $post:ident).mono
      · intro heap condition
        refine ⟨condition.1, ?_, ?_⟩
        · rintro output finish ⟨finalModel, represented, valid, stopped⟩
          exact condition.2 finalModel output finish represented valid stopped
        · intro _ _ _ impossible
          exact impossible.elim
      · exact Std.Do.PostCond.entails.refl _)).raw
  return declarations

end Internal

end Complexity.Language.Syntax.Represented
