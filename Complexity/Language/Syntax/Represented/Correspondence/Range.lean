/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic
import Complexity.Language.Eval.Locals.Range.LocalReturn

/-!
# Correspondence for represented finite ranges

Relate a prepared mathematical fold or completing `forIn` to its actual named
source range, retaining local completion or a genuine function return.
Lexical slot alignment and the existing range rules retain
complete source coordinates, actual body control and intermediate heap observations.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

-- Publish the proof where it is checked, rather than abstracting a later local
-- hypothesis (which would merely assume the round it is meant to establish).
private def publishRangeRound (source suffix : Name) (steps : Syntax) :
    Lean.Elab.Tactic.TacticM Unit := Lean.Elab.Tactic.withMainContext do
  let sourceName ← resolveGlobalConstNoOverload (mkIdent source)
  let name := sourceName.getPrefix ++ suffix
  let goal ← Lean.Elab.Tactic.getMainGoal
  let remaining ← Lean.Elab.Tactic.run goal
    (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic steps))
  unless remaining.isEmpty do
    throwError "the represented range round has unsolved goals"
  let value ← instantiateMVars (mkMVar goal)
  let type ← instantiateMVars (← goal.getType)
  let closed ← Closure.mkValueTypeClosure type value (zetaDelta := true)
  let shared := ShareCommon.shareCommon' #[closed.type, closed.value]
  addDecl (.thmDecl {
    name, levelParams := closed.levelParams.toList
    type := shared[0]!, value := shared[1]! })
  addDocStringCore name
    "One represented range round of the actual source loop, with its captured input and heap relations."
  goal.assign (mkAppN (mkConst name closed.levelArgs.toList) closed.exprArgs)

-- Internal wrapper: keep the already generated tactic block as syntax instead
-- of serializing and compiling it again inside `run_tac`.
syntax (name := representedRangeRound)
  "represented_range_round " ident ppSpace ident " => " Lean.Parser.Tactic.tacticSeq : tactic

elab_rules : tactic
  | `(tactic| represented_range_round $source:ident $suffix:ident => $steps:tacticSeq) =>
      publishRangeRound source.getId suffix.getId steps

-- Give the shared relation a name as well, so the round contracts need not
-- repeat its source-coordinate formula in every precondition and postcondition.
syntax (name := representedRangeRelation)
  "represented_range_relation " ident ppSpace ident " => " term : term

@[term_elab representedRangeRelation]
private def elabRangeRelation : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let `(represented_range_relation $source:ident $suffix:ident => $body:term) := stx
    | throwUnsupportedSyntax
  let sourceName ← resolveGlobalConstNoOverload source
  let name := sourceName.getPrefix ++ suffix.getId
  let value ← Lean.Elab.Term.elabTermAndSynthesize body expectedType?
  let result ← mkAuxDefinition name (← inferType value) value (zetaDelta := true) (compile := false)
  addDocStringCore name
    "The same heap-indexed mathematical state relation used by this source range's round contracts."
  return result

-- Register only the declarations already checked above. Resource entries can
-- select this exact relation without reconstructing or proving another round.
private def registerRangeRounds (code stateRel guardRel bodyRel : Name)
    (localCompletion : Bool) : Lean.Elab.Tactic.TacticM Unit := do
  registerLoopRangeRounds (← resolveGlobalConstNoOverload (mkIdent code)) {
    stateRel := ← resolveGlobalConstNoOverload (mkIdent stateRel)
    guardRel := ← resolveGlobalConstNoOverload (mkIdent guardRel)
    bodyRel := ← resolveGlobalConstNoOverload (mkIdent bodyRel)
    localCompletion }

private def rangeRoundRegistration (code stateRel guardRel bodyRel : TSyntax `ident)
    (localCompletion : Bool) : TermElabM (TSyntax `tactic) := do
  let registration := mkCIdent ``registerRangeRounds
  let codeName : TSyntax `term := quote code.getId
  let stateRelName : TSyntax `term := quote stateRel.getId
  let guardRelName : TSyntax `term := quote guardRel.getId
  let bodyRelName : TSyntax `term := quote bodyRel.getId
  let completion : TSyntax `term := quote localCompletion
  `(tactic| run_tac
    $registration:ident $codeName $stateRelName $guardRelName $bodyRelName $completion)

/-- The source emitter has already selected the named loop. Only its actual
arguments are read from the elaborated goal; transparent proof locals preserve
anonymous coordinates and frozen endpoints without interpreting source text. -/
private def bindActualRangeArguments (action : Name) (names : Array Name) :
    Lean.Elab.Tactic.TacticM Unit := Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let collect : StateT (Array (Array Expr)) MetaM Unit :=
    target.forEach' fun expression => do
      let expression := expression.consumeMData
      let arguments := expression.getAppArgs
      if expression.getAppFn.consumeMData.isConstOf action && arguments.size >= names.size then
        let arguments := arguments.extract 0 names.size
        unless arguments.any (·.hasLooseBVars) do modify (·.push arguments)
        return false
      return true
  let (_, occurrences) ← collect.run #[]
  let some arguments := occurrences[0]?
    | throwError "the actual range invocation is not exposed in this proof goal"
  unless occurrences.all (· == arguments) do
    throwError "the proof goal contains different invocations of the selected range"
  let mut goal := goal
  for name in names, argument in arguments do
    let type ← goal.withContext (inferType argument)
    let next ← goal.define name type argument
    let (_, next) ← next.intro1P
    goal := next
  Lean.Elab.Tactic.replaceMainGoal [goal]

def RangeRegistration.site (range : RangeRegistration) : TermElabM ActualRangeSite :=
  match range.site? with
  | some site => pure site
  | none => throwError "the prepared range has no checked actual source site"

/-- Align source declarations by lexical occurrence, not by a name lookup.
Anonymous Core coordinates remain in the full source scope. -/
def sourceBindingSlots (bindings : Array Binding)
    (entryScope scope : Array SourceLocal) : TermElabM (Array Nat) := do
  let mut used : NameSet := {}
  let mut positions := #[]
  for binding in bindings do
    let some entry := entryScope.find? fun entry =>
        entry.name == some binding.name.getId && !used.contains entry.proofName.getId
      | throwError "the prepared block contains an unmatched lexical slot"
    unless entry.type == binding.type.coreTy do
      throwError "the source block's lexical entry does not match its prepared slots"
    let some position := scope.findIdx? fun actual =>
        actual.proofName.getId == entry.proofName.getId
      | throwError "the source block dropped an entry coordinate"
    positions := positions.push position
    used := used.insert entry.proofName.getId
  return positions

def RangeRegistration.slots (range : RangeRegistration) : TermElabM (Array Nat) := do
  let site ← range.site
  sourceBindingSlots range.captured site.entryScope site.scope

/-- Source locals use Core's product spine, including its final Unit. -/
def sourceFields (count : Nat) (locals : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  let mut remaining := locals
  let mut fields := #[]
  for _ in [:count] do
    fields := fields.push (← `(($remaining).1))
    remaining ← `(($remaining).2)
  return fields

def sourceTuple (fields : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let mut result ← `(())
  for field in fields.reverse do result ← `(($field, $result))
  return result

def RangeRegistration.selectState (range : RangeRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let site ← range.site
  let fields ← sourceFields site.scope.size locals
  let positions ← range.slots
  fieldsTerm (← positions.toList.mapM fun index =>
    match fields[index]? with
    | some field => pure field
    | none => throwError "the selected range coordinate is outside its actual locals")

/-- A function return is actual source control, not a saved local-result slot. -/
def RangeRegistration.returnsFromFunction (range : RangeRegistration) : TermElabM Bool := do
  match range.model with
  | .fold .. => return false
  | .completion .. => return (← range.site).pendingSlot?.isNone

/-- Read the actual saved or returned result beside the actual final state;
the mathematical result never reconstructs a source handle. -/
def RangeRegistration.select (range : RangeRegistration) (locals : TSyntax `term)
    (returned? : Option (TSyntax `term) := none) :
    TermElabM (TSyntax `term) := do
  let state ← range.selectState locals
  match range.model with
  | .fold .. => pure state
  | .completion .. =>
      let site ← range.site
      let some position := site.pendingSlot? | do
        let some returned := returned?
          | throwError "a returning range requires its actual source result"
        return ← `(($returned, $state))
      let fields ← sourceFields site.scope.size locals
      let some pending := fields[position]?
        | throwError "the completion coordinate is outside the actual range locals"
      `(($pending, $state))

private structure RangePendingProof where
  entry : Array (TSyntax `tactic)
  current : Array (TSyntax `tactic)
  entryRules : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)
  currentRules : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)

/-- Assemble the already prepared proof steps without one deeply nested
quotation. The statement and tactic order are unchanged. -/
private def rangeSummaryProof (name : TSyntax `ident) (statement : TSyntax `term)
    (steps : Array (TSyntax `tactic)) : TermElabM (TSyntax `tactic) :=
  `(tactic| have $name:ident : $statement := by
    $steps:tactic*)

private def rangeRoundProof (name : TSyntax `ident) (statement : TSyntax `term)
    (steps : Array (TSyntax `tactic)) (source suffix : TSyntax `ident)
    (publish : Bool) : TermElabM (TSyntax `tactic) := do
  let steps ← if publish then
      pure #[← `(tactic| represented_range_round $source:ident $suffix:ident =>
        $steps:tactic*)]
    else pure steps
  rangeSummaryProof name statement steps

private def rangePendingProof (site : ActualRangeSite)
    (arguments fields : Array (TSyntax `term)) (running : TSyntax `ident) :
    TermElabM RangePendingProof := do
  let some pendingSlot := site.pendingSlot?
    | return ⟨#[], #[← `(tactic| skip)], #[], #[]⟩
  let some entryPending := arguments[pendingSlot]?
    | throwError "the pending range result has no actual entry coordinate"
  let some currentPending := fields[pendingSlot]?
    | throwError "the pending range result is outside its source locals"
  let pendingEntry := mkIdent (← mkFreshUserName `rangePendingEntry)
  let pendingCurrent := mkIdent (← mkFreshUserName `rangePendingCurrent)
  return {
    entry := #[← `(tactic| let $pendingEntry:ident : $entryPending = none := by rfl)]
    current := #[← `(tactic|
      have $pendingCurrent:ident : $currentPending = none := $running:ident)]
    entryRules := #[← `(Lean.Parser.Tactic.simpLemma| $pendingEntry:ident)]
    currentRules := #[← `(Lean.Parser.Tactic.simpLemma| $pendingCurrent:ident)] }

/-- Choose the existing loop theorem by actual source completion behavior.
Both paths consume the generated guard and body with their actual control. -/
private def rangeLoopProof (site : ActualRangeSite) (returnsFromFunction : Bool)
    (completionRep nativeStep start stop stride initialState entry heap initial : TSyntax `term)
    (stateRel guardRel bodyRel positive control after finish executed outcome : TSyntax `ident) :
    TermElabM (Array (TSyntax `tactic)) := do
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let view := member `View
  let program := mkIdent (site.name.getPrefix ++ `program)
  let guard := member `Guard
  let body := member `Body
  if let some position := site.pendingSlot? then
    let stoppedGuard := member `guard_completed
    let pendingAtom ← `(Complexity.Language.Atom.var $(← liftMacroM (Core.variableTerm position)))
    return #[← `(tactic|
      obtain ⟨$after:ident, $finish:ident, $executed:ident, $outcome:ident⟩ :=
        Complexity.Language.Stmt.observe_while_completion_rel_forIn_range_step
          $view:ident $program:ident $guard:ident $body:ident $pendingAtom $stoppedGuard:ident
          $stop $stride $positive:ident $stateRel:ident $completionRep $nativeStep
          $guardRel:ident $bodyRel:ident $start $initialState $entry $heap $initial (by rfl))]
  let guardAdapter ← `(by
    intro index state locals heap related
    obtain ⟨after, finish, executed, retained, _⟩ :=
      $guardRel:ident index state locals heap related rfl
    exact ⟨after, finish, executed, retained⟩)
  let bodyAdapter ← if returnsFromFunction then `(by
      intro index state locals heap inside related
      exact $bodyRel:ident index state locals heap inside related rfl)
    else `(by
      intro index state locals heap inside related
      obtain ⟨after, finish, executed, retained, _⟩ :=
        $bodyRel:ident index state locals heap inside related rfl
      exact ⟨Complexity.Language.Control.normal, after, finish, executed, retained, trivial⟩)
  let proof ← `(tactic|
    obtain ⟨$control:ident, $after:ident, $finish:ident, $executed:ident, $outcome:ident⟩ :=
      Complexity.Language.Stmt.observe_while_rel_forIn_range_step
        $view:ident $program:ident $guard:ident $body:ident
        $stop $stride $positive:ident $stateRel:ident $completionRep $nativeStep
        $guardAdapter $bodyAdapter $start $initialState $entry $heap $initial)
  return #[proof]

/-- Relate the loop outcome to its prepared mathematical result. Only a normal
fold erases the completion flag; a completion model keeps it in the result. -/
private def rangeResultProof (range : RangeRegistration)
    (substitutions : Array (Name × TSyntax `term))
    (bodyNative completionCore start stop stride initialState resultModel selected finish : TSyntax `term)
    (positive outcome observed : TSyntax `ident) :
    TermElabM (Array (TSyntax `tactic) × Array (TSyntax `tactic)) := do
  let type ← termOfExpr range.result.type.nativeType
  let core ← termOfExpr (coreTypeExpr range.result.type.coreTy)
  let representation ← termOfExpr range.result.type.representation
  let statement ← `(($representation : Complexity.Language.Representation $type $core).Rel
    $resultModel $selected $finish)
  match range.model with
  | .completion resultType embedding mutableStep initialMutable =>
      let embedding := resolveRaw embedding substitutions
      let mutableStep := resolveRaw mutableStep substitutions
      let initialMutable := resolveRaw initialMutable substitutions
      let returnedType ← termOfExpr resultType.nativeType
      let stateType ← termOfExpr range.state.type.nativeType
      let equal := mkIdent (← mkFreshUserName `rangeCompletionEqual)
      let nativeRange ← `(({
        start := $start, stop := $stop
        step := $stride, step_pos := $positive:ident } : Std.Legacy.Range))
      let fullResult ← `(let outcome := Id.run (forIn (m := Id)
          $nativeRange
          ((none, ($start, $initialState)) : Option $returnedType × (Nat × $stateType))
          (fun index running =>
            let iteration := $bodyNative index running.2.2
            Option.elim iteration.1
              (pure (ForInStep.yield (none, (index + $stride, iteration.2))))
              (fun returned => pure (ForInStep.done (some returned, (index, iteration.2))))))
        (outcome.1, outcome.2.2))
      let proof ← `(tactic|
        have $observed:ident : $statement := by
          have $equal:ident : $fullResult = $resultModel :=
            Complexity.Language.Stmt.forIn_range_step_completion_eq
              $bodyNative $mutableStep $embedding
              (by
                intro index mutable
                first
                | rfl
                | dsimp only [Id.run, Id.instMonad, Pure.pure, Bind.bind, Option.elim]
                  repeat' first | rfl | split)
              $start $stop $stride $positive:ident $initialMutable
          rw [← $equal:ident]
          exact ⟨($outcome:ident).2, ($outcome:ident).1.1⟩)
      return (#[← `(tactic| skip)], #[proof])
  | .fold embedding mutableStep initialMutable indices =>
      let embedding := resolveRaw embedding substitutions
      let mutableStep := resolveRaw mutableStep substitutions
      let initialMutable := resolveRaw initialMutable substitutions
      let indices := resolveRaw indices substitutions
      let equal := mkIdent (← mkFreshUserName `rangeFoldEqual)
      let normalize := #[
        ← `(tactic| simp only [Option.elim_none] at $outcome:ident),
        ← `(tactic| rw [Complexity.Language.Stmt.forIn_range_step_yield_eq_foldl
          (α := Complexity.Language.Value $completionCore) $bodyNative
          $start $stop $stride $positive:ident $initialState] at $outcome:ident),
        ← `(tactic| simp only [Id.run] at $outcome:ident)]
      let proof ← `(tactic|
        have $observed:ident : $statement := by
          have $equal:ident : ($indices).foldl
              (fun state index => $bodyNative index state) $initialState = $resultModel :=
            List.foldl_hom $embedding (g₁ := $mutableStep)
              (g₂ := fun state index => $bodyNative index state)
              (l := $indices) (init := $initialMutable) (by intros; rfl)
          rw [← $equal:ident]
          exact ($outcome:ident).1.1)
      return (normalize, #[proof])

private def rangeNormalProof (site : ActualRangeSite)
    (normal control outcome : TSyntax `ident) :
    TermElabM (Array (TSyntax `tactic)) := do
  if site.pendingSlot?.isSome then return #[← `(tactic| skip)]
  return #[
    ← `(tactic| have $normal:ident : $control:ident = .normal := by
      cases $control:ident with
      | normal => rfl
      | returned _ => exact False.elim ($outcome:ident).2
      | fault _ => exact False.elim ($outcome:ident).2),
    ← `(tactic| subst $control:ident)]

private def rangeBodyFinish (range : RangeRegistration) (site : ActualRangeSite)
    (returnsFromFunction hasCompletion : Bool)
    (fields : Array (TSyntax `term)) (positions : Array Nat)
    (index cursorEqual strideEqual fixed : TSyntax `ident) (strideModel : ValueModel)
    (completionCore completionRep frameShape frameContents : TSyntax `term)
    (preserveArrays : Bool) (fixedSimp : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (pending : RangePendingProof) : TraceFinish := fun context => do
  let returnedModel ← range.returned.requireModel
  let rawOutcome := resolveRaw returnedModel.rawModel context.known
  let outcomeType ← actualTypeTerm range.returned.type.coreTy
  let rawOutcome ← `(($rawOutcome : $outcomeType))
  let observed ← observationAt range.returned context.heap context.relations
  let nativeType ← termOfExpr range.returned.type.nativeType
  let coreType ← termOfExpr (coreTypeExpr range.returned.type.coreTy)
  let representation ← termOfExpr range.returned.type.representation
  let observedName := mkIdent (← mkFreshUserName `rangeOutcomeObserved)
  let observationProof ← `(tactic|
    have $observedName:ident : ($representation :
        Complexity.Language.Representation $nativeType $coreType).Rel
        $(returnedModel.model) $rawOutcome $(context.heap) := $observed)
  let observed : TSyntax `term := ⟨observedName.raw⟩
  let rawState ← if hasCompletion then `(($rawOutcome).2) else pure rawOutcome
  let stateObserved ← if hasCompletion then `(($observed).2) else pure observed
  let rawCompletion ← if hasCompletion then `(($rawOutcome).1)
    else `((none : Option (Complexity.Language.Value $completionCore)))
  let completionObserved ← if hasCompletion then `(($observed).1)
    else `(Complexity.Language.Representation.option_none $completionRep $(context.heap))
  let cursorNext ← if hasCompletion then
      `(if ($rawCompletion).isSome then $index:ident else $index:ident + $(strideModel.model))
    else `($index:ident + $(strideModel.model))
  let mut afterFields := fields
  for binding in range.captured, position in positions, field in [:range.captured.size] do
    if binding.mutable then
      afterFields := afterFields.set! position (← fieldProjection range.captured.size field rawState)
  afterFields := afterFields.set! site.cursorSlot cursorNext
  if hasCompletion then
    if let some position := site.pendingSlot? then
      afterFields := afterFields.set! position rawCompletion
  let after ← sourceTuple afterFields
  let nextFrame ← if preserveArrays then
      `(And.intro
        (Complexity.Language.Heap.ShapeExtends.trans $frameShape $(context.shape))
        (fun {kind} buffer values observed =>
          $(context.contents) (kind := kind) buffer values
            ($frameContents (kind := kind) buffer values observed)))
    else `(Complexity.Language.Heap.ShapeExtends.trans $frameShape $(context.shape))
  let scalarFacts ← context.scalarEqualities.mapM fun equality =>
    `(Lean.Parser.Tactic.simpLemma| $equality:term)
  let executionRules := #[
    ← `(Lean.Parser.Tactic.simpLemma| $cursorEqual:ident),
    ← `(Lean.Parser.Tactic.simpLemma| $strideEqual:ident),
    ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_none),
    ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_some),
    ← `(Lean.Parser.Tactic.simpLemma| Bool.false_eq_true),
    ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)] ++
    fixedSimp ++ pending.entryRules ++ pending.currentRules ++ scalarFacts ++ context.branchRules
  -- A nested named loop returns an actual locals tuple, not necessarily a
  -- constructor expression. Compare its lexical coordinates using the fixed
  -- fields already proved by that loop; do not rebuild them from the model.
  let coordinateEqual ← `(by
    simp (config := { zetaDelta := true }) only [$executionRules,*] <;> rfl)
  let mut localsEqual ← `(Subsingleton.elim _ _)
  for _ in site.scope do localsEqual ← `(Prod.ext $coordinateEqual $localsEqual)
  let executed ← `(by first
    | rfl
    | simp only [$executionRules,*] <;>
        exact congrArg Part.some (Prod.ext (Prod.ext rfl $localsEqual) rfl))
  let returnedObserved ← `(by
    have retained := $stateObserved
    -- Select mathematical branches before relating scalar coordinates;
    -- otherwise rewriting a discriminant can hide its branch equation.
    simp (config := { implicitDefEqProofs := false }) only
      [Id.run, Id.instMonad, Pure.pure, Bind.bind, $(context.branchRules),*]
      at retained ⊢ <;>
      simpa (config := { implicitDefEqProofs := false }) only [$scalarFacts,*]
        using retained)
  let completionRules := pending.currentRules ++ context.branchRules
  let completedObserved ← `(by
    simpa (config := { implicitDefEqProofs := false }) only
      [Id.run, Id.instMonad, Pure.pure, Bind.bind, $completionRules,*] using $completionObserved)
  let cursorObserved ← if hasCompletion then `(by
      have aligned := congrArg
        (fun (completed : Bool) => if completed then $index:ident else $index:ident + $(strideModel.model))
        (Complexity.Language.Representation.option_isSome_eq $completionRep $completionObserved).symm
      simpa only [Id.run, Id.instMonad, Pure.pure, Bind.bind, $(context.branchRules),*] using aligned)
    else `(rfl)
  if returnsFromFunction then
    let control ← `(($rawCompletion).elim
      Complexity.Language.Control.normal Complexity.Language.Control.returned)
    let relatedControl ← `(by
      apply (Complexity.Language.Control.represents_iff_exists
        $control $completionRep _ $(context.heap)).mpr
      exact ⟨$rawCompletion, rfl, $completedObserved⟩)
    return #[observationProof, ← `(tactic|
      exact ⟨$control, $after, $(context.heap), $executed,
        ⟨$returnedObserved, $cursorObserved, $fixed:ident, $nextFrame⟩, $relatedControl⟩)]
  return #[observationProof, ← `(tactic|
    exact ⟨$after, $(context.heap), $executed,
      ⟨$returnedObserved, $cursorObserved, $fixed:ident, $nextFrame⟩, $completedObserved⟩)]

private def rangeCaptureNeedsContents : NativeType → Bool
  | .array _ => true
  | .prod left right => rangeCaptureNeedsContents left || rangeCaptureNeedsContents right
  | .option payload => rangeCaptureNeedsContents payload
  | .record _ layout _ => rangeCaptureNeedsContents layout
  | .pure _ | .raw _ | .list _ => false

/-- Recover immutable mathematical captures from observations of the same
actual slots in the current heap. These facts are available to the function's
original recursive descent proof; they do not assume an inverse representation. -/
private def rangeImmutableFacts (range : RangeRegistration) (initialValue : Value)
    (positions : Array Nat) (fixed : Array (Nat × TSyntax `term))
    (arguments fields : Array (TSyntax `term))
    (selected heap current frameShape : TSyntax `term)
    (frameContents : Option (TSyntax `term)) (entryObserved : TSyntax `term) :
    TermElabM (Array (TSyntax `tactic)) := do
  let currentModel ← range.state.requireModel
  let initialModel ← initialValue.requireModel
  let entrySelected ← fieldsTerm (← positions.toList.mapM fun position =>
    match arguments[position]? with
    | some argument => pure argument
    | none => throwError "an immutable range capture has no actual entry coordinate")
  let relationName := range.state.relationName
  let currentBinding := { range.state with model? := some {
    currentModel with rawModel := selected, observation := .named relationName.getId } }
  let entryBinding := { range.state with model? := some {
    model := initialModel.model, rawModel := entrySelected
    observation := .named relationName.getId } }
  let entryName := mkIdent (← mkFreshUserName `rangeEntryObserved)
  let stateType ← termOfExpr range.state.type.nativeType
  let stateCore ← termOfExpr (coreTypeExpr range.state.type.coreTy)
  let stateRepresentation ← termOfExpr range.state.type.representation
  let currentRelations : Array RetainedObservation :=
    #[⟨relationName.getId, range.state.type, ⟨relationName.raw⟩⟩]
  let entryRelations : Array RetainedObservation :=
    #[⟨relationName.getId, range.state.type, ⟨entryName.raw⟩⟩]
  let mut facts := #[]
  for binding in range.captured, index in [:range.captured.size] do
    if binding.mutable then continue
    -- Products, options and records reuse preservation of their fields.
    -- A contents-observing array still requires the actual contents frame.
    if rangeCaptureNeedsContents binding.type && frameContents.isNone then continue
    let some position := positions[index]?
      | throwError "an immutable range capture has no lexical slot"
    let some (_, fixedFact) := fixed.find? (fun entry => entry.1 == position)
      | throwError "an immutable range capture has no fixed source coordinate"
    let some actual := fields[position]?
      | throwError "an immutable range capture is outside its current source locals"
    let some entry := arguments[position]?
      | throwError "an immutable range capture has no actual entry coordinate"
    let projection ← fieldProjection range.captured.size index ⟨range.state.name.raw⟩
    let currentField ← value [currentBinding] projection (some binding.type)
    let entryField ← value [entryBinding] projection (some binding.type)
    let currentValue := (← currentField.requireModel).model
    let entryValue := (← entryField.requireModel).model
    let observedCurrent ← observationAt currentField current currentRelations
    let observedEntry ← observationAt entryField heap entryRelations
    let preserved ← preservation binding.type heap current frameShape frameContents
    let nativeType ← termOfExpr binding.type.nativeType
    let coreType ← termOfExpr (coreTypeExpr binding.type.coreTy)
    let representation ← termOfExpr binding.type.representation
    let representation ← `(($representation : Complexity.Language.Representation
      $nativeType $coreType))
    let equality := mkIdent (← mkFreshUserName `rangeImmutableEqual)
    facts := facts.push (← `(tactic|
      have $equality:ident : $currentValue = $entryValue := by
        apply ($representation).functional (value := $entry) (heap := $current)
        · have observed : ($representation).Rel $currentValue $actual $current := $observedCurrent
          simpa only [$fixedFact:term] using observed
        · exact $preserved (show ($representation).Rel $entryValue $entry $heap from $observedEntry)))
  if facts.isEmpty then return #[]
  return #[← `(tactic|
    have $entryName:ident :
        ($stateRepresentation : Complexity.Language.Representation $stateType $stateCore).Rel
          $(initialModel.model) $entrySelected $heap := $entryObserved)] ++ facts

/-- Prove the original named range in its full source coordinates. Iteration is
only a mathematical view; body calls retain their actual control and heap. -/
def rangeRelationProof (range : RangeRegistration) (initialValue : Value)
    (heap : TSyntax `term) (relations : Array RetainedObservation)
    (known : Array (Name × TSyntax `term)) (preserveArrays : Bool)
    (proveBody : RangeBodyProof) (publishRounds : Bool := false) :
    TermElabM (Array (TSyntax `tactic) × TSyntax `term × Nat) := do
  let site ← range.site
  let returnsFromFunction ← range.returnsFromFunction
  let positions ← range.slots
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let localsType := member `Locals
  let view := member `View
  let code := member `Code
  let guard := member `Guard
  let body := member `Body
  let guardObserve := member `guard_observe
  let bodyObserve := member `body_observe
  let observe := member `observe
  let guardEquation := member `guard_eq
  let bodyEquation := member `body_eq
  let program := mkIdent (site.name.getPrefix ++ `program)
  let mut arguments : Array (TSyntax `ident) := #[]
  for _ in site.scope do arguments := arguments.push (mkIdent (← mkFreshUserName `rangeArgument))
  let argumentTerms := arguments.map fun argument => (⟨argument.raw⟩ : TSyntax `term)
  let entry ← sourceTuple argumentTerms
  let action := Lean.Syntax.mkApp ⟨(mkIdent site.name).raw⟩ argumentTerms
  let extraction := mkCIdent ``bindActualRangeArguments
  let actionName : TSyntax `term := quote site.name
  let argumentNames : TSyntax `term := quote (arguments.map (·.getId))
  let extractCall := Lean.Syntax.mkApp ⟨extraction.raw⟩ #[actionName, argumentNames]
  let extractElement ← `(doElem| $extractCall:term)
  let extractBody : TSyntax ``doSeq :=
    ⟨Lean.Elab.Term.Do.mkDoSeq #[extractElement.raw]⟩
  let extract ← `(tactic| run_tac $extractBody:doSeq)
  let (summary, stateRel, locals, current, related, cursorEqual, fixed, framed,
      active, running, guardRel, bodyRel, positive, stopEqual, strideEqual, startEqual) ← do
    let summary := mkIdent (← mkFreshUserName `rangeRelated)
    let stateRel := mkIdent (← mkFreshUserName `rangeStateRel)
    let locals := mkIdent (← mkFreshUserName `rangeLocals)
    let current := mkIdent (← mkFreshUserName `rangeHeap)
    let related := mkIdent (← mkFreshUserName `rangeStateRelated)
    let cursorEqual := mkIdent (← mkFreshUserName `rangeCursorEqual)
    let fixed := mkIdent (← mkFreshUserName `rangeFixed)
    let framed := mkIdent (← mkFreshUserName `rangeFramed)
    let active := mkIdent (← mkFreshUserName `rangeActive)
    let running := mkIdent (← mkFreshUserName `rangeRunning)
    let guardRel := mkIdent (← mkFreshUserName `rangeGuardRelated)
    let bodyRel := mkIdent (← mkFreshUserName `rangeBodyRelated)
    let positive := mkIdent (← mkFreshUserName `rangeStridePositive)
    let stopEqual := mkIdent (← mkFreshUserName `rangeStopEqual)
    let strideEqual := mkIdent (← mkFreshUserName `rangeStrideEqual)
    let startEqual := mkIdent (← mkFreshUserName `rangeStartEqual)
    pure (summary, stateRel, locals, current, related, cursorEqual, fixed, framed,
      active, running, guardRel, bodyRel, positive, stopEqual, strideEqual, startEqual)
  let index := range.index.nativeName
  let state := range.state.name
  let stateObserved := range.state.relationName
  let (stateType, stateCore, representation, observedType, observedCore,
      observedRepresentation, completionCore, completionType?, completionRep, pendingValue) ← do
    let stateType ← termOfExpr range.state.type.nativeType
    let stateCore ← termOfExpr (coreTypeExpr range.state.type.coreTy)
    let representation ← termOfExpr range.state.type.representation
    let observedType ← termOfExpr range.result.type.nativeType
    let observedCore ← termOfExpr (coreTypeExpr range.result.type.coreTy)
    let observedRepresentation ← termOfExpr range.result.type.representation
    let resultCore ← termOfExpr (coreTypeExpr site.result)
    let completionCore ← match site.pendingSlot? with
      | none => pure resultCore
      | some position => do
          let some binding := site.scope[position]?
            | throwError "the pending range result is outside its source locals"
          let .option payload := binding.type
            | throwError "a local completion coordinate must have an optional result type"
          termOfExpr (coreTypeExpr payload)
    let completionType? := match range.model with
      | .fold .. => none
      | .completion type .. => some type
    let completionRep ← match completionType? with
      | some type => do
          let native ← termOfExpr type.nativeType
          let representation ← termOfExpr type.representation
          `(($representation : Complexity.Language.Representation $native $completionCore))
      | none => `(Complexity.Language.Representation.ofEmbedding
          (Function.Embedding.refl (Complexity.Language.Value $completionCore)))
    let pendingValue ← match site.pendingSlot? with
      | some position => do
          let atom ← `(Complexity.Language.Atom.var $(← liftMacroM (Core.variableTerm position)))
          `(fun (locals : $localsType:ident) => ($atom).eval (($view:ident).symm locals))
      | none => `(fun (_ : $localsType:ident) => (none : Option (Complexity.Language.Value $completionCore)))
    pure (stateType, stateCore, representation, observedType, observedCore,
      observedRepresentation, completionCore, completionType?, completionRep, pendingValue)
  let initialModel ← initialValue.requireModel
  let resultModel ← range.result.requireModel
  let startModel ← range.start.requireModel
  let stopModel ← range.stop.requireModel
  let strideModel ← range.stride.requireModel
  let entryObserved ← observationAt initialValue heap relations
  let startObserved ← observationAt range.start heap relations
  let stopObserved ← observationAt range.stop heap relations
  let strideObserved ← observationAt range.stride heap relations
  let nativeSubstitution ← range.captured.mapM fun binding => do
    return (binding.nativeName.getId, (← binding.requireModel).model)
  let bodyNative := resolveRaw range.bodyNative nativeSubstitution
  let nativeStep ← if completionType?.isSome then pure bodyNative
    else `(fun (index : Nat) (state : $stateType) =>
      ((none : Option (Complexity.Language.Value $completionCore)), $bodyNative index state))
  let nextIndex ← `(if ($nativeStep $index:ident $state:ident).1.isSome
    then $index:ident else $index:ident + $(strideModel.model))
  let nextState ← `(($nativeStep $index:ident $state:ident).2)
  let nextCompletion ← `(($nativeStep $index:ident $state:ident).1)
  let fields ← sourceFields site.scope.size ⟨locals.raw⟩
  let selected ← range.selectState ⟨locals.raw⟩
  let some cursor := fields[site.cursorSlot]?
    | throwError "the actual range cursor is outside its full source locals"
  let some entryCursor := argumentTerms[site.cursorSlot]?
    | throwError "the actual range cursor has no entry argument"
  let scopeArguments := site.scope.zip argumentTerms |>.map fun (binding, argument) =>
    (binding.proofName.getId, argument)
  let frozenStop := resolveRaw site.stop scopeArguments
  let frozenStride := resolveRaw site.stride scopeArguments
  let mut fixedType ← `(True)
  let mut fixedFacts : Array (TSyntax `term) := #[]
  let mutableSlots := (range.captured.zip positions).filterMap fun (binding, position) =>
    if binding.mutable then some position else none
  let fixedSlots := site.scope.zipIdx |>.filter (fun (_, position) =>
    position != site.cursorSlot && !mutableSlots.contains position &&
      !(completionType?.isSome && site.pendingSlot? == some position))
  for (_, position) in fixedSlots.reverse do
    fixedType ← `($(fields[position]!) = $(argumentTerms[position]!) ∧ $fixedType)
  let mut fixedTail : TSyntax `term := ⟨fixed.raw⟩
  for _ in fixedSlots do
    fixedFacts := fixedFacts.push (← `(($fixedTail).1))
    fixedTail ← `(($fixedTail).2)
  -- Running entry is separate from the completed post-state relation. In
  -- particular, a stored local result is not a fixed empty source coordinate.
  let pending ← rangePendingProof site argumentTerms fields running
  let heapPost ← if preserveArrays then
      `(fun finish => Complexity.Language.Heap.ShapeExtends $heap finish ∧
        Complexity.Language.Buffer.PreservesContents $heap finish)
    else `(fun finish => Complexity.Language.Heap.ShapeExtends $heap finish)
  let initialFrame ← if preserveArrays then
      `(And.intro (Complexity.Language.Heap.ShapeExtends.refl $heap)
        (by intro kind buffer values observed; exact observed))
    else `(Complexity.Language.Heap.ShapeExtends.refl $heap)
  let frameShape ← if preserveArrays then `(($framed:ident).1) else `($framed:ident)
  let frameContents ← if preserveArrays then `(($framed:ident).2) else `(True.intro)
  let fixedSimp ← fixedFacts.mapM fun fact => `(Lean.Parser.Tactic.simpLemma| $fact:term)
  let bodyFinish := rangeBodyFinish range site returnsFromFunction completionType?.isSome
    fields positions index cursorEqual strideEqual fixed strideModel
    completionCore completionRep frameShape frameContents preserveArrays fixedSimp pending
  let fixedCoordinates := fixedSlots.zip fixedFacts |>.map fun ((_, position), fact) =>
    (position, fact)
  let mut bodyPrefix ← rangeImmutableFacts range initialValue positions fixedCoordinates
    argumentTerms fields selected heap ⟨current.raw⟩ frameShape
    (if preserveArrays then some frameContents else none) entryObserved
  let mut bodyRelations : Array RetainedObservation := #[]
  if range.state.type.isIdentity then
    bodyPrefix := bodyPrefix ++ #[
      ← `(tactic| change $state:ident = $selected at $stateObserved:ident),
      ← `(tactic| subst $state:ident),
      ← `(tactic| let $state:ident : $stateType := $selected)]
  else
    bodyRelations := bodyRelations.push
      ⟨stateObserved.getId, range.state.type, ⟨stateObserved.raw⟩⟩
  let bodyKnown := known.push (range.state.rawName.getId, selected)
  let bodyProof : Array (TSyntax `tactic) := bodyPrefix ++ #[
      ← `(tactic| rw [$bodyObserve:ident, $bodyEquation:ident]),
      ← `(tactic| simp (config := { failIfUnchanged := false }) only
        [$cursorEqual:ident, $(pending.currentRules),*])] ++
    (← proveBody range.body range.returned ⟨current.raw⟩ bodyRelations
      bodyKnown preserveArrays bodyFinish)
  let after := mkIdent (← mkFreshUserName `rangeAfter)
  let finish := mkIdent (← mkFreshUserName `rangeFinish)
  let control := mkIdent (← mkFreshUserName `rangeControl)
  let executed := mkIdent (← mkFreshUserName `rangeExecuted)
  let outcome := mkIdent (← mkFreshUserName `rangeOutcome)
  let normal := mkIdent (← mkFreshUserName `rangeNormal)
  let finalObserved := mkIdent (← mkFreshUserName `rangeFinalObserved)
  let finalFixed := mkIdent (← mkFreshUserName `rangeFinalFixed)
  let actualResult := mkIdent (← mkFreshUserName `rangeReturned)
  let actualResult? := if returnsFromFunction then some (⟨actualResult.raw⟩ : TSyntax `term)
    else none
  let selectedAfter ← range.select ⟨after.raw⟩ actualResult?
  let (normalizeResult, resultProof) ← rangeResultProof range nativeSubstitution
    bodyNative completionCore startModel.model stopModel.model strideModel.model
    initialModel.model resultModel.model selectedAfter ⟨finish.raw⟩ positive outcome finalObserved
  let afterFields ← sourceFields site.scope.size ⟨after.raw⟩
  let mut fixedAfter ← `(True)
  for (_, position) in fixedSlots.reverse do
    let expected ← if site.pendingSlot? == some position then `(none)
      else pure argumentTerms[position]!
    fixedAfter ← `($(afterFields[position]!) = $expected ∧ $fixedAfter)
  let guardNormalize ← normalizeAction
  let mut localsEta ← `(Subsingleton.elim _ _)
  for _ in site.scope do localsEta ← `(Prod.ext rfl $localsEta)
  localsEta ← `(show $(← sourceTuple fields) = $locals:ident from $localsEta)
  let guardStatement ← `(∀ ($index:ident : Nat) ($state:ident : $stateType)
        ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
        $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
        $pendingValue $locals:ident = none →
        ∃ after finish,
          Complexity.Language.Stmt.observe $view:ident $guard:ident $program:ident
            $locals:ident $current:ident =
            Part.some ((.returned (decide ($index:ident < $(stopModel.model))), after), finish) ∧
          $stateRel:ident $index:ident $state:ident after finish ∧ $pendingValue after = none)
  let guardSteps := #[← `(tactic| exact (by
      intro $index:ident $state:ident $locals:ident $current:ident $related:ident $running:ident
      obtain ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩ := $related:ident
      $(pending.current):tactic*
      refine ⟨$locals:ident, $current:ident, ?_,
        ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩, $running:ident⟩
      rw [$guardObserve:ident, $guardEquation:ident]
      simp (config := { failIfUnchanged := false }) only [$(pending.currentRules),*]
      $guardNormalize:tactic
      apply congrArg Part.some
      apply Prod.ext
      · apply Prod.ext
        · apply congrArg Complexity.Language.Control.returned
          simp only [$cursorEqual:ident, $stopEqual:ident, $fixedSimp,*]
        · simpa only [$(pending.currentRules),*] using $localsEta
      · rfl))]
  let guardSuffix := mkIdent (if preserveArrays then `guard_rel_preserving else `guard_rel)
  let bodySuffix := mkIdent (if preserveArrays then `body_rel_preserving else `body_rel)
  let guardProof ← rangeRoundProof guardRel guardStatement guardSteps guard guardSuffix publishRounds
  let initial ← `(⟨$entryObserved, $startEqual:ident, by repeat' constructor, $initialFrame⟩)
  let rangeProof ← rangeLoopProof site returnsFromFunction completionRep nativeStep startModel.model stopModel.model
    strideModel.model initialModel.model entry heap initial
    stateRel guardRel bodyRel positive control after finish executed outcome
  let normalProof ← if returnsFromFunction then do
      let equal := mkIdent (← mkFreshUserName `rangeControlEqual)
      let related := mkIdent (← mkFreshUserName `rangeReturnRelated)
      pure #[← `(tactic|
        obtain ⟨$actualResult:ident, $equal:ident, $related:ident⟩ :=
          (Complexity.Language.Control.represents_iff_exists $control:ident $completionRep
            _ $finish:ident).mp ($outcome:ident).2),
        ← `(tactic| rw [$equal:ident] at $executed:ident),
        ← `(tactic| have $outcome:ident := And.intro ($outcome:ident).1 $related:ident)]
    else rangeNormalProof site normal control outcome
  let finalControl ← if returnsFromFunction then
      `(($actualResult:ident).elim Complexity.Language.Control.normal Complexity.Language.Control.returned)
    else `(Complexity.Language.Control.normal)
  let statement ← `(∃ ($after:ident : $localsType:ident)
        ($finish:ident : Complexity.Language.Heap),
        $action $heap = Part.some (($finalControl, $after:ident), $finish:ident) ∧
        ($observedRepresentation : Complexity.Language.Representation $observedType $observedCore).Rel
          $(resultModel.model) $selectedAfter $finish:ident ∧
        $heapPost $finish:ident ∧ $fixedAfter)
  let statement ← if returnsFromFunction then
      `(∃ ($actualResult:ident : Option (Complexity.Language.Value $completionCore)), $statement)
    else pure statement
  let bodyConclusion ← if returnsFromFunction then
      `(∃ control after finish,
        Complexity.Language.Stmt.observe $view:ident $body:ident $program:ident
          $locals:ident $current:ident = Part.some ((control, after), finish) ∧
        $stateRel:ident $nextIndex $nextState after finish ∧
        Complexity.Language.Control.Represents control $completionRep $nextCompletion finish)
    else `(∃ after finish,
        Complexity.Language.Stmt.observe $view:ident $body:ident $program:ident
          $locals:ident $current:ident = Part.some ((.normal, after), finish) ∧
        $stateRel:ident $nextIndex $nextState after finish ∧
        ($completionRep).option.Rel $nextCompletion ($pendingValue after) finish)
  let bodyStatement ← `(∀ ($index:ident : Nat) ($state:ident : $stateType)
          ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
          $index:ident < $(stopModel.model) →
          $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
          $pendingValue $locals:ident = none →
          $bodyConclusion)
  let bodySteps := #[
    ← `(tactic| intro $index:ident $state:ident $locals:ident $current:ident
      $active:ident $related:ident $running:ident),
    ← `(tactic| obtain ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩ :=
      $related:ident)] ++ pending.current ++ bodyProof
  let bodyRelationProof ← rangeRoundProof bodyRel bodyStatement bodySteps body bodySuffix publishRounds
  let relationBody ← `(fun ($index:ident : Nat) ($state:ident : $stateType)
      ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap) =>
    ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
      $state:ident $selected $current:ident ∧
    $cursor = $index:ident ∧ $fixedType ∧ $heapPost $current:ident)
  let relationBody ← if publishRounds then do
      let suffix := mkIdent (if preserveArrays then `stateRel_preserving else `stateRel)
      `(represented_range_relation $guard:ident $suffix:ident => $relationBody)
    else pure relationBody
  let registration ← if publishRounds then do
      pure #[← rangeRoundRegistration code
        (member (if preserveArrays then `stateRel_preserving else `stateRel))
        (member guardSuffix.getId) (member bodySuffix.getId) site.pendingSlot?.isSome]
    else pure #[]
  let prepareRelations := pending.entry ++ #[
    ← `(tactic| let $startEqual:ident : $entryCursor = $(startModel.model) := Eq.symm $startObserved),
    ← `(tactic| let $stopEqual:ident : $frozenStop = $(stopModel.model) := Eq.symm $stopObserved),
    ← `(tactic| let $strideEqual:ident : $frozenStride = $(strideModel.model) := Eq.symm $strideObserved),
    ← `(tactic| have $positive:ident : 0 < $(strideModel.model) := by
      simp (config := { zetaDelta := true, failIfUnchanged := false }) only [Nat.add_eq] <;> omega),
    ← `(tactic| let $stateRel:ident := $relationBody),
    guardProof, bodyRelationProof] ++ registration
  let exposeExecution := #[
    ← `(tactic| change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $entry $heap = _ at $executed:ident),
    ← `(tactic| rw [$observe:ident] at $executed:ident)]
  let witnesses ← `(⟨$after:ident, $finish:ident, $executed:ident, $finalObserved:ident,
    ($outcome:ident).1.2.2.2, $finalFixed:ident⟩)
  let witnesses ← if returnsFromFunction then `(⟨$actualResult:ident, $witnesses⟩)
    else pure witnesses
  let conclude := #[
    ← `(tactic| have $finalFixed:ident : $fixedAfter := by
      simpa only [$(pending.entryRules),*] using ($outcome:ident).1.2.2.1),
    ← `(tactic| exact $witnesses)]
  let proof ← rangeSummaryProof summary statement
    (prepareRelations ++ rangeProof ++ normalizeResult ++ normalProof ++
      exposeExecution ++ resultProof ++ conclude)
  return (#[extract, proof], ⟨summary.raw⟩, fixedSlots.size)

end Internal

end Complexity.Language.Syntax.Represented
