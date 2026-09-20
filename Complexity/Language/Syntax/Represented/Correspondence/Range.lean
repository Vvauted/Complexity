/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic
import Complexity.Language.Eval.Locals.Range.LocalReturn

/-!
# Correspondence for represented finite ranges

Relate a prepared mathematical fold or locally completing `forIn` to its actual
named source range. Lexical slot alignment and the existing range rules retain
complete source coordinates, actual body control and intermediate heap observations.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

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

/-- A completion view reads the actual saved result beside the actual final
state; the mathematical result never reconstructs a source handle. -/
def RangeRegistration.select (range : RangeRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let state ← range.selectState locals
  match range.model with
  | .fold .. => pure state
  | .completion .. =>
      let site ← range.site
      let some position := site.pendingSlot?
        | throwError "a local range result requires its actual completion coordinate"
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

private def rangePendingProof (site : ActualRangeSite)
    (arguments fields : Array (TSyntax `term)) (running : TSyntax `ident) :
    TermElabM RangePendingProof := do
  let some pendingSlot := site.pendingSlot? | return ⟨#[], #[], #[], #[]⟩
  let some entryPending := arguments[pendingSlot]?
    | throwError "the pending range result has no actual entry coordinate"
  let some currentPending := fields[pendingSlot]?
    | throwError "the pending range result is outside its source locals"
  let pendingEntry := mkIdent (← mkFreshUserName `rangePendingEntry)
  let pendingCurrent := mkIdent (← mkFreshUserName `rangePendingCurrent)
  return {
    entry := #[← `(tactic| have $pendingEntry:ident : $entryPending = none := by rfl)]
    current := #[← `(tactic|
      have $pendingCurrent:ident : $currentPending = none := $running:ident)]
    entryRules := #[← `(Lean.Parser.Tactic.simpLemma| $pendingEntry:ident)]
    currentRules := #[← `(Lean.Parser.Tactic.simpLemma| $pendingCurrent:ident)] }

/-- Choose the existing loop theorem by actual source completion behavior.
Both paths consume the same generated guard and normally executing body. -/
private def rangeLoopProof (site : ActualRangeSite)
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
  let bodyAdapter ← `(by
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

/-- Prove the original named range in its full source coordinates. Iteration is
only a mathematical view; body calls retain their actual control and heap. -/
def rangeRelationProof (range : RangeRegistration) (initialValue : Value)
    (heap : TSyntax `term) (relations : Array RetainedObservation)
    (known : Array (Name × TSyntax `term)) (preserveArrays : Bool)
    (proveBody : RangeBodyProof) :
    TermElabM (Array (TSyntax `tactic) × TSyntax `term × Nat) := do
  let site ← range.site
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
      | some type => termOfExpr type.representation
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
  let bodyFinish : TraceFinish := fun context => do
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
    let rawState ← if completionType?.isSome then `(($rawOutcome).2) else pure rawOutcome
    let stateObserved ← if completionType?.isSome then `(($observed).2) else pure observed
    let rawCompletion ← if completionType?.isSome then `(($rawOutcome).1)
      else `((none : Option (Complexity.Language.Value $completionCore)))
    let completionObserved ← if completionType?.isSome then `(($observed).1)
      else `(Complexity.Language.Representation.option_none $completionRep $(context.heap))
    let cursorNext ← if completionType?.isSome then
        `(if ($rawCompletion).isSome then $index:ident else $index:ident + $(strideModel.model))
      else `($index:ident + $(strideModel.model))
    let mut afterFields := fields
    for binding in range.captured, position in positions, field in [:range.captured.size] do
      if binding.mutable then
        afterFields := afterFields.set! position (← fieldProjection range.captured.size field rawState)
    afterFields := afterFields.set! site.cursorSlot cursorNext
    if completionType?.isSome then
      let some position := site.pendingSlot?
        | throwError "a completion range requires its actual local result slot"
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
    let executed ← `(by first
      | rfl
      | simp only [$executionRules,*])
    let returnedObserved ← `(by
      simpa (config := { implicitDefEqProofs := false }) only
        [Id.run, Id.instMonad, Pure.pure, Bind.bind, $(context.branchRules),*]
        using $stateObserved)
    let completedObserved ← `(by
      simpa (config := { implicitDefEqProofs := false }) only [Id.run, Id.instMonad, Pure.pure, Bind.bind,
        $(pending.currentRules),*, $(context.branchRules),*] using $completionObserved)
    let cursorObserved ← if completionType?.isSome then `(by
        have aligned := congrArg
          (fun (completed : Bool) => if completed then $index:ident else $index:ident + $(strideModel.model))
          (Complexity.Language.Representation.option_isSome_eq $completionRep $completionObserved).symm
        simpa only [Id.run, Id.instMonad, Pure.pure, Bind.bind, $(context.branchRules),*] using aligned)
      else `(rfl)
    return #[observationProof, ← `(tactic|
      exact ⟨$after, $(context.heap), $executed,
        ⟨$returnedObserved, $cursorObserved, $fixed:ident, $nextFrame⟩, $completedObserved⟩)]
  let mut bodyPrefix := #[]
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
  let selectedAfter ← range.select ⟨after.raw⟩
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
  let guardProof ← `(tactic|
    have $guardRel:ident : ∀ ($index:ident : Nat) ($state:ident : $stateType)
        ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
        $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
        $pendingValue $locals:ident = none →
        ∃ after finish,
          Complexity.Language.Stmt.observe $view:ident $guard:ident $program:ident
            $locals:ident $current:ident =
            Part.some ((.returned (decide ($index:ident < $(stopModel.model))), after), finish) ∧
          $stateRel:ident $index:ident $state:ident after finish ∧ $pendingValue after = none := by
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
      · rfl)
  let initial ← `(⟨$entryObserved, $startEqual:ident, by repeat' constructor, $initialFrame⟩)
  let rangeProof ← rangeLoopProof site completionRep nativeStep startModel.model stopModel.model
    strideModel.model initialModel.model entry heap initial
    stateRel guardRel bodyRel positive control after finish executed outcome
  let normalProof ← rangeNormalProof site normal control outcome
  let statement ← `(∃ ($after:ident : $localsType:ident)
        ($finish:ident : Complexity.Language.Heap),
        $action $heap = Part.some ((Complexity.Language.Control.normal, $after:ident), $finish:ident) ∧
        ($observedRepresentation : Complexity.Language.Representation $observedType $observedCore).Rel
          $(resultModel.model) $selectedAfter $finish:ident ∧
        $heapPost $finish:ident ∧ $fixedAfter)
  let bodyStatement ← `(∀ ($index:ident : Nat) ($state:ident : $stateType)
          ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
          $index:ident < $(stopModel.model) →
          $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
          $pendingValue $locals:ident = none →
          ∃ after finish,
            Complexity.Language.Stmt.observe $view:ident $body:ident $program:ident
              $locals:ident $current:ident = Part.some ((.normal, after), finish) ∧
            $stateRel:ident $nextIndex $nextState after finish ∧
            ($completionRep).option.Rel $nextCompletion ($pendingValue after) finish)
  let bodySteps := #[
    ← `(tactic| intro $index:ident $state:ident $locals:ident $current:ident
      $active:ident $related:ident $running:ident),
    ← `(tactic| obtain ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩ :=
      $related:ident)] ++ pending.current ++ bodyProof
  let bodyRelationProof ← rangeSummaryProof bodyRel bodyStatement bodySteps
  let prepareRelations := pending.entry ++ #[
    ← `(tactic| have $startEqual:ident : $entryCursor = $(startModel.model) := Eq.symm $startObserved),
    ← `(tactic| have $stopEqual:ident : $frozenStop = $(stopModel.model) := Eq.symm $stopObserved),
    ← `(tactic| have $strideEqual:ident : $frozenStride = $(strideModel.model) := Eq.symm $strideObserved),
    ← `(tactic| have $positive:ident : 0 < $(strideModel.model) := by
      simp (config := { zetaDelta := true, failIfUnchanged := false }) only [Nat.add_eq] <;> omega),
    ← `(tactic| let $stateRel:ident ($index:ident : Nat) ($state:ident : $stateType)
        ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap) : Prop :=
      ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
        $state:ident $selected $current:ident ∧
      $cursor = $index:ident ∧ $fixedType ∧ $heapPost $current:ident),
    guardProof, bodyRelationProof]
  let exposeExecution := #[
    ← `(tactic| change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $entry $heap = _ at $executed:ident),
    ← `(tactic| rw [$observe:ident] at $executed:ident)]
  let conclude := #[
    ← `(tactic| have $finalFixed:ident : $fixedAfter := by
      simpa only [$(pending.entryRules),*] using ($outcome:ident).1.2.2.1),
    ← `(tactic| exact ⟨$after:ident, $finish:ident, $executed:ident, $finalObserved:ident,
      ($outcome:ident).1.2.2.2, $finalFixed:ident⟩)]
  let proof ← rangeSummaryProof summary statement
    (prepareRelations ++ rangeProof ++ normalizeResult ++ normalProof ++
      exposeExecution ++ resultProof ++ conclude)
  return (#[extract, proof], ⟨summary.raw⟩, fixedSlots.size)

end Internal

end Complexity.Language.Syntax.Represented
