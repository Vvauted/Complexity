/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic
import Complexity.Language.Eval.Locals.Range.Represented

/-!
# Correspondence for represented finite ranges

Relate a prepared mathematical fold to its actual named source range. Lexical
slot alignment and the existing range rule retain complete source coordinates,
actual body control and intermediate heap observations.
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
  | some site => do
      if site.localReturn then
        throwError "a live-controlled source range cannot use a normal range-fold correspondence"
      pure site
  | none => throwError "the prepared range has no checked actual source site"

/-- Align source declarations by lexical occurrence, not by a name lookup.
Anonymous Core coordinates remain in the full source scope. -/
def RangeRegistration.slots (range : RangeRegistration) : TermElabM (Array Nat) := do
  let site ← range.site
  let mut used : NameSet := {}
  let mut positions := #[]
  for binding in range.captured do
    let some entry := site.entryScope.find? fun entry =>
        entry.name == some binding.name.getId && !used.contains entry.proofName.getId
      | throwError "the prepared range contains an unmatched lexical slot"
    unless entry.type == binding.type.coreTy do
      throwError "the source range's lexical entry does not match its prepared slots"
    let some position := site.scope.findIdx? fun actual =>
        actual.proofName.getId == entry.proofName.getId
      | throwError "the source range dropped an entry coordinate"
    positions := positions.push position
    used := used.insert entry.proofName.getId
  return positions

/-- Source locals use Core's product spine, including its final Unit. -/
private def sourceFields (count : Nat) (locals : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  let mut remaining := locals
  let mut fields := #[]
  for _ in [:count] do
    fields := fields.push (← `(($remaining).1))
    remaining ← `(($remaining).2)
  return fields

private def sourceTuple (fields : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let mut result ← `(())
  for field in fields.reverse do result ← `(($field, $result))
  return result

def RangeRegistration.select (range : RangeRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let site ← range.site
  let fields ← sourceFields site.scope.size locals
  let positions ← range.slots
  fieldsTerm (← positions.toList.mapM fun index =>
    match fields[index]? with
    | some field => pure field
    | none => throwError "the selected range coordinate is outside its actual locals")
/-- Prove the original named range in its full source coordinates. The fold is
only a mathematical view; body calls retain their actual control and heap. -/
def rangeRelationProof (range : RangeRegistration) (initialValue : Value)
    (heap : TSyntax `term) (relations : Array RetainedObservation)
    (known : Array (Name × TSyntax `term)) (preserveArrays : Bool)
    (proveBody : RangeBodyProof) : TermElabM (Array (TSyntax `tactic) × TSyntax `term) := do
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
  let summary := mkIdent (← mkFreshUserName `rangeRelated)
  let stateRel := mkIdent (← mkFreshUserName `rangeStateRel)
  let index := range.index.nativeName
  let state := range.state.name
  let locals := mkIdent (← mkFreshUserName `rangeLocals)
  let current := mkIdent (← mkFreshUserName `rangeHeap)
  let related := mkIdent (← mkFreshUserName `rangeStateRelated)
  let stateObserved := range.state.relationName
  let cursorEqual := mkIdent (← mkFreshUserName `rangeCursorEqual)
  let fixed := mkIdent (← mkFreshUserName `rangeFixed)
  let framed := mkIdent (← mkFreshUserName `rangeFramed)
  let active := mkIdent (← mkFreshUserName `rangeActive)
  let guardRel := mkIdent (← mkFreshUserName `rangeGuardRelated)
  let bodyRel := mkIdent (← mkFreshUserName `rangeBodyRelated)
  let positive := mkIdent (← mkFreshUserName `rangeStridePositive)
  let stopEqual := mkIdent (← mkFreshUserName `rangeStopEqual)
  let strideEqual := mkIdent (← mkFreshUserName `rangeStrideEqual)
  let startEqual := mkIdent (← mkFreshUserName `rangeStartEqual)
  let stateType ← termOfExpr range.state.type.nativeType
  let stateCore ← termOfExpr (coreTypeExpr range.state.type.coreTy)
  let representation ← termOfExpr range.state.type.representation
  let resultCore ← termOfExpr (coreTypeExpr site.result)
  let returnRep ← `(Complexity.Language.Representation.ofEmbedding
    (Function.Embedding.refl (Complexity.Language.Value $resultCore)))
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
  let embedding := resolveRaw range.embedding nativeSubstitution
  let mutableStep := resolveRaw range.mutableStep nativeSubstitution
  let initialMutable := resolveRaw range.initialMutable nativeSubstitution
  let indices := resolveRaw range.indices nativeSubstitution
  let fields ← sourceFields site.scope.size ⟨locals.raw⟩
  let selected ← range.select ⟨locals.raw⟩
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
    position != site.cursorSlot && !mutableSlots.contains position)
  for (_, position) in fixedSlots.reverse do
    fixedType ← `($(fields[position]!) = $(argumentTerms[position]!) ∧ $fixedType)
  let mut fixedTail : TSyntax `term := ⟨fixed.raw⟩
  for _ in fixedSlots do
    fixedFacts := fixedFacts.push (← `(($fixedTail).1))
    fixedTail ← `(($fixedTail).2)
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
    let rawState := resolveRaw returnedModel.rawModel context.known
    let observed ← observationAt range.returned context.heap context.relations
    let mut afterFields := fields
    for binding in range.captured, position in positions, field in [:range.captured.size] do
      if binding.mutable then
        afterFields := afterFields.set! position (← fieldProjection range.captured.size field rawState)
    afterFields := afterFields.set! site.cursorSlot (← `($index:ident + $(strideModel.model)))
    let after ← sourceTuple afterFields
    let selectedAfter ← range.select after
    let nextObserved ← `(($representation : Complexity.Language.Representation $stateType $stateCore).Rel
      ($bodyNative $index:ident $state:ident) $selectedAfter $(context.heap))
    let nextFrame ← if preserveArrays then
        `(And.intro
          (Complexity.Language.Heap.ShapeExtends.trans $frameShape $(context.shape))
          (fun {kind} buffer values observed =>
            $(context.contents) (kind := kind) buffer values
              ($frameContents (kind := kind) buffer values observed)))
      else `(Complexity.Language.Heap.ShapeExtends.trans $frameShape $(context.shape))
    let scalarFacts ← context.scalarEqualities.mapM fun equality =>
      `(Lean.Parser.Tactic.simpLemma| $equality:term)
    let executed ← `(by first
      | rfl
      | simp only [$cursorEqual:ident, $strideEqual:ident, $fixedSimp,*, $scalarFacts,*])
    let returnedObserved ← `(by
      change $nextObserved
      exact $observed)
    return #[← `(tactic|
      exact ⟨Complexity.Language.Control.normal, $after, $(context.heap), $executed,
        ⟨$returnedObserved, rfl, $fixed:ident, $nextFrame⟩, trivial⟩)]
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
      ← `(tactic| simp (config := { failIfUnchanged := false }) only [$cursorEqual:ident])] ++
    (← proveBody range.body range.returned ⟨current.raw⟩ bodyRelations
      bodyKnown preserveArrays bodyFinish)
  let after := mkIdent (← mkFreshUserName `rangeAfter)
  let finish := mkIdent (← mkFreshUserName `rangeFinish)
  let control := mkIdent (← mkFreshUserName `rangeControl)
  let executed := mkIdent (← mkFreshUserName `rangeExecuted)
  let outcome := mkIdent (← mkFreshUserName `rangeOutcome)
  let normal := mkIdent (← mkFreshUserName `rangeNormal)
  let foldEqual := mkIdent (← mkFreshUserName `rangeFoldEqual)
  let finalObserved := mkIdent (← mkFreshUserName `rangeFinalObserved)
  let selectedAfter ← range.select ⟨after.raw⟩
  let guardNormalize ← normalizeAction
  let mut localsEta ← `(Subsingleton.elim _ _)
  for _ in site.scope do localsEta ← `(Prod.ext rfl $localsEta)
  let proof ← `(tactic|
    have $summary:ident : ∃ ($after:ident : $localsType:ident)
        ($finish:ident : Complexity.Language.Heap),
        $action $heap = Part.some ((Complexity.Language.Control.normal, $after:ident), $finish:ident) ∧
        ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
          $(resultModel.model) $selectedAfter $finish:ident ∧ $heapPost $finish:ident := by
      have $startEqual:ident : $entryCursor = $(startModel.model) := Eq.symm $startObserved
      have $stopEqual:ident : $frozenStop = $(stopModel.model) := Eq.symm $stopObserved
      have $strideEqual:ident : $frozenStride = $(strideModel.model) := Eq.symm $strideObserved
      have $positive:ident : 0 < $(strideModel.model) := by
        simp (config := { zetaDelta := true, failIfUnchanged := false }) only [Nat.add_eq] <;> omega
      let $stateRel:ident ($index:ident : Nat) ($state:ident : $stateType)
          ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap) : Prop :=
        ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
          $state:ident $selected $current:ident ∧
        $cursor = $index:ident ∧ $fixedType ∧ $heapPost $current:ident
      have $guardRel:ident : ∀ ($index:ident : Nat) ($state:ident : $stateType)
          ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
          $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
          ∃ after finish,
            Complexity.Language.Stmt.observe $view:ident $guard:ident $program:ident
              $locals:ident $current:ident =
              Part.some ((.returned (decide ($index:ident < $(stopModel.model))), after), finish) ∧
            $stateRel:ident $index:ident $state:ident after finish := by
        intro $index:ident $state:ident $locals:ident $current:ident $related:ident
        obtain ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩ := $related:ident
        refine ⟨$locals:ident, $current:ident, ?_,
          $stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩
        rw [$guardObserve:ident, $guardEquation:ident]
        $guardNormalize:tactic
        apply congrArg Part.some
        apply Prod.ext
        · apply Prod.ext
          · apply congrArg Complexity.Language.Control.returned
            simp only [$cursorEqual:ident, $stopEqual:ident, $fixedSimp,*]
          · exact $localsEta
        · rfl
      have $bodyRel:ident : ∀ ($index:ident : Nat) ($state:ident : $stateType)
          ($locals:ident : $localsType:ident) ($current:ident : Complexity.Language.Heap),
          $index:ident < $(stopModel.model) →
          $stateRel:ident $index:ident $state:ident $locals:ident $current:ident →
          ∃ control after finish,
            Complexity.Language.Stmt.observe $view:ident $body:ident $program:ident
              $locals:ident $current:ident = Part.some ((control, after), finish) ∧
            $stateRel:ident ($index:ident + $(strideModel.model))
              ($bodyNative $index:ident $state:ident) after finish ∧
            control.Represents $returnRep none finish := by
        intro $index:ident $state:ident $locals:ident $current:ident $active:ident $related:ident
        obtain ⟨$stateObserved:ident, $cursorEqual:ident, $fixed:ident, $framed:ident⟩ := $related:ident
        $bodyProof:tactic*
      obtain ⟨$control:ident, $after:ident, $finish:ident, $executed:ident, $outcome:ident⟩ :=
        Complexity.Language.Stmt.observe_while_rel_forIn_range_step
          $view:ident $program:ident $guard:ident $body:ident
          $(stopModel.model) $(strideModel.model) $positive:ident $stateRel:ident $returnRep
          (fun index state => (none, $bodyNative index state)) $guardRel:ident
          (by simpa only [Option.isSome_none, Bool.false_eq_true, if_false] using $bodyRel:ident)
          $(startModel.model) $(initialModel.model) $entry $heap
          ⟨$entryObserved, $startEqual:ident, by repeat' constructor, $initialFrame⟩
      simp only [Option.elim_none] at $outcome:ident
      rw [Complexity.Language.Stmt.forIn_range_step_yield_eq_foldl
        (α := Complexity.Language.Value $resultCore) $bodyNative
        $(startModel.model) $(stopModel.model) $(strideModel.model)
        $positive:ident $(initialModel.model)] at $outcome:ident
      simp only [Id.run] at $outcome:ident
      have $normal:ident : $control:ident = .normal := by
        cases $control:ident with
        | normal => rfl
        | returned _ => exact False.elim ($outcome:ident).2
        | fault _ => exact False.elim ($outcome:ident).2
      subst $control:ident
      change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
        $entry $heap = _ at $executed:ident
      rw [$observe:ident] at $executed:ident
      have $foldEqual:ident : ($indices).foldl
          (fun state index => $bodyNative index state) $(initialModel.model) = $(resultModel.model) :=
        List.foldl_hom $embedding (g₁ := $mutableStep)
          (g₂ := fun state index => $bodyNative index state)
          (l := $indices) (init := $initialMutable) (by intros; rfl)
      have $finalObserved:ident :
          ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
            (($indices).foldl (fun state index => $bodyNative index state) $(initialModel.model))
            $selectedAfter $finish:ident := ($outcome:ident).1.1
      rw [$foldEqual:ident] at $finalObserved:ident
      exact ⟨$after:ident, $finish:ident, $executed:ident, $finalObserved:ident,
        ($outcome:ident).1.2.2.2⟩)
  return (#[extract, proof], ⟨summary.raw⟩)

end Internal

end Complexity.Language.Syntax.Represented
