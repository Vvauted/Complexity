/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Range

/-!
# Heap-indexed correspondence of represented traces

Compose the selected operations, branches and actual finite ranges through
their heap-indexed relations. Old contents are retained only when the supplied
operation contracts establish the required preservation.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal


/-- Equality of an identity-view product also rewrites its actual coordinate
uses. This is proof-side decomposition of equality, not a source projection. -/
private partial def identityCoordinateEqualities (type : Ty) (equality : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  match type with
  | .prod left right =>
      let leftProof ← `(congrArg Prod.fst $equality)
      let rightProof ← `(congrArg Prod.snd $equality)
      return #[equality] ++ (← identityCoordinateEqualities left leftProof) ++
        (← identityCoordinateEqualities right rightProof)
  | _ => return #[equality]

partial def relationTrace (trace : Array Trace) (returnedValue : Value)
    (initialHeap : TSyntax `term) (initialRelations : Array RetainedObservation)
    (initialKnown : Array (Name × TSyntax `term) := #[]) (preserveArrays : Bool := false)
    (ranges : Array RangeRegistration := #[]) (finish? : Option TraceFinish := none)
    (seed? : Option TraceContext := none) (actualBranches : Bool := false) :
    TermElabM (Array (TSyntax `tactic)) := do
  let initial : TraceContext ← match seed? with
    | some context => pure context
    | none => do
        pure {
          heap := initialHeap
          relations := initialRelations
          known := initialKnown
          scalarEqualities := #[]
          shape := ← `(Complexity.Language.Heap.ShapeExtends.refl $initialHeap)
          contents := ← `((by intro kind view values observed; exact observed :
            Complexity.Language.Buffer.PreservesContents $initialHeap $initialHeap)) }
  let mut relations := initial.relations
  let mut known := initial.known
  let mut scalarEqualities := initial.scalarEqualities
  let mut currentHeap := initial.heap
  let mut preserved := initial.shape
  let mut preservedContents := initial.contents
  let branchRules := initial.branchRules
  let actualBranches := actualBranches || finish?.isSome || trace.any Trace.containsRange
  let mut tactics := #[← normalizeAction]
  unless branchRules.isEmpty do
    tactics := tactics.push (← `(tactic|
      simp (config := { failIfUnchanged := false }) only [$branchRules,*]))
  let finishChoice (arm : Value) (result : Binding)
      (selected : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
      (rest : Array Trace) : TraceFinish := fun context => do
    let armModel ← arm.requireModel
    let resultModel ← result.requireModel
    let actual := resolveRaw armModel.rawModel context.known
    let observed ← observationAt arm context.heap context.relations
    let nativeType ← termOfExpr result.type.nativeType
    let coreType ← termOfExpr (coreTypeExpr result.type.coreTy)
    let representation ← termOfExpr result.type.representation
    let joined := result.relationName
    let armObserved := mkIdent (← mkFreshUserName `armObserved)
    let selected := context.branchRules ++ selected
    let mut joinTactics := #[← `(tactic|
      have $armObserved:ident : ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
          $(armModel.model) $actual $(context.heap) := $observed),
      ← `(tactic|
      have $joined:ident : ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
          $(resultModel.model) $actual $(context.heap) := by
        simpa (config := { implicitDefEqProofs := false }) only
          [Id.run, Id.instMonad, Pure.pure, Bind.bind, $selected,*]
          using $armObserved:ident)]
    let mut next := context
    if result.type.isIdentity then
      joinTactics := joinTactics.push (← `(tactic| change $(resultModel.model) = $actual at $joined:ident))
      let equalities ← identityCoordinateEqualities result.type.coreTy ⟨joined.raw⟩
      let rewrites ← equalities.mapM fun equality =>
        `(Lean.Parser.Tactic.simpLemma| ← $equality:term)
      joinTactics := joinTactics.push (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [$rewrites,*]))
      next := { next with
        known := (next.known.filter (fun entry => entry.1 != result.rawName.getId)).push
          (result.rawName.getId, resultModel.model)
        scalarEqualities := next.scalarEqualities ++ equalities }
    else
      next := { next with
        known := (next.known.filter (fun entry => entry.1 != result.rawName.getId)).push
          (result.rawName.getId, actual)
        relations := next.relations.push ⟨joined.getId, result.type, ⟨joined.raw⟩⟩ }
    return joinTactics ++ (← relationTrace rest returnedValue next.heap next.relations next.known
      preserveArrays ranges finish? (some next) true)
  for (instruction, position) in trace.zipIdx do
    if actualBranches then
      let context : TraceContext := {
        heap := currentHeap, relations, known, scalarEqualities,
        shape := preserved, contents := preservedContents, branchRules }
      let rest := trace.extract (position + 1) trace.size
      match instruction with
      | .conditional condition yes no yesResult noResult result =>
          let observation ← observationAt condition currentHeap relations
          let condition ← condition.requireModel
          let equality := mkIdent (← mkFreshUserName `conditionEqual)
          let selected := mkIdent (← mkFreshUserName `conditionSelected)
          let raw := resolveRaw condition.rawModel known
          let context := { context with
            scalarEqualities := context.scalarEqualities.push ⟨equality.raw⟩ }
          let yesRules := #[← `(Lean.Parser.Tactic.simpLemma| if_pos $selected:ident)]
          let noRules := #[← `(Lean.Parser.Tactic.simpLemma| if_neg $selected:ident)]
          let yesProof ← relationTrace yes yesResult currentHeap relations known preserveArrays ranges
            (some (finishChoice yesResult result yesRules rest))
            (some { context with branchRules := branchRules ++ yesRules }) true
          let noProof ← relationTrace no noResult currentHeap relations known preserveArrays ranges
            (some (finishChoice noResult result noRules rest))
            (some { context with branchRules := branchRules ++ noRules }) true
          return tactics ++ #[
            ← `(tactic| have $equality:ident : $(condition.model) = $raw := $observation),
            ← `(tactic| dsimp (config := { failIfUnchanged := false }) only at $equality:ident),
            ← `(tactic| simp (config := { failIfUnchanged := false }) only [← $equality:ident]),
            ← `(tactic| focus
              by_cases $selected:ident : $(condition.model) = true
              · simp (config := { failIfUnchanged := false }) only [$yesRules,*]
                $yesProof:tactic*
              · simp (config := { failIfUnchanged := false }) only [$noRules,*]
                $noProof:tactic*)]
      | .optionMatch discriminant payload absent present noneResult someResult result =>
          let discriminantModel ← discriminant.requireModel
          let payloadModel ← payload.requireModel
          let raw := resolveRaw discriminantModel.rawModel known
          let nativeType ← termOfExpr discriminant.type.nativeType
          let coreType ← termOfExpr (coreTypeExpr discriminant.type.coreTy)
          let representation ← termOfExpr discriminant.type.representation
          let payloadType ← termOfExpr payload.type.nativeType
          let payloadCore ← termOfExpr (coreTypeExpr payload.type.coreTy)
          let payloadRepresentation ← termOfExpr payload.type.representation
          let observation ← observationAt discriminant currentHeap relations
          let observed := mkIdent (← mkFreshUserName `optionObserved)
          let rawCase := mkIdent (← mkFreshUserName `sourceCase)
          let nativeCase := mkIdent (← mkFreshUserName `nativeCase)
          let selectedRaw := mkIdent (← mkFreshUserName `selectedSourceCase)
          let selectedNative := mkIdent (← mkFreshUserName `selectedNativeCase)
          let impossible := mkIdent (← mkFreshUserName `impossiblePayload)
          let payloadObserved := payload.relationName
          let selectedObservation ← `(Eq.mp
            (congrArg₂
              (fun native actual => ($representation :
                Complexity.Language.Representation $nativeType $coreType).Rel
                  native actual $currentHeap)
              $nativeCase:ident $rawCase:ident)
            $observed:ident)
          let normalizeCases ← `(tactic|
            dsimp (config := { failIfUnchanged := false }) only
              [Id.run, Id.instMonad, Pure.pure, Bind.bind] at $rawCase:ident $nativeCase:ident)
          -- A completion choice may already be fixed by its enclosing branch.
          -- Keep the original equations for relation transport, but normalize
          -- copies to eliminate impossible cases and retain payload equalities.
          let selectCases := #[
            ← `(tactic| have $selectedRaw:ident := $rawCase:ident),
            ← `(tactic| have $selectedNative:ident := $nativeCase:ident),
            ← `(tactic| simp (config := { failIfUnchanged := false }) only
              [Id.run, Id.instMonad, Pure.pure, Bind.bind,
                Option.elim_none, Option.elim_some, Option.some.injEq, reduceCtorEq,
                ↓reduceIte, $branchRules,*] at $selectedRaw:ident $selectedNative:ident)]
          let rules := #[
            ← `(Lean.Parser.Tactic.simpLemma| $rawCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| $nativeCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| $selectedRaw:ident),
            ← `(Lean.Parser.Tactic.simpLemma| $selectedNative:ident),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_none),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_some)]
          let context := { context with branchRules := branchRules ++ rules }
          let noneProof ← relationTrace absent noneResult currentHeap relations known preserveArrays ranges
            (some (finishChoice noneResult result rules rest)) (some context) true
          let mut someContext := context
          let mut somePrefix := #[]
          if payload.type.isIdentity then
            somePrefix := #[
              ← `(tactic| change $(payloadModel.model) = $(payload.rawName):ident at $payloadObserved:ident),
              ← `(tactic| subst $(payload.rawName):ident)]
            someContext := { someContext with
              known := someContext.known.push (payload.rawName.getId, payloadModel.model) }
          else
            someContext := { someContext with
              relations := someContext.relations.push
                ⟨payloadObserved.getId, payload.type, ⟨payloadObserved.raw⟩⟩ }
          let someProof ← relationTrace present someResult currentHeap someContext.relations
            someContext.known preserveArrays ranges
            (some (finishChoice someResult result rules rest)) (some someContext) true
          let someProof := somePrefix ++ someProof
          return tactics ++ #[← `(tactic| focus
            have $observed:ident : ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
                $(discriminantModel.model) $raw $currentHeap := $observation
            cases $rawCase:ident : $raw:term with
            | none =>
                cases $nativeCase:ident : $(discriminantModel.model):term with
                | none =>
                    $normalizeCases:tactic
                    $selectCases:tactic*
                    all_goals
                      simp (config := { failIfUnchanged := false }) only [$rules,*]
                      $noneProof:tactic*
                | some $impossible:ident =>
                    $normalizeCases:tactic
                    exact False.elim $selectedObservation
            | some $(payload.rawName):ident =>
                cases $nativeCase:ident : $(discriminantModel.model):term with
                | none =>
                    $normalizeCases:tactic
                    exact False.elim $selectedObservation
                | some $(payload.nativeName):ident =>
                    $normalizeCases:tactic
                    $selectCases:tactic*
                    all_goals
                      have $payloadObserved:ident : ($payloadRepresentation :
                          Complexity.Language.Representation $payloadType $payloadCore).Rel
                          $(payload.nativeName):ident $(payload.rawName):ident $currentHeap :=
                        $selectedObservation
                      simp (config := { failIfUnchanged := false }) only [$rules,*]
                      $someProof:tactic*)]
      | _ => pure ()
    let mut rangeFixedCount : Option Nat := none
    let (result, relationProof) ← match instruction with
      | .call invocation => do
          let models ← invocation.arguments.mapM Value.requireModel
          let operation ← invocation.operation.requireModel
          let mut applied := models.map (·.model)
          let mut hypotheses := #[]
          for argument in invocation.arguments, model in models do
            if argument.type.isIdentity then
              let observed ← observationAt argument currentHeap relations
              let equality := mkIdent (← mkFreshUserName `argumentEqual)
              let raw := resolveRaw model.rawModel known
              tactics := tactics.push (← `(tactic|
                have $equality:ident : $(model.model) = $raw := $observed))
              tactics := tactics.push (← `(tactic|
                dsimp (config := { failIfUnchanged := false }) only at $equality:ident))
              scalarEqualities := scalarEqualities.push ⟨equality.raw⟩
              tactics := tactics.push (← `(tactic|
                simp (config := { failIfUnchanged := false }) only [← $equality:ident]))
            else
              applied := applied.push (resolveRaw model.rawModel known)
              hypotheses := hypotheses.push (← observationAt argument currentHeap relations)
          applied := applied.push currentHeap ++ hypotheses
          let relation ← if preserveArrays then do
              let some strong := operation.preservingRelation
                | throwError "native array composition requires a proved contents-preserving call"
              pure strong
            else pure operation.relation
          pure (invocation.result, Lean.Syntax.mkApp ⟨relation.raw⟩ applied)
      | .range tag arguments result _ => do
          let some range := ranges.find? (fun range => range.tag == tag)
            | throwError "the proof trace has no matching prepared range"
          let some initial := arguments[0]?
            | throwError "a range observation requires its entry state"
          let (setup, proof, fixedCount) ←
            rangeRelationProof range initial currentHeap relations known preserveArrays
              (fun body returned heap observations known strong finish =>
                relationTrace body returned heap observations known strong ranges (some finish))
          tactics := tactics ++ setup
          rangeFixedCount := some fixedCount
          pure (result, proof)
      | .conditional condition yes no yesResult noResult result => do
          let observed ← observationAt condition currentHeap relations
          let condition ← condition.requireModel
          let resultModel ← result.requireModel
          let equality := mkIdent (← mkFreshUserName `conditionEqual)
          let rawCondition := resolveRaw condition.rawModel known
          tactics := tactics.push (← `(tactic|
            have $equality:ident : $(condition.model) = $rawCondition := $observed))
          tactics := tactics.push (← `(tactic|
            dsimp (config := { failIfUnchanged := false }) only at $equality:ident))
          scalarEqualities := scalarEqualities.push ⟨equality.raw⟩
          tactics := tactics.push (← `(tactic|
            simp (config := { failIfUnchanged := false }) only [← $equality:ident]))
          let yesAction ← traceAction yes.toList yesResult known
          let noAction ← traceAction no.toList noResult known
          let type ← actualTypeTerm result.type.coreTy
          let coreType ← termOfExpr (coreTypeExpr result.type.coreTy)
          let nativeType ← termOfExpr result.type.nativeType
          let representation ← termOfExpr result.type.representation
          let summary := mkIdent (← mkFreshUserName `branchRelated)
          let test := mkIdent (← mkFreshUserName `branchSelected)
          let branchContext : TraceContext := {
            heap := currentHeap, relations, known, scalarEqualities := #[]
            shape := ← `(Complexity.Language.Heap.ShapeExtends.refl $currentHeap)
            contents := ← `((by intro kind view values observed; exact observed :
              Complexity.Language.Buffer.PreservesContents $currentHeap $currentHeap))
            branchRules }
          let yesRules := branchRules.push (← `(Lean.Parser.Tactic.simpLemma| if_pos $test:ident))
          let noRules := branchRules.push (← `(Lean.Parser.Tactic.simpLemma| if_neg $test:ident))
          let yesProof ← relationTrace yes yesResult currentHeap relations known preserveArrays
            ranges none (some { branchContext with branchRules := yesRules })
          let noProof ← relationTrace no noResult currentHeap relations known preserveArrays
            ranges none (some { branchContext with branchRules := noRules })
          let heapPost ← if preserveArrays then
              `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish ∧
                Complexity.Language.Buffer.PreservesContents $currentHeap finish)
            else `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish)
          tactics := tactics.push (← `(tactic|
            have $summary:ident : ∃ (returned : $type) (finish : Complexity.Language.Heap),
                (if $(condition.model) then $yesAction else $noAction) $currentHeap =
                  Part.some (.ok returned, finish) ∧
                ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
                  $(resultModel.model) returned finish ∧
                $heapPost finish := by
              by_cases $test:ident : $(condition.model) = true
              · simp only [if_pos $test:ident]
                $yesProof:tactic*
              · simp only [if_neg $test:ident]
                $noProof:tactic*))
          pure (result, (⟨summary.raw⟩ : TSyntax `term))
      | .optionMatch discriminant payload absent present noneResult someResult result => do
          let discriminantModel ← discriminant.requireModel
          let payloadModel ← payload.requireModel
          let resultModel ← result.requireModel
          let noneAction ← traceAction absent.toList noneResult known
          let someAction ← traceAction present.toList someResult known
          let raw := resolveRaw discriminantModel.rawModel known
          let type ← actualTypeTerm result.type.coreTy
          let coreType ← termOfExpr (coreTypeExpr result.type.coreTy)
          let nativeType ← termOfExpr result.type.nativeType
          let representation ← termOfExpr result.type.representation
          let discriminantType ← termOfExpr discriminant.type.nativeType
          let discriminantCore ← termOfExpr (coreTypeExpr discriminant.type.coreTy)
          let discriminantRepresentation ← termOfExpr discriminant.type.representation
          let payloadType ← termOfExpr payload.type.nativeType
          let rawPayloadType ← actualTypeTerm payload.type.coreTy
          let payloadCore ← termOfExpr (coreTypeExpr payload.type.coreTy)
          let payloadRepresentation ← termOfExpr payload.type.representation
          let summary := mkIdent (← mkFreshUserName `matchRelated)
          let observed := mkIdent (← mkFreshUserName `optionObserved)
          let rawCase := mkIdent (← mkFreshUserName `sourceCase)
          let nativeCase := mkIdent (← mkFreshUserName `nativeCase)
          let impossible := mkIdent (← mkFreshUserName `impossiblePayload)
          let payloadObserved := payload.relationName
          let observation ← observationAt discriminant currentHeap relations
          let rules := branchRules ++ #[
            ← `(Lean.Parser.Tactic.simpLemma| $rawCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| $nativeCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_none),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_some)]
          let branchContext : TraceContext := {
            heap := currentHeap, relations, known, scalarEqualities := #[]
            shape := ← `(Complexity.Language.Heap.ShapeExtends.refl $currentHeap)
            contents := ← `((by intro kind view values observed; exact observed :
              Complexity.Language.Buffer.PreservesContents $currentHeap $currentHeap))
            branchRules := rules }
          let noneProof ← relationTrace absent noneResult currentHeap relations known preserveArrays
            ranges none (some branchContext)
          let mut someRelations := relations
          let mut someKnown := known
          let mut somePrefix := #[]
          if payload.type.isIdentity then
            somePrefix := somePrefix.push (← `(tactic|
              change $(payloadModel.model) = $(payload.rawName):ident at $payloadObserved:ident))
            somePrefix := somePrefix.push (← `(tactic| subst $(payload.rawName):ident))
            someKnown := someKnown.push (payload.rawName.getId, payloadModel.model)
          else
            someRelations := someRelations.push ⟨payloadObserved.getId, payload.type,
              ⟨payloadObserved.raw⟩⟩
          let someProof := somePrefix ++
            (← relationTrace present someResult currentHeap someRelations someKnown preserveArrays
              ranges none (some { branchContext with relations := someRelations, known := someKnown }))
          let heapPost ← if preserveArrays then
              `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish ∧
                Complexity.Language.Buffer.PreservesContents $currentHeap finish)
            else `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish)
          tactics := tactics.push (← `(tactic|
            have $summary:ident : ∃ (returned : $type) (finish : Complexity.Language.Heap),
                (Option.elim $raw $noneAction:term
                  (fun ($(payload.rawName):ident : $rawPayloadType) => $someAction:term)) $currentHeap =
                    Part.some (.ok returned, finish) ∧
                ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
                  $(resultModel.model) returned finish ∧
                $heapPost finish := by
              have $observed:ident :
                  ($discriminantRepresentation : Complexity.Language.Representation
                    $discriminantType $discriminantCore).Rel $(discriminantModel.model) $raw $currentHeap :=
                $observation
              cases $rawCase:ident : $raw:term with
              | none =>
                  cases $nativeCase:ident : $(discriminantModel.model):term with
                  | none =>
                      simp (config := { failIfUnchanged := false }) only [$rawCase:ident, $nativeCase:ident,
                        Option.elim_none, Option.elim_some]
                      $noneProof:tactic*
                  | some $impossible:ident =>
                      simp only [Complexity.Language.Representation.option, $rawCase:ident,
                        $nativeCase:ident] at $observed:ident
              | some $(payload.rawName):ident =>
                  cases $nativeCase:ident : $(discriminantModel.model):term with
                  | none =>
                      simp only [Complexity.Language.Representation.option, $rawCase:ident,
                        $nativeCase:ident] at $observed:ident
                  | some $(payload.nativeName):ident =>
                      have $payloadObserved:ident :
                          ($payloadRepresentation : Complexity.Language.Representation
                            $payloadType $payloadCore).Rel
                            $(payload.nativeName):ident $(payload.rawName):ident $currentHeap := by
                        simpa only [Complexity.Language.Representation.option, $rawCase:ident,
                          $nativeCase:ident] using $observed:ident
                      simp (config := { failIfUnchanged := false }) only [$rawCase:ident, $nativeCase:ident,
                        Option.elim_none, Option.elim_some]
                      $someProof:tactic*))
          pure (result, (⟨summary.raw⟩ : TSyntax `term))
    let returned := result.rawName
    let observed := result.relationName
    let finish := mkIdent (← mkFreshUserName `nextHeap)
    let executed := mkIdent (← mkFreshUserName `callExecuted)
    let extended := mkIdent (← mkFreshUserName `callExtended)
    let contents := mkIdent (← mkFreshUserName `contentsPreserved)
    let range? : Option RangeRegistration := match instruction with
      | .range tag _ _ _ => ranges.find? (fun range => range.tag == tag)
      | _ => none
    let returnsFromFunction ← match range? with
      | some range => range.returnsFromFunction
      | none => pure false
    let actualResult := mkIdent (← mkFreshUserName `rangeReturned)
    tactics := tactics.push (← if returnsFromFunction then `(tactic|
        obtain ⟨$actualResult:ident, $returned:ident, $finish:ident, $executed:ident,
            $observed:ident, $extended:ident⟩ := $relationProof)
      else `(tactic|
        obtain ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident, $extended:ident⟩ :=
          $relationProof))
    let mut rangeFixedFacts : Array (TSyntax `term) := #[]
    if let some fixedCount := rangeFixedCount then
      let fixed := mkIdent (← mkFreshUserName `rangeFixedLocals)
      tactics := tactics.push (← `(tactic| obtain ⟨$extended:ident, $fixed:ident⟩ := $extended:ident))
      let mut remaining : TSyntax `term := ⟨fixed.raw⟩
      for _ in [:fixedCount] do
        rangeFixedFacts := rangeFixedFacts.push (← `(($remaining).1))
        remaining ← `(($remaining).2)
      scalarEqualities := scalarEqualities ++ rangeFixedFacts
    if preserveArrays then
      tactics := tactics.push (← `(tactic|
        obtain ⟨$extended:ident, $contents:ident⟩ := $extended:ident))
    if let some range := range? then
      let actualResult? := if returnsFromFunction then some (⟨actualResult.raw⟩ : TSyntax `term)
        else none
      let selected ← range.select ⟨returned.raw⟩ actualResult?
      known := known.push (result.rawName.getId, selected)
      if result.type.isIdentity then
        let model ← result.requireModel
        tactics := tactics.push (← `(tactic| change $(model.model) = $selected at $observed:ident))
        scalarEqualities := scalarEqualities.push ⟨observed.raw⟩
    else if result.type.isIdentity then
      let model ← result.requireModel
      tactics := tactics.push (← `(tactic| change $(model.model) = $returned:ident at $observed:ident))
      tactics := tactics.push (← `(tactic| subst $returned:ident))
      known := known.push (result.rawName.getId, model.model)
    tactics := tactics.push (← `(tactic|
      simp (config := { failIfUnchanged := false }) only [Id.run, Id.instMonad, Bind.bind, Pure.pure,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
        StateT.bind, StateT.pure, Part.bind_some, $branchRules,*] at $executed:ident))
    tactics := tactics.push (← `(tactic| rw [$executed:ident]))
    tactics := tactics.push (← normalizeAction)
    unless rangeFixedFacts.isEmpty do
      let rules ← rangeFixedFacts.mapM fun fact => `(Lean.Parser.Tactic.simpLemma| $fact:term)
      tactics := tactics.push (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [$rules,*]))
      tactics := tactics.push (← normalizeAction)
    if range?.isSome && result.type.isIdentity then
      tactics := tactics.push (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [← $observed:ident]))
      let model ← result.requireModel
      known := (known.filter (fun entry => entry.1 != result.rawName.getId)).push
        (result.rawName.getId, model.model)
    let mut nextRelations := #[]
    for entry in relations do
      let transported := mkIdent (← mkFreshUserName `retainedList)
      let keeps ← preservation entry.type currentHeap ⟨finish.raw⟩ ⟨extended.raw⟩
        (if preserveArrays then some ⟨contents.raw⟩ else none)
      tactics := tactics.push (← `(tactic|
        have $transported:ident := $keeps $(entry.proof)))
      nextRelations := nextRelations.push ⟨entry.name, entry.type, ⟨transported.raw⟩⟩
    relations := nextRelations
    unless result.type.isIdentity do
      relations := relations.push ⟨observed.getId, result.type, ⟨observed.raw⟩⟩
    preserved ← `(Complexity.Language.Heap.ShapeExtends.trans $preserved $extended:ident)
    if preserveArrays then
      preservedContents ← `(fun {kind} view values observed =>
        $contents:ident (kind := kind) view values ($preservedContents view values observed))
    currentHeap := ⟨finish.raw⟩
    if range?.any (fun range => match range.model with
        | .completion .. => true | .fold .. => false) then
      -- Share this invocation's mathematical result only in its continuation.
      -- Fresh names and exact subterms keep later generic loop bodies separate;
      -- the actual payload, locals and heap still come from the observation.
      let model ← result.requireModel
      let sharedTerm := match model.model with
        | `(let $_:ident := $outcome; $_) => outcome
        | _ => model.model
      let shared := mkIdent (← mkFreshUserName `rangeModel)
      let context : TraceContext := {
        heap := currentHeap, relations, known, scalarEqualities,
        shape := preserved, contents := preservedContents, branchRules }
      let continuation ← relationTrace (trace.extract (position + 1) trace.size)
        returnedValue currentHeap relations known preserveArrays ranges finish?
        (some context) actualBranches
      let continuation := continuation.map fun tactic =>
        (⟨tactic.raw.rewriteBottomUp fun stx =>
          if stx == sharedTerm.raw then shared.raw else stx⟩ : TSyntax `tactic)
      let equal := mkIdent (← mkFreshUserName `rangeModelEqual)
      return tactics ++ #[← `(tactic| let $shared:ident := $sharedTerm),
        ← `(tactic| have $equal:ident : $sharedTerm = $shared:ident := rfl),
        ← `(tactic| dsimp only [Id.run, Id.instMonad, Pure.pure, Bind.bind] at $equal:ident),
        ← `(tactic| simp only [$equal:ident])] ++ continuation
  if let some finish := finish? then
    return tactics ++ (← finish {
      heap := currentHeap, relations, known, scalarEqualities,
      shape := preserved, contents := preservedContents, branchRules })
  let observed ← observationAt returnedValue currentHeap relations
  let returnedModel ← returnedValue.requireModel
  let result := resolveRaw returnedModel.rawModel known
  let nativeType ← termOfExpr returnedValue.type.nativeType
  let coreType ← termOfExpr (coreTypeExpr returnedValue.type.coreTy)
  let representation ← termOfExpr returnedValue.type.representation
  let observed ← `(show ($representation :
      Complexity.Language.Representation $nativeType $coreType).Rel
      $(returnedModel.model) $result $currentHeap from $observed)
  let heapPost ← if preserveArrays then `(And.intro $preserved $preservedContents) else pure preserved
  -- Argument rewrites also affect scalar fields retained in a mixed raw state.
  -- Keep their actual projection equalities, without replacing its heap-backed
  -- representation by equality of the whole native and raw values.
  let scalarFacts ← scalarEqualities.mapM fun equality =>
    `(Lean.Parser.Tactic.simpLemma| $equality:term)
  let executionRules := scalarFacts ++ branchRules
  let executed ← `(by first | rfl | simp only [$executionRules,*] <;> rfl)
  let observed ← `(by
    simpa (config := { implicitDefEqProofs := false }) only
      [Id.run, Id.instMonad, Pure.pure, Bind.bind, $branchRules,*] using $observed)
  tactics := tactics.push (← `(tactic|
    exact ⟨$result, $currentHeap, $executed, $observed, $heapPost⟩))
  return tactics

end Internal

end Complexity.Language.Syntax.Represented
