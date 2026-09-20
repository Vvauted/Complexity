/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic

/-!
# Exact unchanged-heap correspondence of represented traces

Compose checked unchanged-heap equations for encoded mathematical values.
Allocating operations and ranges do not acquire an exact equation merely from
having a mathematical result relation.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def encodedValue (type : NativeType) (value : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  if type.isIdentity then return value
  let encoding ← PureImport.encoding type
  `($(← termOfExpr encoding.embedding) $value)
/-- Compose only checked unchanged-heap equations. Branches select their actual
callee, and mathematical records are returned through their checked encoding. -/
partial def exactTrace (trace : Array Trace) (returnedValue : Value)
    (heap : TSyntax `term) (initialRelations : Array RetainedObservation)
    (initialKnown : Array (Name × TSyntax `term) := #[]) :
    TermElabM (Array (TSyntax `tactic)) := do
  let mut relations := initialRelations
  let mut known := initialKnown
  let mut scalarEqualities : Array (TSyntax `term) := #[]
  let mut tactics := #[← normalizeAction]
  for instruction in trace do
    let (result, equation) ← match instruction with
      | .call invocation => do
          let operation ← invocation.operation.requireModel
          let models ← invocation.arguments.mapM Value.requireModel
          let mut applied := models.map (·.model)
          let mut hypotheses := #[]
          for argument in invocation.arguments, model in models do
            if argument.type.isIdentity then
              let observed ← observationAt argument heap relations
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
              hypotheses := hypotheses.push (← observationAt argument heap relations)
          applied := applied.push heap ++ hypotheses
          let some equation := operation.equation
            | throwError "an allocating operation has no unchanged-heap equation"
          pure (invocation.result, Lean.Syntax.mkApp ⟨equation.raw⟩ applied)
      | .conditional condition yes no yesResult noResult result => do
          let observed ← observationAt condition heap relations
          let condition ← condition.requireModel
          let resultModel ← result.requireModel
          let value ← encodedValue result.type resultModel.model
          let rawCondition := resolveRaw condition.rawModel known
          let equality := mkIdent (← mkFreshUserName `conditionEqual)
          tactics := tactics.push (← `(tactic|
            have $equality:ident : $(condition.model) = $rawCondition := $observed))
          scalarEqualities := scalarEqualities.push ⟨equality.raw⟩
          tactics := tactics.push (← `(tactic|
            simp (config := { failIfUnchanged := false }) only [← $equality:ident]))
          let yesAction ← traceAction yes.toList yesResult known
          let noAction ← traceAction no.toList noResult known
          let summary := mkIdent (← mkFreshUserName `branchExact)
          let test := mkIdent (← mkFreshUserName `branchSelected)
          let yesProof ← exactTrace yes yesResult heap relations known
          let noProof ← exactTrace no noResult heap relations known
          tactics := tactics.push (← `(tactic|
            have $summary:ident :
                (if $(condition.model) then $yesAction else $noAction) $heap =
                  Part.some (.ok $value, $heap) := by
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
          let value ← encodedValue result.type resultModel.model
          let noneAction ← traceAction absent.toList noneResult known
          let someAction ← traceAction present.toList someResult known
          let raw := resolveRaw discriminantModel.rawModel known
          let discriminantType ← termOfExpr discriminant.type.nativeType
          let discriminantCore ← termOfExpr (coreTypeExpr discriminant.type.coreTy)
          let discriminantRepresentation ← termOfExpr discriminant.type.representation
          let payloadType ← termOfExpr payload.type.nativeType
          let rawPayloadType ← actualTypeTerm payload.type.coreTy
          let payloadCore ← termOfExpr (coreTypeExpr payload.type.coreTy)
          let payloadRepresentation ← termOfExpr payload.type.representation
          let summary := mkIdent (← mkFreshUserName `matchExact)
          let observed := mkIdent (← mkFreshUserName `optionObserved)
          let rawCase := mkIdent (← mkFreshUserName `sourceCase)
          let nativeCase := mkIdent (← mkFreshUserName `nativeCase)
          let impossible := mkIdent (← mkFreshUserName `impossiblePayload)
          let payloadObserved := payload.relationName
          let observation ← observationAt discriminant heap relations
          let noneProof ← exactTrace absent noneResult heap relations known
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
            (← exactTrace present someResult heap someRelations someKnown)
          tactics := tactics.push (← `(tactic|
            have $summary:ident :
                (Option.elim $raw $noneAction:term
                  (fun ($(payload.rawName):ident : $rawPayloadType) => $someAction:term)) $heap =
                    Part.some (.ok $value, $heap) := by
              have $observed:ident :
                  ($discriminantRepresentation : Complexity.Language.Representation
                    $discriminantType $discriminantCore).Rel $(discriminantModel.model) $raw $heap :=
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
                            $(payload.nativeName):ident $(payload.rawName):ident $heap := by
                        simpa only [Complexity.Language.Representation.option, $rawCase:ident,
                          $nativeCase:ident] using $observed:ident
                      simp (config := { failIfUnchanged := false }) only [$rawCase:ident, $nativeCase:ident,
                        Option.elim_none, Option.elim_some]
                      $someProof:tactic*))
          pure (result, (⟨summary.raw⟩ : TSyntax `term))
      | .range .. => throwError "range execution has no generated unchanged-heap equation"
    let executed := mkIdent (← mkFreshUserName `callExecuted)
    let scalarFacts ← scalarEqualities.mapM fun equality =>
      `(Lean.Parser.Tactic.simpLemma| ← $equality:term)
    tactics := tactics.push (← `(tactic| have $executed:ident := $equation))
    tactics := tactics.push (← `(tactic|
      simp (config := { failIfUnchanged := false }) only [Id.run, Id.instMonad, Bind.bind, Pure.pure,
        Functor.map, MonadLift.monadLift, ExceptT.lift,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
        StateT.bind, StateT.pure, StateT.map, Part.bind_some, Part.map_some,
        $scalarFacts,*] at $executed:ident))
    tactics := tactics.push (← `(tactic| rw [$executed:ident]))
    tactics := tactics.push (← normalizeAction)
    let model ← result.requireModel
    let value ← encodedValue result.type model.model
    known := known.push (result.rawName.getId, value)
    unless result.type.isIdentity do
      let encoding ← PureImport.encoding result.type
      let exactEncoding ← encoding.relationSyntax
      let proof ← `(($exactEncoding $(model.model) $value $heap).mpr rfl)
      relations := relations.push ⟨result.relationName.getId, result.type, proof⟩
  let model ← returnedValue.requireModel
  let raw := resolveRaw model.rawModel known
  let value ← encodedValue returnedValue.type model.model
  let encoding ← PureImport.encoding returnedValue.type
  let exactEncoding ← encoding.relationSyntax
  let observed ← observationAt returnedValue heap relations
  let equality ← `(($exactEncoding $(model.model) $raw $heap).mp $observed)
  let type ← actualTypeTerm returnedValue.type.coreTy
  let scalarFacts ← scalarEqualities.mapM fun equality =>
    `(Lean.Parser.Tactic.simpLemma| ← $equality:term)
  let proof ← `(congrArg (fun (value : $type) =>
    Part.some ((Except.ok value : Except Complexity.Language.Fault $type), $heap))
    (show $value = $raw from $equality).symm)
  tactics := tactics.push (← `(tactic|
    first
    | rfl
    | exact $proof
    | simpa only [$scalarFacts,*] using $proof))
  tactics.mapM fun tactic => `(tactic| all_goals $tactic:tactic)

end Internal

end Complexity.Language.Syntax.Represented
