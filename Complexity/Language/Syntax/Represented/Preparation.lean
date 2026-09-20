/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Statements
import Lean.Util.SCC

/-!
# Represented functions and mathematical model dependencies

Prepare complete function bodies and resolve optional mathematical candidates
in callee-first order. Dependency analysis does not reorder the actual source
functions, invent termination, or suppress failed correspondence proofs.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def prepareFunction (names : DeclarationNames)
    (imports : ImportedPrograms) (declaration : ParsedDeclaration) : PrepareM Unit := do
  let family := names.publicFamily
  let name := declaration.name
  let body := declaration.body
  let termination := declaration.termination
  let hints ← Lean.Elab.elabTerminationHints termination
  if (← get).functions.any (fun fn => fn.name.getId == name.getId) then
    throwErrorAt name "duplicate native source function"
  let result ← resolveType declaration.result
  let mut parsed := #[]
  let mut scope := []
  for parameter in declaration.params do
    let parameterName := parameter.name
    let type ← resolveType parameter.type
    let rawName := mkIdent (← mkFreshUserName (parameterName.getId.appendAfter "_source"))
    let relation := mkIdent (← mkFreshUserName (parameterName.getId.appendAfter "_represented"))
    let rawModel := if type.isIdentity then ⟨parameterName.raw⟩ else ⟨rawName.raw⟩
    let parameter : Parameter := { name := parameterName, type, rawName, relationName := relation }
    parsed := parsed.push parameter
    let binding : Binding := {
      toParameter := parameter,
      model? := some {
        model := ⟨parameterName.raw⟩, rawModel
        observation := if type.isIdentity then .refl else .named relation.getId } }
    scope := binding :: scope
  let elements ← match body with
    | `(do $elements:doSeq) => pure (getDoElems elements).toList
    | _ => pure [← `(doElem| return $body:term)]
  -- Self calls always have a source target. A total recursive model is only
  -- requested by termination hints and checked with the same descent proof;
  -- partial fixed points do not request a total mathematical function.
  let current : Operation := {
    family := names.sourceFamily
    sourceName := name.getId
    inputs := parsed.map (·.type)
    result
    modelDependency? := some name.getId
    model? := if hints.isNotNone && hints.partialFixpoint?.isNone then some {
      native := ⟨(modelName names name).raw⟩
      equation := none
      relation := fieldName family name "_action_rel_native"
      refinement := fieldName family name "_refines"
      preservingRelation := some (fieldName family name "_action_rel_native_preserving") }
      else none }
  modify fun state => { state with current := some current, currentRecursive := false }
  let ⟨raw, native, calls, returned, normal⟩ ←
    sequence names imports result scope elements .immutable true
  let recursive := (← get).currentRecursive
  let fn : Function := {
    name := name
    parameters := parsed
    result := result
    rawBody := ← doTerm raw
    model? := ← if hints.partialFixpoint?.isSome || normal.isSome then pure none else
      mapModelsM ((·, ·) <$> native <*> calls) returned fun (native, calls) returned => do
        return {
          nativeBody := ← doTerm native, calls, returned, termination, recursive } }
  if fn.model?.isNone && hints.isNotNone then
    logWarningAt name "this source function has no generated total mathematical model; \
      its termination or fixed-point hints were not checked, and source termination still requires a contract"
  modify fun state => { state with
    functions := state.functions.push fn
    current := none
    currentRecursive := false }

/-- Model dependencies follow the prepared trace, including the mathematical
body attached to an actual range. Unreachable source statements are not model
dependencies. -/
private partial def modelDependencies (ranges : Array RangeRegistration)
    (trace : Array Trace) : List Name :=
  trace.toList.flatMap fun instruction => match instruction with
    | .call invocation => invocation.operation.modelDependency?.toList
    | .conditional _ yes no _ _ _ =>
        modelDependencies ranges yes ++ modelDependencies ranges no
    | .optionMatch _ _ absent present _ _ _ =>
        modelDependencies ranges absent ++ modelDependencies ranges present
    | .range tag _ _ _ =>
        match ranges.find? (fun range => range.tag == tag) with
        | some range => modelDependencies ranges range.body
        | none => []

/-- Replace pending local calls by their completed mathematical interfaces.
This traverses proof data only: source bodies, operation families, and loop
sites were already prepared once in their original declaration order. -/
private partial def resolveModelTrace (names : DeclarationNames) (current : Name)
    (completed : Array Function) (ranges : Array RangeRegistration) (trace : Array Trace) :
    TermElabM (Option (Array Trace) × Array RangeRegistration) := do
  let mut resolved : Array Trace := #[]
  let mut ranges := ranges
  for instruction in trace do
    match instruction with
    | .call invocation =>
        let operation : Operation ← match invocation.operation.modelDependency? with
          | none => pure invocation.operation
          | some dependency =>
              if dependency == current then
                -- Only the existing explicitly requested recursive model can
                -- reach this branch; SCC membership supplies no termination.
                pure { invocation.operation with modelDependency? := none }
              else do
                let some callee := completed.find? (fun fn => fn.name.getId == dependency)
                  | throwError "a local mathematical dependency was not completed before its caller"
                pure (functionOperation names callee)
        if operation.model?.isNone then return (none, ranges)
        resolved := resolved.push (.call { invocation with operation })
    | .conditional condition yes no yesResult noResult result =>
        let (yes, updated) ← resolveModelTrace names current completed ranges yes
        ranges := updated
        let (no, updated) ← resolveModelTrace names current completed ranges no
        ranges := updated
        let some yes := yes | return (none, ranges)
        let some no := no | return (none, ranges)
        resolved := resolved.push (.conditional condition yes no yesResult noResult result)
    | .optionMatch discriminant payload absent present noneResult someResult result =>
        let (absent, updated) ← resolveModelTrace names current completed ranges absent
        ranges := updated
        let (present, updated) ← resolveModelTrace names current completed ranges present
        ranges := updated
        let some absent := absent | return (none, ranges)
        let some present := present | return (none, ranges)
        resolved := resolved.push
          (.optionMatch discriminant payload absent present noneResult someResult result)
    | .range tag arguments result _ =>
        let some range := ranges.find? (fun range => range.tag == tag)
          | throwError "a mathematical range dependency has no prepared source site"
        let (body, updated) ← resolveModelTrace names current completed ranges range.body
        ranges := updated
        let some body := body | return (none, ranges)
        ranges := ranges.map fun candidate =>
          if candidate.tag == tag then { candidate with body } else candidate
        resolved := resolved.push (.range tag arguments result (body.all Trace.preservesArrays))
  return (some resolved, ranges)

private partial def modelRangeTags (ranges : Array RangeRegistration)
    (trace : Array Trace) : List Name :=
  trace.toList.flatMap fun instruction => match instruction with
    | .call _ => []
    | .conditional _ yes no _ _ _ => modelRangeTags ranges yes ++ modelRangeTags ranges no
    | .optionMatch _ _ absent present _ _ _ =>
        modelRangeTags ranges absent ++ modelRangeTags ranges present
    | .range tag _ _ _ =>
        tag :: match ranges.find? (fun range => range.tag == tag) with
          | some range => modelRangeTags ranges range.body
          | none => []

/-- Complete only mathematical candidates in callee-first order. The returned
source preparation retains its original function and operation order. A missing
callee model or a mutual cycle removes dependent candidates, not valid source.
Actual correspondence failures still report ordinary elaboration errors. -/
def completeModels (names : DeclarationNames) (prepared : Preparation) :
    TermElabM (Preparation × Array Name) := do
  let vertices := prepared.functions.toList.map (·.name.getId)
  let components := Lean.SCC.scc vertices fun name =>
    match prepared.functions.find? (fun fn => fn.name.getId == name) with
    | some fn =>
        (fn.model?.map (fun model => modelDependencies prepared.ranges model.calls) |>.getD []).filter
          (fun dependency => vertices.contains dependency)
    | none => []
  let mut completed : Array Function := #[]
  let mut ranges := prepared.ranges
  for component in components do
    for name in component do
      let some fn := prepared.functions.find? (fun fn => fn.name.getId == name)
        | throwError "a mathematical dependency does not belong to the prepared source family"
      let (model?, updated) ← match component, fn.model? with
        | [_], some model => do
            let (calls, updated) ← resolveModelTrace names name completed ranges model.calls
            pure (calls.map (fun calls => { model with calls }), updated)
        | _, _ => pure (none, ranges)
      ranges := updated
      if let some candidate := fn.model? then
        if model?.isNone then
          let hints ← Lean.Elab.elabTerminationHints candidate.termination
          if hints.isNotNone then
            logWarningAt fn.name "this source function has no generated total mathematical model; \
              its termination hints were not checked, and source termination still requires a contract"
      completed := completed.push { fn with model? }
  let functions ← prepared.functions.mapM fun fn => do
    let some resolved := completed.find? (fun resolved => resolved.name.getId == fn.name.getId)
      | throwError "the source function is missing its mathematical dependency result"
    pure resolved
  -- Local while observations are independent of a whole-function model. Resolve
  -- their calls only after all function interfaces have been completed; in
  -- particular, a recursive while does not acquire an assumed recursive model.
  let mut whiles := #[]
  for loop in prepared.whiles do
    let (guard, updated) ← resolveModelTrace names Name.anonymous completed ranges loop.guard
    ranges := updated
    let (body, updated) ← resolveModelTrace names Name.anonymous completed ranges loop.body
    ranges := updated
    if let some guard := guard then
      if let some body := body then
        if guard.all Trace.preservesArrays && body.all Trace.preservesArrays then
          whiles := whiles.push { loop with guard, body }
  let retained := (functions.toList.flatMap fun fn =>
    fn.model?.map (fun model => modelRangeTags ranges model.calls) |>.getD []
    ) ++ whiles.toList.flatMap (fun loop =>
      modelRangeTags ranges loop.guard ++ modelRangeTags ranges loop.body)
  ranges := ranges.filter (fun range => retained.contains range.tag)
  -- Completion local types survive unchanged: they do not depend on resolved
  -- pure calls or array-preserving round traces.
  return ({ prepared with functions, ranges, whiles },
    completed.filterMap fun fn => fn.model?.map (fun _ => fn.name.getId))

end Internal

end Complexity.Language.Syntax.Represented
