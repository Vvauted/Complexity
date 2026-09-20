/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Preparation
import Complexity.Language.Syntax.Represented.OperationDeclarations
import Complexity.Language.Syntax.Represented.Declarations
import Complexity.Language.Syntax.Represented.ModelEquation
import Complexity.Language.Syntax.Represented.Correspondence.While
import Complexity.Language.Syntax.Represented.Correspondence.While.Completion

/-!
# Elaboration of represented source programs

Coordinate preparation, actual source emission, checked mathematical models
and registration. Default and native naming policies share this same entry
point and preserve the order and identities of actual source operations.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

private def emitDeclarations (declarations : Array Syntax) : CommandElabM Unit :=
  elabCommand (mkNullNode declarations)

private def readImports (libraries : Array (TSyntax `ident)) : CommandElabM ImportedPrograms :=
  readRepresentedImports libraries

private def registerNativeProgram (names : DeclarationNames) (functions : Array Function)
    (totals : Array Name) :
    CommandElabM Unit := do
  let family := names.publicFamily
  let rawFamily := names.sourceFamily
  let sourceProgramName ← resolveGlobalConstNoOverload (mkIdentFrom rawFamily (rawFamily.getId ++ `program))
  let typeInfo (type : NativeType) : FunctionTypeInfo := {
    nativeType := type.nativeType, coreTy := type.coreTy, representation := type.representation }
  let headers ← (functions.filter (·.exposed)).mapM fun fn => do
    let action ← resolveGlobalConstNoOverload (fieldName rawFamily fn.name)
    let model? : Option FunctionModelInfo ← match fn.model? with
      | none => pure none
      | some _ => do
          let name ← resolveGlobalConstNoOverload (modelName names fn.name)
          let relation ← resolveGlobalConstNoOverload (fieldName family fn.name "_action_rel_native")
          let refinement ← resolveGlobalConstNoOverload (fieldName family fn.name "_refines")
          let equation ← if fn.hasExactEquation then
              some <$> resolveGlobalConstNoOverload (fieldName family fn.name "_action_eq_native")
            else pure none
          let preservingRelation ← if fn.preservesArrays then
              some <$> resolveGlobalConstNoOverload
                (fieldName family fn.name "_action_rel_native_preserving")
            else pure none
          let total ← if totals.contains fn.name.getId then
              some <$> resolveGlobalConstNoOverload (fieldName family fn.name "_total")
            else pure none
          pure (some {
            name, equation, relation := some relation
            refinement := some refinement, preservingRelation, total })
    pure ({
      name := fn.name.getId
      params := fn.parameters.map (fun parameter => (parameter.name.getId, parameter.type.coreTy))
      result := fn.result.coreTy
      source? := some { family := sourceProgramName.getPrefix, name := fn.name.getId, action }
      mathematical? := some {
        params := fn.parameters.map (fun parameter => (parameter.name.getId, typeInfo parameter.type))
        result := typeInfo fn.result }
      model? } : FunctionInfo)
  registerProgramInfo family headers

end Internal

open Internal


/-- Elaborate one prepared source program and its optional checked mathematical
view. Naming policies do not select another preparer, evaluator or compiler. -/
def elaborateWithNames (names : DeclarationNames) (libraries : Array (TSyntax `ident))
    (functions : Array (TSyntax `sourceFunction)) : CommandElabM Unit := do
  let family := names.publicFamily
  let imports ← readImports libraries
  let (prepared, modelOrder) ← liftTermElabM do
    let declarations ← functions.mapM fun declaration => liftMacroM (parseDeclaration declaration)
    let mut initial : Preparation := {}
    for declaration in declarations do
      if initial.localHeaders.any (fun header => header.name.getId == declaration.name.getId) then
        throwErrorAt declaration.name "duplicate source function"
      let parameters ← declaration.params.mapM fun parameter => do
        return (parameter.name.getId, ← resolveType parameter.type)
      let header : LocalHeader := {
        name := declaration.name, parameters, result := ← resolveType declaration.result }
      initial := { initial with
        localHeaders := initial.localHeaders.push header }
    let (_, state) ← (declarations.forM (prepareFunction names imports)).run initial
    completeModels names state
  for registration in prepared.folds do
    emitDeclarations (← liftTermElabM (foldDeclarations registration))
    registerProgramInfo registration.operation.family #[{
      name := `fold
      params := #[(`initial, registration.callback.accumulator.coreTy),
        (`root, .option (.node registration.callback.kind))]
      result := registration.callback.accumulator.coreTy }]
  for registration in prepared.constructors do
    emitDeclarations (← liftTermElabM (consDeclarations registration))
    registerProgramInfo registration.operation.family #[{
      name := `cons
      params := #[(`head, registration.kind.toTy), (`tail, .option (.node registration.kind))]
      result := .option (.node registration.kind) }]
  for registration in prepared.deconstructors do
    emitDeclarations (← liftTermElabM (unconsDeclarations registration))
    registerProgramInfo registration.operation.family #[{
      name := `uncons
      params := #[(`root, .option (.node registration.kind))]
      result := .option (.prod registration.kind.toTy (.option (.node registration.kind))) }]
  for registration in prepared.emptinessTests do
    emitDeclarations (← liftTermElabM (isEmptyDeclarations registration))
    registerProgramInfo registration.operation.family #[{
      name := `isEmpty
      params := #[(`root, .option (.node registration.kind))]
      result := .bool }]
  let rawFunctions ← liftTermElabM (prepared.functions.mapM rawFunction)
  let rawFamily := names.sourceFamily
  let operationFamilies := prepared.folds.map (·.operation.family) ++
    prepared.constructors.map (·.operation.family) ++ prepared.deconstructors.map (·.operation.family) ++
    prepared.emptinessTests.map (·.operation.family) ++ prepared.calledFamilies
  let actualSites ← Complexity.Language.Syntax.elaborateSourceProgramWithBlockSites
    rawFamily rawFunctions libraries false operationFamilies
  let ranges ← prepared.ranges.mapM fun range => do
    let some site := actualSites.ranges.find? (fun site => site.tag == range.tag)
      | throwError "the source emitter did not return the prepared range site"
    pure { range with site? := some site }
  let completionWhiles ← prepared.completionWhiles.mapM fun loop => do
    let some site := actualSites.whiles.find? (fun site => site.tag == loop.tag)
      | throwError "the source emitter did not return the prepared completion while site"
    pure { loop with site? := some site }
  let prepared := { prepared with completionWhiles }
  let signatures := mkIdentFrom family (family.getId ++ `signatures)
  let program := mkIdentFrom family (family.getId ++ `program)
  let rawSignatures := mkIdentFrom family (rawFamily.getId ++ `signatures)
  let rawProgram := mkIdentFrom family (rawFamily.getId ++ `program)
  if family.getId != rawFamily.getId then
    emitDeclarations #[
      (← `(command| abbrev $signatures:ident := $rawSignatures:ident)).raw,
      (← `(command| def $program:ident : Complexity.Language.Program $signatures:ident := $rawProgram:ident)).raw]
  for fn in prepared.functions do
    if fn.exposed then emitDeclarations (← liftTermElabM (interfaceDeclarations names fn))
    if fn.model?.isNone && fn.exposed && family.getId != rawFamily.getId then
      let name := fieldName family fn.name
      let action := fieldName rawFamily fn.name
      elabCommand (← `(command|
        /-- The same source action, without an asserted total mathematical model. -/
        noncomputable abbrev $name:ident := $action:ident))
  let mut totals := #[]
  for name in modelOrder do
    let some fn := prepared.functions.find? (fun fn => fn.name.getId == name)
      | throwError "the completed mathematical function has no actual source declaration"
    let some model := fn.model?
      | throwError "a source-only function entered mathematical declaration emission"
    elabCommand (← liftTermElabM (nativeDeclaration names fn model))
    if let some equation ← liftTermElabM (modelEquationDeclaration? names fn model ranges) then
      elabCommand equation
      let equationName ← resolveGlobalConstNoOverload
        (fieldName names.publicFamily fn.name "_model_eq")
      addDocStringCore equationName
        "A mathematical model equation simplifying completion-range state maps through pure branches."
    if fn.hasExactEquation then
      elabCommand (← liftTermElabM (equationDeclaration names fn model))
      if let some declaration ← liftTermElabM (totalDeclaration? names fn) then
        elabCommand declaration
        totals := totals.push fn.name.getId
    if fn.preservesArrays then
      elabCommand (← liftTermElabM (relationDeclaration names fn model true ranges))
    elabCommand (← liftTermElabM (relationDeclaration names fn model false ranges))
    if fn.exposed then elabCommand (← liftTermElabM (refinementDeclaration names fn))
  for loop in prepared.whiles do
    let some site := actualSites.whiles.find? (fun site => site.tag == loop.tag)
      | throwError "the source emitter did not return the prepared while site"
    emitDeclarations (← liftTermElabM (whileDeclarations { loop with site? := some site } ranges))
  for loop in prepared.completionWhiles do
    emitDeclarations (← liftTermElabM (completionWhileDeclarations loop))
  registerNativeProgram names prepared.functions totals

/-- Prepare one actual source program and optional mathematical functions.
Normal finite ranges have a fold view; early exits and general while retain
their actual source control and are proved using state contracts. -/
syntax (name := nativeSourceProgram) "source_program " "(" &"native" ") " ident " where" ppLine
  many1Indent(sourceFunction) : command

/-- Import completed native operation families or verified pure source callbacks.
Native callbacks retain their actual source identities and heap-indexed relations. -/
syntax (name := importingNativeSourceProgram)
  "source_program " "(" &"native" ") " ident " importing " ident,+ " where" ppLine
  many1Indent(sourceFunction) : command

elab_rules : command
  | `(command| source_program $family:ident where $functions:sourceFunction*) =>
      elaborateWithNames (.source family) #[] functions
  | `(command| source_program $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => elaborateWithNames (.source family) libraries.getElems functions
  | `(command| source_program (native) $family:ident where $functions:sourceFunction*) =>
      elaborateWithNames (.native family) #[] functions
  | `(command| source_program (native) $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => elaborateWithNames (.native family) libraries.getElems functions

end Complexity.Language.Syntax.Represented
