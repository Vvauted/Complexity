/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Emission
import Lean.Elab.PreDefinition.TerminationHint
import Lean.PrettyPrinter.Delaborator

/-!
# Shared source-program elaboration entry points

Prepares optional native structure views, invokes the ordered source emitter, elaborates its
commands and registers only checked program/coordinate metadata. Public entry points remain in
`Complexity.Language.Syntax`; internal preparation helpers live in `Core`.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

private def nativeExprSyntax (value : Lean.Expr) : Lean.Elab.Term.TermElabM (TSyntax `term) :=
  Lean.withOptions (fun options => options.setBool `pp.fullNames true) do
    Lean.PrettyPrinter.delab value

private def nativeView (header : NativeHeader) : Lean.Elab.Term.TermElabM NativeView := do
  let mut simplifications := #[``Function.Embedding.coe_refl, ``Function.Embedding.coe_prodMap,
    ``Prod.map, ``id, ``Equiv.refl_apply, ``Equiv.refl_symm,
    ``Equiv.toFun_as_coe, ``Equiv.invFun_as_coe]
  for parameter in header.params do
    simplifications := simplifications ++ (← registeredTypeNames parameter.type.nativeType)
  simplifications := simplifications ++ (← registeredTypeNames header.result.nativeType)
  return {
    header := header
    parameterTypes := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.nativeType)
    resultType := ← nativeExprSyntax header.result.nativeType
    parameterEncodings := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.encoding)
    parameterRebuilds := ← header.params.mapM (fun parameter => do
      let rebuild ← nativeExprSyntax (← nativeReconstruction parameter.type)
      let rawType ← Lean.Elab.liftMacroM (valueTypeTerm parameter.type.coreTy)
      let nativeType ← nativeExprSyntax parameter.type.nativeType
      `(($rebuild : $rawType → $nativeType)))
    resultEncoding := ← nativeExprSyntax header.result.encoding
    parameterEmbeddings := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.embedding)
    resultEmbedding := ← nativeExprSyntax header.result.embedding
    parameterEquivs := ← header.params.mapM (fun parameter => nativeEquivalence parameter.type)
    resultEquiv := ← nativeEquivalence header.result
    simplifications := simplifications.map mkCIdent
  }

private partial def mentionsRegisteredConstructor (stx : Syntax) :
    Lean.Elab.Term.TermElabM Bool := do
  if stx.isIdent then
    try
      let name ← Lean.resolveGlobalConstNoOverload stx
      if (getStructureConstructorInfo? (← Lean.getEnv) name).isSome then return true
    catch _ => pure ()
  for argument in stx.getArgs do
    if ← mentionsRegisteredConstructor argument then return true
  return false

private def prepareNativeSources (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) (imports : Array ImportedProgram) :
    Lean.Elab.Term.TermElabM (Array (TSyntax `sourceFunction) × Array NativeView) := do
  let mut headers : Array NativeHeader := #[]
  let mut needed := false
  for source in sources do
    let declaration ← Lean.Elab.liftMacroM (parseDeclaration source)
    let mut params : Array NativeParameter := #[]
    for parameter in declaration.params do
      let type ← elabPureType parameter.type
      needed := needed || !(← registeredTypeNames type.nativeType).isEmpty
      params := params.push { name := parameter.name, type := type }
    let result ← elabPureType declaration.result
    needed := needed || !(← registeredTypeNames result.nativeType).isEmpty
    needed := needed || (← mentionsRegisteredConstructor declaration.body.raw)
    headers := headers.push {
      name := declaration.name, params := params, result := result
      native := generatedName family declaration.name ""
    }
  for source in imports do
    needed := needed || source.functions.any (·.nativeHeader.isSome)
  unless needed do return (sources, #[])
  let mut callees := headers
  for source in imports do
    for fn in source.functions do
      unless fn.pure do continue
      let name := mkIdentFrom source.name (source.name.getId ++ fn.name)
      let native := mkCIdent (source.family ++ fn.name)
      let header : NativeHeader ← match fn.nativeHeader with
        | some header => pure { header with name := name, native := native }
        | none => do
            let params ← fn.params.mapM fun (param, type) => do
              return ({
                name := mkIdentFrom source.name param
                type := ← resolvePureType (Lean.mkApp (Lean.mkConst ``Value) (coreTypeExpr type)) } :
                NativeParameter)
            pure ({
              name := name
              params := params
              native := native
              result := ← resolvePureType (Lean.mkApp (Lean.mkConst ``Value) (coreTypeExpr fn.result)) } :
              NativeHeader)
      callees := callees.push header
  let mut lowered := #[]
  let mut views := #[]
  for source in sources, header in headers do
    let declaration ← Lean.Elab.liftMacroM (parseDeclaration source)
    let body ← lowerNativeBody callees header declaration.body
    let parameters ← header.params.mapM fun parameter => do
      let type ← Lean.Elab.liftMacroM (valueTypeTerm parameter.type.coreTy)
      pure ({ name := parameter.name, type } : ParsedParameter)
    let result ← Lean.Elab.liftMacroM (valueTypeTerm header.result.coreTy)
    lowered := lowered.push (← Lean.Elab.liftMacroM
      ({ declaration with params := parameters, result, body }.toSyntax))
    views := views.push (← nativeView header)
  return (lowered, views)

end Core

open Core

/-- Elaborate the shared typed source and return the actual sites requested by
proof-side range tags. Explicit imports retain their order and written names;
additional operation families are linked only when not already imported.
Names are resolved only after their source declarations have checked; no range
tag affects the emitted program or its instruction costs. -/
def elaborateSourceProgramWithSites (family : TSyntax `ident)
    (functions : Array (TSyntax `sourceFunction)) (libraries : Array (TSyntax `ident))
    (pureMode : Bool := false) (additionalLibraries : Array (TSyntax `ident) := #[]) :
    Lean.Elab.Command.CommandElabM (Array ActualRangeSite) := do
  let mut imports : Array ImportedProgram := #[]
  for library in libraries do
    let (name, functions) ← getProgramInfo library
    if imports.any (fun imported => imported.family == name) then
      Lean.throwErrorAt library "duplicate source program import"
    imports := imports.push ⟨library, name, functions⟩
  for library in additionalLibraries do
    let (name, functions) ← getProgramInfo library
    unless imports.any (fun imported => imported.family == name) do
      imports := imports.push ⟨library, name, functions⟩
  let (functions, nativeViews) ← if pureMode then
      Lean.Elab.Command.liftTermElabM (prepareNativeSources family functions imports)
    else pure (functions, #[])
  for source in functions do
    let fn ← Lean.Elab.liftMacroM (parseFunction source)
    let hints ← Lean.Elab.elabTerminationHints fn.termination
    if pureMode then
      if hints.partialFixpoint?.isSome then
        Lean.throwErrorAt fn.termination "pure source functions must terminate; partial fixed points are not supported"
    else if hints.isNotNone then
      Lean.throwErrorAt fn.termination "termination hints are checked by 'source_program (pure)'"
  let (declarations, information, coordinates, ranges) ←
    Lean.Elab.liftMacroM (programDeclarations family functions imports pureMode nativeViews)
  Lean.Elab.Command.elabCommand declarations
  registerProgramInfo family information
  registerLoopCoordinates coordinates
  ranges.mapM fun site => do
    let name ← Lean.resolveGlobalConstNoOverload (mkIdentFrom family site.name)
    return { site with name }

/-- Elaborate a family through the shared typed-source lowering and declaration
generator. Higher-level proof views call this entry directly: they do not
re-enter the public command elaborator or install another source semantics.
The optional pure view is checked against the same emitted source program. -/
def elaborateSourceProgram (family : TSyntax `ident)
    (functions : Array (TSyntax `sourceFunction)) (libraries : Array (TSyntax `ident))
    (pureMode : Bool := false) : Lean.Elab.Command.CommandElabM Unit := do
  discard <| elaborateSourceProgramWithSites family functions libraries pureMode

elab_rules : command
  | `(command| source_program% $family:ident where $functions:sourceFunction*) => do
      elaborateSourceProgram family functions #[]
  | `(command| source_program% $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => do
      elaborateSourceProgram family functions libraries.getElems
  | `(command| source_program (pure) $family:ident where $functions:sourceFunction*) => do
      elaborateSourceProgram family functions #[] true
  | `(command| source_program (pure) $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => do
      elaborateSourceProgram family functions libraries.getElems true

end Complexity.Language.Syntax
