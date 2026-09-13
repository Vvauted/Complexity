/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Syntax.Native
import Lean.Elab.Command
import Lean.EnvExtension

/-!
# Source program headers for frontend imports

The named frontend records public function headers after elaborating their
source program. Lean's persistent environment extension carries these headers
across module imports. The key is the resolved `family.program` declaration,
so ordinary namespace and open-name resolution determine the imported family.
Structured headers retain the core's recursive product and option types,
including borrowed buffers inside them; they require no separate import encoding.
There is one registry for raw declarations and declarations with mathematical
views. A mathematical signature does not imply a total mathematical model:
source identities, represented types and checked model theorems are separate.

This metadata routes named calls; it contains no implementation, execution
assumption or cost annotation. Actual source bodies and their embedding proofs
remain declarations checked by Lean. The headers do not enumerate every entry
of an extended program's table: imported bodies can occupy other entries.
-/

namespace Complexity.Language.Syntax

open Lean Meta Elab Command

/-- The original emitted source entry and its proof-facing action. These names
do not select a replacement implementation or a mathematical evaluator. -/
structure SourceFunctionInfo where
  family : Name
  name : Name
  action : Name

/-- A closed mathematical type and its checked observation of a source value.
This metadata contains no reconstruction of a heap-backed value. -/
structure FunctionTypeInfo where
  nativeType : Expr
  coreTy : Ty
  representation : Expr

/-- Mathematical parameter and result observations, independent of whether a
total mathematical function has been supplied or proved. -/
structure MathematicalFunctionInfo where
  params : Array (Name × FunctionTypeInfo)
  result : FunctionTypeInfo

/-- Names of an existing mathematical model and its checked source theorems.
Different proof interfaces may provide an equation, a relational observation,
a refinement or a total source contract. Missing theorems are not inferred. -/
structure FunctionModelInfo where
  name : Name
  equation : Option Name := none
  relation : Option Name := none
  refinement : Option Name := none
  preservingRelation : Option Name := none
  total : Option Name := none

/-- A named source function's public header, without its implementation.
`name` is its local declaration name within the source family; parameter names
are retained for generated ordinary-argument proof interfaces. -/
structure FunctionInfo where
  name : Name
  params : Array (Name × Ty)
  result : Ty
  /-- The public value function has a checked pure source correspondence.
  Its actual source observation has the explicit `_action` suffix. -/
  pure : Bool := false
  /-- The independently checked native header, when a represented pure family
  uses registered structures rather than the core's native value types. -/
  nativeHeader : Option NativeHeader := none
  /-- Filled at registration with the original source identity. -/
  source? : Option SourceFunctionInfo := none
  /-- A mathematical signature is also available to contract-only declarations. -/
  mathematical? : Option MathematicalFunctionInfo := none
  /-- Optional checked model proofs; this is not a source-language mode. -/
  model? : Option FunctionModelInfo := none

private initialize programInfoExt :
    SimplePersistentEnvExtension (Name × Array FunctionInfo) (NameMap (Array FunctionInfo)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
  }

private def resolveProgramName (family : TSyntax `ident) : CommandElabM Name :=
  resolveGlobalConstNoOverload (mkIdentFrom family (family.getId ++ `program))

private def checkTypeInfo (type : FunctionTypeInfo) (expected : Ty) : TermElabM Unit := do
  unless type.coreTy == expected do
    throwError "a mathematical header has a different source layout"
  for expression in #[type.nativeType, type.representation] do
    if expression.hasFVar || expression.hasMVar then
      throwError "source header type and representation expressions must be closed"

private def pureTypeInfo (type : PureType) : FunctionTypeInfo :=
  ⟨type.nativeType, type.coreTy, type.representation⟩

private def pureMathematicalInfo (function : FunctionInfo) : TermElabM MathematicalFunctionInfo := do
  match function.nativeHeader with
  | some header =>
      return {
        params := header.params.map (fun parameter => (parameter.name.getId, pureTypeInfo parameter.type))
        result := pureTypeInfo header.result }
  | none =>
      let params ← function.params.mapM fun (name, type) => do
        let resolved ← resolvePureType (mkApp (mkConst ``Value) (coreTypeExpr type))
        return (name, pureTypeInfo resolved)
      let result ← resolvePureType (mkApp (mkConst ``Value) (coreTypeExpr function.result))
      return { params, result := pureTypeInfo result }

private def completeFunctionInfo (family : Name) (function : FunctionInfo) :
    CommandElabM FunctionInfo := do
  let source := function.source?.getD {
    family, name := function.name
    action := (family ++ function.name).appendAfter (if function.pure then "_action" else "") }
  let mut function := { function with source? := some source }
  if function.pure then
    if function.mathematical?.isNone then
      let mathematical ← liftTermElabM (pureMathematicalInfo function)
      function := { function with mathematical? := some mathematical }
    if function.model?.isNone then
      let name := source.family ++ source.name
      function := { function with model? := some {
        name
        equation := some (name.appendAfter "_action_eq_pure")
        refinement := if function.nativeHeader.isSome then some (name.appendAfter "_refines") else none
        total := some (name.appendAfter "_total") } }
  if let some mathematical := function.mathematical? then
    unless mathematical.params.size == function.params.size do
      throwError "mathematical and source headers have different parameter counts"
    liftTermElabM do
      for (_, type) in mathematical.params, (_, expected) in function.params do
        checkTypeInfo type expected
      checkTypeInfo mathematical.result function.result
  if function.model?.isSome then
    unless function.mathematical?.isSome do
      throwError "a checked mathematical model requires a mathematical signature"
  return function

/-- Record the public local headers of an already elaborated source program.
The frontend calls this after elaborating all generated declarations. -/
def registerProgramInfo (family : TSyntax `ident) (functions : Array FunctionInfo) :
    CommandElabM Unit := do
  let programName ← resolveProgramName family
  let functions ← functions.mapM (completeFunctionInfo programName.getPrefix)
  if let some first := functions[0]? then
    unless functions.all (fun function =>
        function.source?.map (·.family) == first.source?.map (·.family)) do
      throwError "one source header family must refer to one actual program table"
  modifyEnv fun env => programInfoExt.addEntry env (programName, functions)

/-- Read already registered source headers by their resolved program constant.
This lookup adds no declarations and does not interpret an arbitrary Lean function. -/
def getProgramInfo? (env : Environment) (program : Name) : Option (Array FunctionInfo) :=
  (programInfoExt.getState env).find? program

/-- Resolve a public program name to its original source family and local
headers. A mathematical public alias retains the same actual source table;
an arbitrary Lean declaration is not a source import. -/
def getProgramInfo (family : TSyntax `ident) : CommandElabM (Name × Array FunctionInfo) := do
  let programName ← resolveProgramName family
  let some functions := getProgramInfo? (← getEnv) programName
    | throwErrorAt family "'{family.getId}' is not a registered source program"
  let sourceFamily := ((functions[0]?).bind (·.source?)).map (·.family)
  return (sourceFamily.getD programName.getPrefix, functions)

end Complexity.Language.Syntax
