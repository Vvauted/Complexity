/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation
import Lean.Elab.Command
import Lean.EnvExtension
import Lean.Meta.AppBuilder
import Lean.Structure

/-!
# Registered native types for the source frontend

`source_type Point` derives a pure encoding for an ordinary structure with
nondependent fields. The fields may be scalars, products, options, or previously
registered structures. The generated declarations include the encoding, its
injectivity proof, a `Representation`, and constructor/projection equations.
Persistent metadata exposes these checked declarations to the source elaborator.

Native types and core types remain separate: equal layouts do not identify two
different structures. The encoding is a proof-side transport, not a new core
operation. A frontend must lower a registered constructor or projection to the
existing pair/projection operations and use the registered equations.

This command handles structures without parameters, indices, inherited fields,
or dependent fields. It does not encode buffers or node references, allocate
containers, or register arbitrary native function calls. Unsupported fields are
rejected before any declaration or registration is emitted.
-/

namespace Complexity.Language.Syntax

open Lean Meta Elab Command

/-- A checked native type and its pure representation in the existing core.
The expressions are elaborated terms, not untrusted names or source text.
`nativeType` remains the type used for nominal frontend type checking. -/
structure PureType where
  nativeType : Expr
  coreTy : Ty
  embedding : Expr
  encoding : Expr
  injective : Expr
  representation : Expr
  /-- `∀ a value heap, representation.Rel a value heap ↔ encoding a = value`. -/
  relationEq : Expr

/-- One direct native field, in the original constructor's field order.
The core projection is `tupleProjection fieldCount index`; its equation is
checked when the structure is registered. -/
structure SourceFieldInfo where
  name : Name
  projection : Name
  binderInfo : BinderInfo
  type : PureType
  index : Nat
  equation : Name

/-- Metadata for an already checked `source_type` declaration.
The original constructor and projection names retain their Lean namespaces. -/
structure StructureTypeInfo where
  name : Name
  type : PureType
  constructor : Name
  fields : Array SourceFieldInfo
  constructorEquation : Name

private initialize structureTypeExt :
    SimplePersistentEnvExtension StructureTypeInfo (NameMap StructureTypeInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state info => state.insert info.name info
    addImportedFn := mkStateFromImportedEntries (fun state info => state.insert info.name info) {}
  }

/-- Retrieve a registered structure by its resolved, fully qualified native name. -/
def getStructureTypeInfo? (env : Environment) (name : Name) : Option StructureTypeInfo :=
  (structureTypeExt.getState env).find? name

/-- Resolve a native constructor to its registered structure, including
structures whose constructor is not named `mk`. -/
def getStructureConstructorInfo? (env : Environment) (name : Name) : Option StructureTypeInfo := do
  let .ctorInfo constructor ← env.find? name | none
  let info ← getStructureTypeInfo? env constructor.induct
  if info.constructor == name then some info else none

/-- Find a registered direct projection using the receiver's nominal type,
not merely the shape of its core product. -/
def getStructureSourceField? (env : Environment) (nativeName field : Name) :
    Option SourceFieldInfo := do
  let info ← getStructureTypeInfo? env nativeName
  info.fields.find? fun entry => entry.name == field || entry.projection == field

/-- Quote the existing core type without changing its native interpretation. -/
def coreTypeExpr : Ty → Expr
  | .nat => mkConst ``Ty.nat
  | .bool => mkConst ``Ty.bool
  | .unit => mkConst ``Ty.unit
  | .buffer kind => mkApp (mkConst ``Ty.buffer) (match kind with
      | .nat => mkConst ``CellTy.nat
      | .bool => mkConst ``CellTy.bool)
  | .node kind => mkApp (mkConst ``Ty.node) (match kind with
      | .nat => mkConst ``CellTy.nat
      | .bool => mkConst ``CellTy.bool)
  | .prod left right => mkApp2 (mkConst ``Ty.prod) (coreTypeExpr left) (coreTypeExpr right)
  | .option value => mkApp (mkConst ``Ty.option) (coreTypeExpr value)

private def checkedPureType (nativeType : Expr) (coreTy : Ty) (embedding : Expr) :
    MetaM PureType := do
  let coreValueType := mkApp (mkConst ``Value) (coreTypeExpr coreTy)
  let expected ← mkAppM ``Function.Embedding #[nativeType, coreValueType]
  unless ← isDefEq (← inferType embedding) expected do
    throwError "source encoding has the wrong native type or core layout"
  let encoding ← mkAppM ``Function.Embedding.toFun #[embedding]
  let injective ← mkAppM ``Function.Embedding.injective #[embedding]
  let representation ← mkAppOptM ``Representation.ofEmbedding
    #[some nativeType, some (coreTypeExpr coreTy), some embedding]
  let relationEq ← withLocalDeclD `a nativeType fun a =>
    withLocalDeclD `value coreValueType fun value =>
      withLocalDeclD `heap (mkConst ``Heap) fun heap => do
        let proof ← mkAppOptM ``Representation.ofEmbedding_rel
          #[some nativeType, some (coreTypeExpr coreTy), some embedding,
            some a, some value, some heap]
        mkLambdaFVars #[a, value, heap] proof
  return {
    nativeType := ← instantiateMVars nativeType
    coreTy := coreTy
    embedding := ← instantiateMVars embedding
    encoding := ← instantiateMVars encoding
    injective := ← instantiateMVars injective
    representation := ← instantiateMVars representation
    relationEq := ← instantiateMVars relationEq
  }

private partial def resolvePureType? (nativeType : Expr) : MetaM (Option PureType) := do
  let nativeType ← instantiateMVars nativeType
  if let .const name _ := nativeType then
    if let some info := getStructureTypeInfo? (← getEnv) name then
      return some { info.type with nativeType }
  for (name, coreTy) in [(``Nat, Ty.nat), (``Bool, Ty.bool), (``Unit, Ty.unit)] do
    if ← isDefEq nativeType (mkConst name) then
      let embedding ← mkAppM ``Function.Embedding.refl #[nativeType]
      return some (← checkedPureType nativeType coreTy embedding)
  let reduced ← whnf nativeType
  match reduced with
  | .app (.app (.const ``Prod _) left) right =>
      let some left ← resolvePureType? left | return none
      let some right ← resolvePureType? right | return none
      let embedding ← mkAppM ``Function.Embedding.prodMap #[left.embedding, right.embedding]
      return some (← checkedPureType nativeType (.prod left.coreTy right.coreTy) embedding)
  | .app (.const ``Option _) value =>
      let some value ← resolvePureType? value | return none
      let embedding ← mkAppM ``Function.Embedding.optionMap #[value.embedding]
      return some (← checkedPureType nativeType (.option value.coreTy) embedding)
  | .const name _ =>
      if let some info := getStructureTypeInfo? (← getEnv) name then
        return some { info.type with nativeType }
      return none
  | _ => return none

/-- Resolve a native type to a checked pure representation. This does not
identify native types merely because their `coreTy` fields agree. -/
def resolvePureType (nativeType : Expr) : MetaM PureType := do
  if nativeType.hasMVar then
    throwError "a source type must be fully inferred before resolving its encoding"
  let some result ← resolvePureType? nativeType
    | throwError "no registered pure source encoding for {nativeType}"
  return result

/-- Elaborate a source type in its current Lean namespace and local telescope,
then resolve its pure encoding. Callers retain `nativeType` for type checking. -/
def elabPureType (typeSyntax : TSyntax `term) : TermElabM PureType := do
  let nativeType ← Term.elabType typeSyntax
  Term.synthesizeSyntheticMVarsNoPostponing
  resolvePureType (← instantiateMVars nativeType)

/-- Native type compatibility, independent of whether runtime layouts agree. -/
def PureType.isDefEq (left right : PureType) : MetaM Bool :=
  Meta.isDefEq left.nativeType right.nativeType

/-- The minimal right-nested product layout for a structure's fields. -/
def fieldsCoreType : List Ty → Ty
  | [] => .unit
  | [field] => field
  | field :: rest => .prod field (fieldsCoreType rest)

private def fieldsValue : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit.unit)
  | [field] => pure field
  | field :: rest => do mkAppM ``Prod.mk #[field, ← fieldsValue rest]

/-- The actual nested-product projection used for a registered field.
No extra tail `Unit` or projection exists for a single-field structure. -/
def tupleProjection (fieldCount index : Nat) (value : Expr) : MetaM Expr := do
  unless index < fieldCount do
    throwError "source structure field index {index} is outside {fieldCount} fields"
  let mut projected := value
  for _ in [:index] do
    projected ← mkAppM ``Prod.snd #[projected]
  if index + 1 < fieldCount then
    mkAppM ``Prod.fst #[projected]
  else
    return projected

private def checkClosed (type value : Expr) : MetaM Unit := do
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar then
    throwError "a registered source type must have closed, fully elaborated declarations"
  unless ← isDefEq (← inferType value) type do
    throwError "generated source type declaration does not have its stated type"

private def addDefinition (name : Name) (type value : Expr) (doc : String) : TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  checkClosed type value
  withOptions (Elab.async.set · false) do
    addAndCompile (.defnDecl {
      name := name, levelParams := [], type := type, value := value
      hints := .abbrev, safety := .safe
    })
    enableRealizationsForConst name
  addDocStringCore name doc

private def addTheorem (name : Name) (type value : Expr) (doc : String) : TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  checkClosed type value
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := type, value := value })
    enableRealizationsForConst name
  addDocStringCore name doc

private def deriveStructureType (name : Name) : TermElabM StructureTypeInfo := do
  let env ← getEnv
  if (getStructureTypeInfo? env name).isSome then
    throwError "source type '{name}' is already registered"
  let some info := getStructureInfo? env name
    | throwError "source_type expects an ordinary Lean structure"
  let inductInfo ← getConstInfoInduct name
  unless inductInfo.numParams == 0 && inductInfo.numIndices == 0 && inductInfo.levelParams.isEmpty do
    throwError "source_type currently requires a structure without parameters or indices"
  unless info.parentInfo.isEmpty do
    throwError "source_type currently requires direct fields, without an extends clause"
  let constructor := getStructureCtor env name
  let nativeType := mkConst name
  let fields ← forallTelescope constructor.type fun arguments result => do
    let mut fields : Array SourceFieldInfo := #[]
    unless ← isDefEq result nativeType do
      throwError "source constructor does not return the registered native type"
    unless arguments.size == info.fieldNames.size do
      throwError "source constructor fields do not match its structure metadata"
    for argument in arguments, fieldName in info.fieldNames, index in [:arguments.size] do
      let fieldType ← instantiateMVars (← inferType argument)
      if fieldType.hasFVar then
        throwError "source_type does not support dependent field '{fieldName}'"
      let fieldType ← resolvePureType fieldType
      let some field := getFieldInfo? env name fieldName
        | throwError "missing projection metadata for source field '{fieldName}'"
      fields := fields.push {
        name := fieldName, projection := field.projFn, binderInfo := field.binderInfo
        type := fieldType, index := index, equation := name ++ `sourceEncode ++ fieldName
      }
    return fields
  let coreTy := fieldsCoreType (fields.toList.map (·.type.coreTy))
  let coreValueType := mkApp (mkConst ``Value) (coreTypeExpr coreTy)
  let encodingName := name ++ `sourceEncode
  let injectiveName := name ++ `sourceEncode_injective
  let embeddingName := name ++ `sourceEmbedding
  let representationName := name ++ `sourceRepresentation
  let relationName := name ++ `sourceRepresentation_rel
  let constructorEquation := name ++ `sourceEncode_mk
  let names := #[encodingName, injectiveName, embeddingName, representationName,
    relationName, constructorEquation] ++ fields.map (·.equation)
  for declarationName in names do
    if env.contains declarationName then
      throwError "source_type would overwrite existing declaration '{declarationName}'"
  let encoding ← withLocalDeclD `value nativeType fun value => do
    let encoded ← fields.toList.mapM fun field => do
      let projected ← mkAppM field.projection #[value]
      return mkApp field.type.encoding projected
    mkLambdaFVars #[value] (← fieldsValue encoded)
  let encodingType ← mkArrow nativeType coreValueType
  addDefinition encodingName encodingType encoding
    "The derived pure source encoding of this native structure; not a runtime conversion."
  let encoding := mkConst encodingName
  let injective ← withLocalDeclD `left nativeType fun left =>
    withLocalDeclD `right nativeType fun right => do
      let sameType ← mkEq (mkApp encoding left) (mkApp encoding right)
      withLocalDeclD `same sameType fun same => do
        let mut result ← mkEqRefl (mkConst constructor.name)
        for field in fields do
          let projection ← withLocalDeclD `raw coreValueType fun raw => do
            mkLambdaFVars #[raw] (← tupleProjection fields.size field.index raw)
          let encodedSame ← mkCongrArg projection same
          let fieldSame ← mkAppM ``Function.Embedding.injective #[field.type.embedding, encodedSame]
          result ← mkCongr result fieldSame
        mkLambdaFVars #[left, right, same] result
  let injectiveType ← mkAppM ``Function.Injective #[encoding]
  addTheorem injectiveName injectiveType injective
    "The derived source encoding preserves the native structure's equality."
  let embedding ← mkAppM ``Function.Embedding.mk #[encoding, mkConst injectiveName]
  let embeddingType ← mkAppM ``Function.Embedding #[nativeType, coreValueType]
  addDefinition embeddingName embeddingType embedding
    "The checked injective native-to-core transport for this source type."
  let pureType ← checkedPureType nativeType coreTy (mkConst embeddingName)
  addDefinition representationName (← inferType pureType.representation) pureType.representation
    "The mathematical representation installed by source_type."
  addTheorem relationName (← inferType pureType.relationEq) pureType.relationEq
    "The registered representation is exactly equality with the derived pure encoding."
  let constructorProof ← forallTelescope constructor.type fun arguments _ => do
    let constructed := mkAppN (mkConst constructor.name) arguments
    mkLambdaFVars arguments (← mkEqRefl (mkApp encoding constructed))
  -- State the constructor equation with the actual field encodings on its RHS.
  let constructorType ← forallTelescope constructor.type fun arguments _ => do
    let encoded := (fields.zip arguments).toList.map fun (field, argument) =>
      mkApp field.type.encoding argument
    let equation ← mkEq (mkApp encoding (mkAppN (mkConst constructor.name) arguments))
      (← fieldsValue encoded)
    mkForallFVars arguments equation
  addTheorem constructorEquation constructorType constructorProof
    "Constructing the native structure commutes with the registered core-field encoding."
  for field in fields do
    let (type, proof) ← withLocalDeclD `value nativeType fun value => do
      let lhs := mkApp field.type.encoding (← mkAppM field.projection #[value])
      let rhs ← tupleProjection fields.size field.index (mkApp encoding value)
      let type ← mkForallFVars #[value] (← mkEq lhs rhs)
      let proof ← mkLambdaFVars #[value] (← mkEqRefl lhs)
      return (type, proof)
    addTheorem field.equation type proof
      "Projecting this native field commutes with the actual core product projection."
  return {
    name := name
    type := { pureType with
      encoding := encoding, injective := mkConst injectiveName
      representation := mkConst representationName, relationEq := mkConst relationName }
    constructor := constructor.name
    fields := fields
    constructorEquation := constructorEquation
  }

/-- Register the derived pure representation and constructor/projection rules
of an existing ordinary structure for use by the source frontend. -/
syntax (name := sourceType) "source_type " ident : command

elab_rules : command
  | `(command| source_type $type:ident) => do
      let name ← resolveGlobalConstNoOverload type
      let info ← liftTermElabM (deriveStructureType name)
      modifyEnv fun env => structureTypeExt.addEntry env info

end Complexity.Language.Syntax
