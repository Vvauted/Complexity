/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Syntax.Represented.Types
import Complexity.Language.Buffer.Copy.Native
import Complexity.Language.Buffer.RepresentedCopy
import Complexity.Language.List.Fold.Native
import Complexity.Language.List.Cons.Native
import Complexity.Language.Representation.Preservation
import Complexity.Language.List.Uncons.Native
import Complexity.Language.List.IsEmpty.Native

/-!
# Native mathematical views of represented source operations

This opt-in frontend retains ordinary mathematical types alongside actual source
types. Heap-backed lists carry a relation, not an encoding or an equivalence.
Registered fold operations use the existing source traversal and its proved
callback contract; the native mathematical fold is never a runtime primitive.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

/-- Checked ordinary and source identities of a completed native declaration.
Heap-backed parameters retain their native types and relations; this metadata
does not mark the ordinary function as an effect-free source observation. -/
structure NativeFunctionInfo where
  sourceFamily : Name
  sourceName : Name
  nativeName : Name
  parameters : Array (Name × NativeType)
  result : NativeType
  equation : Option Name
  relation : Name
  refinement : Name
  /-- An optional stronger observation, proved to preserve all old array contents. -/
  preservingRelation : Option Name := none

private initialize nativeProgramInfoExt :
    SimplePersistentEnvExtension (Name × Array NativeFunctionInfo)
      (NameMap (Array NativeFunctionInfo)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
  }

/-- Retrieve completed native headers by the resolved public program name. -/
def getNativeProgramInfo? (env : Environment) (program : Name) : Option (Array NativeFunctionInfo) :=
  (nativeProgramInfoExt.getState env).find? program

private structure ImportedPrograms where
  source : Array (Name × Array FunctionInfo) := #[]
  native : Array NativeFunctionInfo := #[]

private structure Parameter where
  name : TSyntax `ident
  type : NativeType
  rawName : TSyntax `ident
  relationName : TSyntax `ident

private inductive Observation where
  | refl
  | named (name : Name)
  | nil (kind : CellTy)
  | pair (purePair : Bool) (left right : Observation)
  | projection (purePair : Bool) (first : Bool) (pair : Observation)
  | none (payload : NativeType)
  | some (payload : Observation)
  | binary (operation : TSyntax `term) (left right : Observation)

private structure RetainedObservation where
  name : Name
  type : NativeType
  proof : TSyntax `term

private structure Binding extends Parameter where
  model : TSyntax `term
  rawModel : TSyntax `term
  observation : Observation := .refl

private structure Callback where
  sourceFamily : Name
  sourceName : Name
  nativeName : Name
  accumulator : NativeType
  kind : CellTy
  relation : Option Name := none

/-- Both views and their checked source theorem name belong to one operation.
No instruction price or machine assumption is stored in frontend metadata. -/
private structure Operation where
  family : TSyntax `ident
  sourceName : Name
  native : TSyntax `term
  inputs : Array NativeType
  result : NativeType
  equation : Option (TSyntax `ident)
  relation : TSyntax `ident
  refinement : TSyntax `ident
  preservingRelation : Option (TSyntax `ident) := none

private structure FoldRegistration where
  callback : Callback
  operation : Operation

private structure ConsRegistration where
  kind : CellTy
  operation : Operation

private structure UnconsRegistration where
  kind : CellTy
  operation : Operation

private structure IsEmptyRegistration where
  kind : CellTy
  operation : Operation

private structure Value where
  type : NativeType
  raw : TSyntax `term
  native : TSyntax `term
  model : TSyntax `term
  rawModel : TSyntax `term
  observation : Observation := .refl

private structure Invocation where
  operation : Operation
  arguments : Array Value
  result : Binding

/-- Proof composition retains alternatives instead of treating both as executed calls. -/
private inductive Trace where
  | call (invocation : Invocation)
  | conditional (condition : Value) (yes no : Array Trace)
      (yesResult noResult : Value) (result : Binding)
  | optionMatch (discriminant : Value) (payload : Binding) (none some : Array Trace)
      (noneResult someResult : Value) (result : Binding)

private def lookup (scope : List Binding) (name : TSyntax `ident) : TermElabM Binding := do
  let some parameter := scope.find? (fun parameter => parameter.name.getId == name.getId)
    | throwErrorAt name "unknown native source variable '{name.getId}'"
  return parameter

private partial def fieldsTerm : List (TSyntax `term) → TermElabM (TSyntax `term)
  | [] => `(())
  | [field] => pure field
  | field :: rest => do `(($field, $(← fieldsTerm rest)))

private def fieldsObservation : List Observation → Observation
  | [] => .refl
  | [field] => field
  | field :: rest => .pair false field (fieldsObservation rest)

private def fieldProjection (count index : Nat) (receiver : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut result := receiver
  for _ in [:index] do result ← `(Prod.snd $result)
  if index + 1 < count then `(Prod.fst $result) else pure result

private def fieldObservation (count index : Nat) (receiver : Observation) : Observation := Id.run do
  let mut result := receiver
  for _ in [:index] do result := .projection false false result
  if index + 1 < count then return .projection false true result else return result

private partial def value (scope : List Binding) (stx : TSyntax `term)
    (expected : Option NativeType := none) :
    TermElabM Value := withRef stx do
  let binary (left right : TSyntax `term) (input output : TSyntax `term)
      (build : TSyntax `term → TSyntax `term → TermElabM (TSyntax `term)) := do
    let left ← value scope left
    let right ← value scope right
    let input ← resolveType input
    expect stx input left.type
    expect stx input right.type
    let first := mkIdent (← mkFreshUserName `left)
    let second := mkIdent (← mkFreshUserName `right)
    let operationBody ← build ⟨first.raw⟩ ⟨second.raw⟩
    let operation ← `(fun ($first:ident $second:ident : Nat) => $operationBody)
    return ({
      type := ← resolveType output, raw := ← build left.raw right.raw,
      native := ← build left.native right.native, model := ← build left.model right.model,
      rawModel := ← build left.rawModel right.rawModel,
      observation := .binary operation left.observation right.observation } : Value)
  let project (expression : TSyntax `term) (first : Bool) := do
    let pair ← value scope expression
    let (left, right) ← match pair.type with
      | .prod left right => pure (left, right)
      | .pure type => do
          let .prod _ _ := type.coreTy | throwError "projection requires a product"
          let native := type.nativeType.getAppArgs
          pure (← resolveNativeType native[0]!, ← resolveNativeType native[1]!)
      | _ => throwError "projection requires a product"
    let projection := if first then ``Prod.fst else ``Prod.snd
    let apply (term : TSyntax `term) := Lean.Syntax.mkCApp projection #[term]
    return ({
      type := if first then left else right,
      raw := apply pair.raw, native := apply pair.native,
      model := apply pair.model, rawModel := apply pair.rawModel,
      observation := .projection pair.type.isPure first pair.observation } : Value)
  let projectRecord (expression : TSyntax `term) (fieldName : Name) := do
    let record ← value scope expression
    let .record name _ _ := record.type
      | throwErrorAt expression "named field access requires a native record"
    let fields ← recordFields name
    let some index := fields.findIdx? (fun field =>
        field.name == fieldName || field.projection == fieldName)
      | throwError "unknown field '{fieldName}' of native record '{name}'"
    let some field := fields[index]?
      | throwError "native record field metadata has no entry at the selected index"
    return ({
      type := field.type
      raw := ← fieldProjection fields.size index record.raw
      rawModel := ← fieldProjection fields.size index record.rawModel
      native := Lean.Syntax.mkCApp field.projection #[record.native]
      model := Lean.Syntax.mkCApp field.projection #[record.model]
      observation := fieldObservation fields.size index record.observation } : Value)
  let constructRecord (type : NativeType) (arguments : Array (TSyntax `term)) := do
    let .record name _ _ := type | throwError "record construction requires a native record type"
    let fields ← recordFields name
    unless arguments.size == fields.size do throwError "wrong number of native record fields"
    let mut values := #[]
    for argument in arguments, field in fields do
      let fieldValue ← value scope argument (some field.type)
      expect argument field.type fieldValue.type
      values := values.push fieldValue
    let constructor := (getStructureCtor (← getEnv) name).name
    return ({
      type
      raw := ← fieldsTerm (values.map (·.raw)).toList
      rawModel := ← fieldsTerm (values.map (·.rawModel)).toList
      native := Lean.Syntax.mkCApp constructor (values.map (·.native))
      model := Lean.Syntax.mkCApp constructor (values.map (·.model))
      observation := fieldsObservation (values.map (·.observation)).toList } : Value)
  match stx with
  | `(($expression:term)) => value scope expression expected
  | `(($expression:term : $type:term)) =>
      let expected ← resolveType type
      if let .list kind := expected then
        if let `([]) := expression then
          return {
            type := expected, raw := ← `(none), native := stx,
            model := stx, rawModel := ← `(none), observation := .nil kind }
      if let .option payload := expected then
        if let `(none) := expression then
          return {
            type := expected, raw := ← `(none), native := stx,
            model := stx, rawModel := ← `(none), observation := .none payload }
      let result ← value scope expression (some expected)
      expect type expected result.type
      return result
  | `($name:ident) =>
      if name.getId == `true || name.getId == `false then
        return {
          type := ← resolveType (← `(Bool)), raw := stx, native := stx,
          model := stx, rawModel := stx }
      if let .str receiver field := name.getId then
        if scope.any (fun binding => binding.name.getId.isPrefixOf receiver) then
          return ← projectRecord ⟨(mkIdent receiver).raw⟩ (Name.mkSimple field)
      let parameter ← lookup scope name
      return {
        type := parameter.type, raw := stx, native := stx,
        model := parameter.model, rawModel := parameter.rawModel,
        observation := parameter.observation }
  | `($(pair).$field:fieldIdx) =>
      match field.raw.isFieldIdx? with
      | some 1 => project pair true
      | some 2 => project pair false
      | _ => throwError "a native product projection must select field 1 or 2"
  | `(Prod.fst $pair:term) => project pair true
  | `(Prod.snd $pair:term) => project pair false
  | `(($receiver:term).$field:ident) => projectRecord receiver field.getId
  | `({ $fields:structInstField,* }) =>
      let some expected := expected
        | throwError "a native record literal needs its declared result or binding type"
      let .record name _ _ := expected | throwError "expected a native record type"
      let metadata ← recordFields name
      let mut provided := #[]
      for field in fields.getElems do
        let `(structInstField| $name:ident := $expression:term) := field
          | throwErrorAt field "native record literals require direct named fields"
        if provided.any (fun (entry : Name × TSyntax `term) => entry.1 == name.getId) then
          throwErrorAt field "duplicate native record field"
        provided := provided.push (name.getId, expression)
      unless provided.size == metadata.size do throwError "provide every native record field exactly once"
      let arguments ← metadata.mapM fun field => do
        let some (_, expression) := provided.find? (fun entry => entry.1 == field.name)
          | throwError "missing native record field '{field.name}'"
        pure expression
      constructRecord expected arguments
  | `(some $expression:term) | `(Option.some $expression:term) =>
      let result ← value scope expression
      return {
        type := .option result.type, raw := ← `(some $(result.raw)),
        native := ← `(some $(result.native)), model := ← `(some $(result.model)),
        rawModel := ← `(some $(result.rawModel)), observation := .some result.observation }
  | `($_:num) => return {
      type := ← resolveType (← `(Nat)), raw := stx, native := stx,
      model := stx, rawModel := stx }
  | `(()) => return {
      type := ← resolveType (← `(Unit)), raw := stx, native := stx,
      model := stx, rawModel := stx }
  | `(($left, $right)) =>
      let left ← value scope left
      let right ← value scope right
      let type ← mkAppM ``Prod #[left.type.nativeType, right.type.nativeType]
      let type ← resolveNativeType type
      return {
        type,
        raw := ← `(($(left.raw), $(right.raw))), native := ← `(($(left.native), $(right.native))),
        model := ← `(($(left.model), $(right.model))),
        rawModel := ← `(($(left.rawModel), $(right.rawModel))),
        observation := .pair type.isPure left.observation right.observation }
  | `($left + $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a + $b)
  | `($left * $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a * $b)
  | `($left - $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a - $b)
  | `($left / $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a / $b)
  | `($left % $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a % $b)
  | `($called:ident $arguments:term*) =>
      let name ← resolveGlobalConstNoOverload called
      if let .ctorInfo constructor ← getConstInfo name then
        let type ← resolveNativeType (mkConst constructor.induct)
        return ← constructRecord type arguments
      if arguments.size == 1 then
        if let some _ := (← getEnv).getProjectionFnInfo? name then
          return ← projectRecord arguments[0]! name
      throwError "unsupported native call in a value; name source operations with `let`"
  | _ => throwError "unsupported native value expression; name source calls with `let ... ← ...`"

private structure Function where
  name : TSyntax `ident
  parameters : Array Parameter
  result : NativeType
  rawBody : TSyntax `term
  nativeBody : TSyntax `term
  calls : Array Trace
  returned : Value

private def Function.hasExactEquation (fn : Function) : Bool :=
  let scalarArguments := fn.parameters.all fun parameter =>
    match parameter.type with | .pure _ | .list _ => true | _ => false
  match fn.result with
  | .pure _ => scalarArguments && fn.calls.all fun
      | .call invocation => invocation.operation.equation.isSome
      | _ => false
  | _ => false

private partial def Trace.preservesArrays : Trace → Bool
  | .call invocation => invocation.operation.preservingRelation.isSome
  | .conditional _ yes no _ _ _ => yes.all Trace.preservesArrays && no.all Trace.preservesArrays
  | .optionMatch _ _ absent present _ _ _ =>
      absent.all Trace.preservesArrays && present.all Trace.preservesArrays

private def Function.preservesArrays (fn : Function) : Bool :=
  fn.hasExactEquation || fn.calls.all Trace.preservesArrays

private structure Preparation where
  folds : Array FoldRegistration := #[]
  constructors : Array ConsRegistration := #[]
  deconstructors : Array UnconsRegistration := #[]
  emptinessTests : Array IsEmptyRegistration := #[]
  functions : Array Function := #[]
  calledFamilies : Array (TSyntax `ident) := #[]

private abbrev PrepareM := StateT Preparation TermElabM

private def fieldName (family name : TSyntax `ident) (suffix : String := "") : TSyntax `ident :=
  mkIdentFrom name ((family.getId ++ name.getId).appendAfter suffix)

private def sourceFamily (family : TSyntax `ident) : TSyntax `ident :=
  mkIdentFrom family (family.getId ++ `Source)

private def functionOperation (family : TSyntax `ident) (fn : Function) : Operation := {
  family := sourceFamily family
  sourceName := fn.name.getId
  native := ⟨(fieldName family fn.name).raw⟩
  inputs := fn.parameters.map (·.type)
  result := fn.result
  equation := if fn.hasExactEquation then some (fieldName family fn.name "_action_eq_native") else none
  relation := fieldName family fn.name "_action_rel_native"
  refinement := fieldName family fn.name "_refines"
  preservingRelation := if fn.preservesArrays then
    some (fieldName family fn.name "_action_rel_native_preserving") else none }

private def importedOperation (info : NativeFunctionInfo) : Operation := {
  family := mkIdent info.sourceFamily
  sourceName := info.sourceName
  native := ⟨(mkCIdent info.nativeName).raw⟩
  inputs := info.parameters.map (·.2)
  result := info.result
  equation := info.equation.map mkCIdent
  relation := mkCIdent info.relation
  refinement := mkCIdent info.refinement
  preservingRelation := info.preservingRelation.map mkCIdent }

private def findImportedNative? (imports : ImportedPrograms) (name : TSyntax `ident) :
    TermElabM (Option NativeFunctionInfo) := do
  let resolved? ← try pure (some (← resolveGlobalConstNoOverload name)) catch _ => pure none
  let some resolved := resolved? | return none
  return imports.native.find? (fun info => info.nativeName == resolved)

private def findCallback (imports : ImportedPrograms)
    (name : TSyntax `ident) : TermElabM Callback := do
  let resolved ← resolveGlobalConstNoOverload name
  if let some info := imports.native.find? (fun info => info.nativeName == resolved) then
    unless info.parameters.size == 2 do
      throwErrorAt name "fold callbacks require an accumulator and a scalar head"
    let some (_, accumulator) := info.parameters[0]?
      | throwErrorAt name "fold callback has no accumulator parameter"
    let some (_, head) := info.parameters[1]?
      | throwErrorAt name "fold callback has no head parameter"
    expect name accumulator info.result
    let kind ← match head.coreTy with
      | .nat => pure CellTy.nat
      | .bool => pure CellTy.bool
      | _ => throwErrorAt name "fold callback heads must be Nat or Bool"
    return {
      sourceFamily := info.sourceFamily, sourceName := info.sourceName, nativeName := resolved,
      accumulator, kind, relation := some info.relation }
  for (family, functions) in imports.source do
    for info in functions do
      if family ++ info.name == resolved then
        unless info.pure do throwErrorAt name "fold requires a registered pure source callback"
        unless info.params.size == 2 do throwErrorAt name "fold callbacks require two ordinary parameters"
        let some (_, accTy) := info.params[0]?
          | throwErrorAt name "fold callback has no accumulator parameter"
        unless info.result == accTy do throwErrorAt name "fold callbacks must return their accumulator type"
        let some (_, headTy) := info.params[1]?
          | throwErrorAt name "fold callback has no head parameter"
        let kind ← match headTy with
          | .nat => pure CellTy.nat
          | .bool => pure CellTy.bool
          | _ => throwErrorAt name "fold callback heads must be Nat or Bool"
        let accumulator ← if let some header := info.nativeHeader then do
            let some parameter := header.params[0]?
              | throwErrorAt name "fold callback native metadata has no accumulator parameter"
            resolveType (← termOfExpr parameter.type.nativeType)
          else resolveType (← rawTypeTerm accTy)
        return {
          sourceFamily := family, sourceName := info.name, nativeName := resolved,
          accumulator, kind }
  throwErrorAt name "the callback must belong to an explicitly imported source program"

private def foldOperation (family : TSyntax `ident)
    (imports : ImportedPrograms) (name : TSyntax `ident) : PrepareM Operation := do
  let callback ← findCallback imports name
  if let some registered := (← get).folds.find? (fun registered =>
      registered.callback.nativeName == callback.nativeName) then
    return registered.operation
  let count := (← get).folds.size
  let operationFamily := mkIdentFrom name (family.getId ++ `Operations ++
    Name.mkSimple ("fold" ++ toString count))
  let native := Lean.Syntax.mkCApp ``List.foldl #[⟨(mkCIdent callback.nativeName).raw⟩]
  let operation : Operation := {
    family := operationFamily
    sourceName := `fold
    native
    inputs := #[callback.accumulator, .list callback.kind]
    result := callback.accumulator
    equation := if callback.relation.isNone then
      some (mkIdentFrom name (operationFamily.getId ++ `fold_eq)) else none
    relation := mkIdentFrom name (operationFamily.getId ++ `fold_rel)
    refinement := mkIdentFrom name (operationFamily.getId ++ `fold_refines) }
  modify fun state => { state with folds := state.folds.push ⟨callback, operation⟩ }
  return operation

private def consOperation (family : TSyntax `ident) (kind : CellTy) : PrepareM Operation := do
  if let some registered := (← get).constructors.find? (fun registered => registered.kind == kind) then
    return registered.operation
  let operationFamily := mkIdentFrom family
    (family.getId ++ `Operations ++ (match kind with | .nat => `consNat | .bool => `consBool))
  let head ← resolveType (← termOfExpr (match kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool))
  let operation : Operation := {
    family := operationFamily
    sourceName := `cons
    native := ⟨(mkCIdent ``List.cons).raw⟩
    inputs := #[head, .list kind]
    result := .list kind
    equation := none
    relation := mkIdentFrom family (operationFamily.getId ++ `cons_rel)
    refinement := mkIdentFrom family (operationFamily.getId ++ `cons_refines) }
  modify fun state => { state with constructors := state.constructors.push ⟨kind, operation⟩ }
  return operation

private def unconsOperation (family : TSyntax `ident) (kind : CellTy) : PrepareM Operation := do
  if let some registered := (← get).deconstructors.find? (fun registered => registered.kind == kind) then
    return registered.operation
  let operationFamily := mkIdentFrom family
    (family.getId ++ `Operations ++ (match kind with | .nat => `unconsNat | .bool => `unconsBool))
  let headType ← termOfExpr (match kind with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let head ← resolveType headType
  let native ← `(fun (values : List $headType) => values.head?.map (fun head => (head, values.tail)))
  let operation : Operation := {
    family := operationFamily, sourceName := `uncons, native,
    inputs := #[.list kind], result := .option (.prod head (.list kind)), equation := none,
    relation := mkIdentFrom family (operationFamily.getId ++ `uncons_rel),
    refinement := mkIdentFrom family (operationFamily.getId ++ `uncons_refines) }
  modify fun state => { state with deconstructors := state.deconstructors.push ⟨kind, operation⟩ }
  return operation

private def isEmptyOperation (family : TSyntax `ident) (kind : CellTy) : PrepareM Operation := do
  if let some registered := (← get).emptinessTests.find? (fun registered => registered.kind == kind) then
    return registered.operation
  let operationFamily := mkIdentFrom family
    (family.getId ++ `Operations ++ (match kind with | .nat => `isEmptyNat | .bool => `isEmptyBool))
  let result ← resolveType (← `(Bool))
  let operation : Operation := {
    family := operationFamily, sourceName := `isEmpty,
    native := ⟨(mkCIdent ``List.isEmpty).raw⟩,
    inputs := #[.list kind], result,
    equation := some (mkIdentFrom family (operationFamily.getId ++ `isEmpty_eq)),
    relation := mkIdentFrom family (operationFamily.getId ++ `isEmpty_rel),
    refinement := mkIdentFrom family (operationFamily.getId ++ `isEmpty_refines) }
  modify fun state => { state with emptinessTests := state.emptinessTests.push ⟨kind, operation⟩ }
  return operation

private def doTerm (elements : Array (TSyntax `doElem)) : TermElabM (TSyntax `term) := do
  let sequence : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩
  `(do $sequence:doSeq)

private def arrayOperation (append : Bool) : PrepareM Operation := do
  let family := mkIdent `Complexity.Language.Buffer.Copy
  unless (← get).calledFamilies.any (fun imported => imported.getId == family.getId) do
    modify fun state => { state with calledFamilies := state.calledFamilies.push family }
  let native ← if append then pure (⟨(mkCIdent ``Array.append).raw⟩ : TSyntax `term)
    else `(fun (xs : Array Nat) => xs)
  return {
    family, sourceName := if append then `append else `copy
    native
    inputs := if append then #[.array .nat, .array .nat] else #[.array .nat]
    result := .array .nat
    equation := none
    relation := mkCIdent (if append then ``Complexity.Language.Buffer.Copy.append_eval_exists
      else ``Complexity.Language.Buffer.Copy.copy_eval_exists)
    refinement := mkCIdent (if append then ``Complexity.Language.Buffer.append_array_refines
      else ``Complexity.Language.Buffer.copy_array_refines)
    preservingRelation := some (mkCIdent (if append then
      ``Complexity.Language.Buffer.Copy.append_eval_exists_preserving
      else ``Complexity.Language.Buffer.Copy.copy_eval_exists_preserving)) }

private partial def canonicalCall? (imports : ImportedPrograms) (scope : List Binding)
    (expression : TSyntax `term) :
    PrepareM (Option (TSyntax `term)) := do
  if let `($called:ident) := expression then
    if let .str receiverName "uncons" := called.getId then
      unless receiverName == `List do
        let receiver : TSyntax `ident := ⟨Syntax.ident called.raw.getHeadInfo
          receiverName.toString.toRawSubstring receiverName []⟩
        return some (← `(List.uncons $receiver:ident))
    if let .str receiverName "isEmpty" := called.getId then
      if scope.any (fun binding => binding.name.getId == receiverName) then
        let receiver : TSyntax `ident := ⟨Syntax.ident called.raw.getHeadInfo
          receiverName.toString.toRawSubstring receiverName []⟩
        return some (← `(List.isEmpty $receiver:ident))
  match expression with
  | `(($inner:term)) => canonicalCall? imports scope inner
  | `(Array.append $left:term $right:term) => return some (← `(Array.append $left $right))
  | `($left:term ++ $right:term) =>
      let leftValue ← value scope left
      if let .array .nat := leftValue.type then return some (← `(Array.append $left $right))
      return none
  | `(List.foldl $callback:ident $initial:term $values:term) =>
      return some (← `(List.foldl $callback:ident $initial $values))
  | `(List.cons $head:term $tail:term) => return some (← `(List.cons $head $tail))
  | `(List.uncons $values:term) => return some (← `(List.uncons $values))
  | `(List.isEmpty $values:term) => return some (← `(List.isEmpty $values))
  | `($head:term :: $tail:term) => return some (← `(List.cons $head $tail))
  | `($called:ident $arguments:term*) =>
      if let .str receiverName "uncons" := called.getId then
        unless receiverName == `List do
          unless arguments.isEmpty do throwErrorAt expression "list.uncons takes no additional arguments"
          let receiver : TSyntax `ident := ⟨Syntax.ident called.raw.getHeadInfo
            receiverName.toString.toRawSubstring receiverName []⟩
          return some (← `(List.uncons $receiver:ident))
      if let .str receiverName "isEmpty" := called.getId then
        if scope.any (fun binding => binding.name.getId == receiverName) then
          unless arguments.isEmpty do throwErrorAt expression "list.isEmpty takes no additional arguments"
          let receiver : TSyntax `ident := ⟨Syntax.ident called.raw.getHeadInfo
            receiverName.toString.toRawSubstring receiverName []⟩
          return some (← `(List.isEmpty $receiver:ident))
      if let .str receiverName "foldl" := called.getId then
        unless receiverName == `List do
          let some callbackTerm := (arguments[0]? : Option (TSyntax `term))
            | throwErrorAt expression "list.foldl requires a named callback and an initial value"
          let some initial := (arguments[1]? : Option (TSyntax `term))
            | throwErrorAt expression "list.foldl requires an initial value"
          unless arguments.size == 2 do throwErrorAt expression "wrong number of list.foldl arguments"
          let `($callback:ident) := callbackTerm.raw
            | throwErrorAt callbackTerm "fold callbacks must be named registered source functions"
          -- This is the user's receiver occurrence, not a generated temporary.
          let receiver : TSyntax `ident := ⟨Syntax.ident called.raw.getHeadInfo
            receiverName.toString.toRawSubstring receiverName []⟩
          return some (← `(List.foldl $callback:ident $initial $receiver:ident))
      if scope.any (fun binding => binding.name.getId == called.getId) then return none
      if (← get).functions.any (fun fn => fn.name.getId == called.getId) then return some expression
      if (← findImportedNative? imports called).isSome then return some expression
      return none
  | _ => return none

private partial def conditionalParts? (expression : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term × TSyntax `term) :=
  match expression with
  | `(($inner:term)) => conditionalParts? inner
  | `(if $condition:term then $yes:term else $no:term) => some (condition, yes, no)
  | _ => none

/-- Extract one actual call from transparent value constructors. Branches and
callbacks are deliberately not traversed: hoisting must not execute unselected code. -/
private partial def hoistValueCall? (imports : ImportedPrograms) (scope : List Binding)
    (expression : TSyntax `term) :
    PrepareM (Option (TSyntax `term × (TSyntax `term → TermElabM (TSyntax `term)))) := do
  match expression with
  | `(($inner:term)) =>
      if let some (called, rebuild) ← hoistValueCall? imports scope inner then
        return some (called, fun value => do `(($(← rebuild value))))
  | `(($inner:term : $type:term)) =>
      if let some (called, rebuild) ← hoistValueCall? imports scope inner then
        return some (called, fun value => do `(($(← rebuild value) : $type)))
  | `({ $fields:structInstField,* }) =>
      let fields := fields.getElems
      for index in [:fields.size] do
        let field := fields[index]!
        if let `(structInstField| $name:ident := $inner:term) := field then
          if let some (called, rebuild) ← hoistValueCall? imports scope inner then
            return some (called, fun value => do
              let updated ← `(structInstField| $name:ident := $(← rebuild value))
              let fields := fields.set! index updated
              `({ $fields:structInstField,* }))
  | `(($left:term, $right:term)) =>
      if let some (called, rebuild) ← hoistValueCall? imports scope left then
        return some (called, fun value => do `(($(← rebuild value), $right)))
      if let some (called, rebuild) ← hoistValueCall? imports scope right then
        return some (called, fun value => do `(($left, $(← rebuild value))))
  | `(some $inner:term) =>
      if let some (called, rebuild) ← hoistValueCall? imports scope inner then
        return some (called, fun value => do `(some $(← rebuild value)))
  | _ => pure ()
  if let some called ← canonicalCall? imports scope expression then
    return some (called, fun value => pure value)
  return none

private partial def matchParts? (expression : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) :=
  match expression with
  | `(($inner:term)) => matchParts? inner
  | `(match $discriminant:term with
      | $first:term => $firstBody:term
      | $second:term => $secondBody:term) =>
      some (discriminant, first, firstBody, second, secondBody)
  | _ => none

private def branchTerm (elements : TSyntax ``doSeq) : TermElabM (TSyntax `term) := do
  if let [element] := (getDoElems elements).toList then
    if let `(doElem| do $nested:doSeq) := element then
      return ← `(do $nested:doSeq)
  `(do $elements:doSeq)

private def isNonePattern (pattern : TSyntax `term) : Bool :=
  match pattern with | `(none) | `(Option.none) | `(.none) => true | _ => false

private def someName? (pattern : TSyntax `term) : Option (TSyntax `ident) :=
  match pattern with
  | `(some $name:ident) | `(Option.some $name:ident) | `(.some $name:ident) => some name
  | _ => none

private def isNilPattern (pattern : TSyntax `term) : Bool :=
  match pattern with | `([]) | `(List.nil) => true | _ => false

private def consNames? (pattern : TSyntax `term) :
    Option (TSyntax `ident × TSyntax `ident) :=
  match pattern with
  | `($head:ident :: $tail:ident) => some (head, tail)
  | _ => none

private partial def sequence (family : TSyntax `ident)
    (imports : ImportedPrograms) (resultType : NativeType)
    (scope : List Binding) (elements : List (TSyntax `doElem)) :
    PrepareM (Array (TSyntax `doElem) × Array (TSyntax `doElem) × Array Trace × Value) := do
  let bindAndContinue (binding : Binding) (raw native : TSyntax `doElem)
      (calls : Array Trace) (rest : List (TSyntax `doElem)) := do
    let (rawRest, nativeRest, later, returned) ← sequence family imports resultType (binding :: scope) rest
    return (#[raw] ++ rawRest, #[native] ++ nativeRest, calls ++ later, returned)
  match elements with
  | [] => throwError "every native source function must end with a return"
  | element :: rest => withRef element do
    -- An unparenthesized `if` after `←` is a `doIf`, not a term.
    -- Normalize that parser shape before the shared typed conditional path.
    if let `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      if let `(doElem| if $test:term then $yes:doSeq else $no:doSeq) := rhs then
        let yesTerm ← branchTerm yes
        let noTerm ← branchTerm no
        let expression ← `(if $test:term then $yesTerm:term else $noTerm:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence family imports resultType scope (normalized :: rest)
      if let `(doElem| match $discriminant:term with
          | $first:term => $firstBody:doSeq
          | $second:term => $secondBody:doSeq) := rhs then
        let firstBody ← branchTerm firstBody
        let secondBody ← branchTerm secondBody
        let expression ← `(match $discriminant:term with
          | $first:term => $firstBody:term
          | $second:term => $secondBody:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence family imports resultType scope (normalized :: rest)
    let binding? := match element with
      | `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term) =>
          some (name, annotation, expression)
      | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
          some (name, annotation, expression)
      | _ => none
    if let some (name, annotation, expression) := binding? then
      if let some (matched, first, firstBody, second, secondBody) := matchParts? expression then
        let some annotation := annotation
          | throwErrorAt name "a native match binding requires an explicit result type"
        let discriminant ← value scope matched
        if let .list _ := discriminant.type then
          let (nilBody, head, tail, consBody) ←
            if isNilPattern first then do
              let some (head, tail) := consNames? second
                | throwErrorAt second "expected a head :: tail List pattern"
              pure (firstBody, head, tail, secondBody)
            else if isNilPattern second then do
              let some (head, tail) := consNames? first
                | throwErrorAt first "expected a head :: tail List pattern"
              pure (secondBody, head, tail, firstBody)
            else throwErrorAt expression "a List match needs exactly [] and head :: tail branches"
          let `(do $consElements:doSeq) := consBody
            | throwErrorAt consBody "a native match branch must end in a do-block return"
          let inspected := mkIdent (← mkFreshUserName `listParts)
          let payload := mkIdent (← mkFreshUserName `listFields)
          let someElements := #[
            ← `(doElem| let $head:ident := $payload:ident.1),
            ← `(doElem| let $tail:ident := $payload:ident.2)] ++ getDoElems consElements
          let someBody ← doTerm someElements
          let optionMatch ← `(match ($inspected:ident) with
            | none => $nilBody:term
            | some $payload:ident => $someBody:term)
          let read ← `(doElem| let $inspected:ident := List.uncons $matched:term)
          let select ← `(doElem| let $name:ident : $annotation ← ($optionMatch:term))
          return ← sequence family imports resultType scope (read :: select :: rest)
        let .option payloadType := discriminant.type
          | throwErrorAt matched "native matching currently supports List and Option values"
        let (noneBody, payloadName, someBody) ←
          if isNonePattern first then do
            let some payload := someName? second
              | throwErrorAt second "expected a some payload option pattern"
            pure (firstBody, payload, secondBody)
          else if isNonePattern second then do
            let some payload := someName? first
              | throwErrorAt first "expected a some payload option pattern"
            pure (secondBody, payload, firstBody)
          else throwErrorAt expression "an Option match needs exactly none and some payload branches"
        let selectedType ← resolveType annotation
        let `(do $noneElements:doSeq) := noneBody
          | throwErrorAt noneBody "a native match branch must be a do block ending in return"
        let `(do $someElements:doSeq) := someBody
          | throwErrorAt someBody "a native match branch must be a do block ending in return"
        let payloadRaw := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_source"))
        let payloadRelation := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_represented"))
        let payload : Binding := {
          name := payloadName, type := payloadType, rawName := payloadRaw,
          relationName := payloadRelation, model := ⟨payloadName.raw⟩, rawModel := ⟨payloadRaw.raw⟩,
          observation := if payloadType.isPure then .refl else .named payloadRelation.getId }
        let (noneRaw, noneNative, noneCalls, noneResult) ←
          sequence family imports selectedType scope (getDoElems noneElements).toList
        let (someRaw, someNative, someCalls, someResult) ←
          sequence family imports selectedType (payload :: scope) (getDoElems someElements).toList
        let rawType ← rawTypeTerm selectedType.coreTy
        let initial ← rawDefaultTerm selectedType.coreTy
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let noneBlock : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((noneRaw.pop.push (← `(doElem| $slot:ident := $(noneResult.raw)))).map (·.raw))⟩
        let someBlock : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((someRaw.pop.push (← `(doElem| $slot:ident := $(someResult.raw)))).map (·.raw))⟩
        let noneNativeBody ← doTerm noneNative
        let someNativeBody ← doTerm someNative
        let payloadNativeType ← termOfExpr payloadType.nativeType
        let nativeChoice ← `(Option.elim $(discriminant.native) (Id.run $noneNativeBody:term)
          (fun ($payloadName:ident : $payloadNativeType) => Id.run $someNativeBody:term))
        let model ← `(Option.elim $(discriminant.model) $(noneResult.model)
          (fun ($payloadName:ident : $payloadNativeType) => $(someResult.model)))
        let binding : Binding := {
          name, type := selectedType, rawName, relationName,
          model, rawModel := ⟨rawName.raw⟩,
          observation := if selectedType.isPure then .refl else .named relationName.getId }
        let (rawRest, nativeRest, later, returned) ←
          sequence family imports resultType (binding :: scope) rest
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $rawType := $initial:term),
          ← `(doElem| match $(discriminant.raw):term with
            | none => $noneBlock:doSeq
            | some $payloadName:ident => $someBlock:doSeq),
          ← `(doElem| let $name:ident : $rawType := $slot:ident)]
        let nativeBinding ← `(doElem| let $name:ident : $nativeType := $nativeChoice)
        return (rawPrefix ++ rawRest, #[nativeBinding] ++ nativeRest,
          #[.optionMatch discriminant payload noneCalls someCalls noneResult someResult binding] ++ later,
          returned)
      if let some (test, yes, no) := conditionalParts? expression then
        let some annotation := annotation
          | throwErrorAt name "a native conditional binding requires an explicit result type"
        let selectedType ← resolveType annotation
        let condition ← value scope test
        expect test (← resolveType (← `(Bool))) condition.type
        let `(do $yesElements:doSeq) := yes
          | throwErrorAt yes "a native conditional branch must be a do block ending in return"
        let `(do $noElements:doSeq) := no
          | throwErrorAt no "a native conditional branch must be a do block ending in return"
        let (yesRaw, yesNative, yesCalls, yesResult) ←
          sequence family imports selectedType scope (getDoElems yesElements).toList
        let (noRaw, noNative, noCalls, noResult) ←
          sequence family imports selectedType scope (getDoElems noElements).toList
        let rawType ← rawTypeTerm selectedType.coreTy
        let initial ← rawDefaultTerm selectedType.coreTy
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let yesBlock : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((yesRaw.pop.push (← `(doElem| $slot:ident := $(yesResult.raw)))).map (·.raw))⟩
        let noBlock : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((noRaw.pop.push (← `(doElem| $slot:ident := $(noResult.raw)))).map (·.raw))⟩
        let yesNativeBody ← doTerm yesNative
        let noNativeBody ← doTerm noNative
        let nativeChoice ← `(if $(condition.native) then Id.run $yesNativeBody:term
          else Id.run $noNativeBody:term)
        let model ← `(if $(condition.model) then $(yesResult.model) else $(noResult.model))
        let binding : Binding := {
          name, type := selectedType, rawName, relationName,
          model, rawModel := ⟨rawName.raw⟩,
          observation := if selectedType.isPure then .refl else .named relationName.getId }
        let (rawRest, nativeRest, later, returned) ←
          sequence family imports resultType (binding :: scope) rest
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $rawType := $initial:term),
          ← `(doElem| if $(condition.raw) then $yesBlock:doSeq else $noBlock:doSeq),
          ← `(doElem| let $name:ident : $rawType := $slot:ident)]
        let nativeBinding ← `(doElem| let $name:ident : $nativeType := $nativeChoice)
        return (rawPrefix ++ rawRest, #[nativeBinding] ++ nativeRest,
          #[.conditional condition yesCalls noCalls yesResult noResult binding] ++ later, returned)
    match element with
    | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
        if let some call ← canonicalCall? imports scope expression then
          let binding ← `(doElem| let $name:ident $[: $annotation:term]? ← $call:term)
          return ← sequence family imports resultType scope (binding :: rest)
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceValue)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let binding ← `(doElem| let $name:ident $[: $annotation:term]? := $rewritten:term)
          return ← sequence family imports resultType scope (call :: binding :: rest)
        let result ← value scope expression (← annotation.mapM fun stx => return ← resolveType stx)
        if let some annotation := annotation then expect annotation (← resolveType annotation) result.type
        let rawType ← rawTypeTerm result.type.coreTy
        let nativeType ← termOfExpr result.type.nativeType
        bindAndContinue {
          name, type := result.type, rawName := name, relationName := name,
          model := result.model,
          rawModel := result.rawModel, observation := result.observation }
          (← `(doElem| let $name:ident : $rawType := $(result.raw)))
          (← `(doElem| let $name:ident : $nativeType := $(result.native))) #[] rest
    | `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term) =>
        let expression := (← canonicalCall? imports scope expression).getD expression
        let (operation, arguments) ← match expression with
          | `(Array.append $left:term $right:term) =>
              pure (← arrayOperation true, #[left, right])
          | `(List.foldl $callback:ident $initial:term $values:term) => do
              pure (← foldOperation family imports callback, #[initial, values])
          | `(List.cons $head:term $tail:term) => do
              let tailValue ← value scope tail
              let .list kind := tailValue.type | throwErrorAt tail "List.cons requires a represented list tail"
              pure (← consOperation family kind, #[head, tail])
          | `(List.uncons $values:term) => do
              let valuesValue ← value scope values
              let .list kind := valuesValue.type | throwErrorAt values "List.uncons requires a represented list"
              pure (← unconsOperation family kind, #[values])
          | `(List.isEmpty $values:term) => do
              let valuesValue ← value scope values
              let .list kind := valuesValue.type
                | throwErrorAt values "List.isEmpty requires a represented list"
              pure (← isEmptyOperation family kind, #[values])
          | `($called:ident $arguments:term*) => do
              if let some fn := (← get).functions.find? (fun fn => fn.name.getId == called.getId) then
                pure (functionOperation family fn, arguments)
              else
                let some info ← findImportedNative? imports called
                  | throwErrorAt called "expected a registered operation, earlier function or imported native function"
                let operation := importedOperation info
                unless (← get).calledFamilies.any (fun imported => imported.getId == operation.family.getId) do
                  modify fun state => { state with calledFamilies := state.calledFamilies.push operation.family }
                pure (operation, arguments)
          | _ => throwErrorAt expression "expected a named registered native source operation"
        unless arguments.size == operation.inputs.size do throwError "wrong number of native call arguments"
        let arguments ← arguments.mapM fun argument => return (← value scope argument)
        for argument in arguments, expected in operation.inputs do expect element expected argument.type
        if let some annotation := annotation then expect annotation (← resolveType annotation) operation.result
        let sourceName := mkIdentFrom name
          (if operation.family.getId == (sourceFamily family).getId then operation.sourceName
            else operation.family.getId ++ operation.sourceName)
        let raw := Lean.Syntax.mkApp ⟨sourceName.raw⟩ (arguments.map (·.raw))
        let native := Lean.Syntax.mkApp operation.native (arguments.map (·.native))
        let model := Lean.Syntax.mkApp operation.native (arguments.map (·.model))
        let rawType ← rawTypeTerm operation.result.coreTy
        let nativeType ← termOfExpr operation.result.nativeType
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let binding : Binding := {
          name, type := operation.result, rawName, relationName,
          model
          rawModel := ⟨rawName.raw⟩
          observation := if operation.result.isPure then .refl else .named relationName.getId }
        bindAndContinue binding
          (← `(doElem| let $name:ident : $rawType ← $raw:term))
          (← `(doElem| let $name:ident : $nativeType := $native))
          #[.call ⟨operation, arguments, binding⟩] rest
    | `(doElem| return $expression:term) =>
        unless rest.isEmpty do throwError "statements after the final return are not supported"
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceResult)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let returned ← `(doElem| return $rewritten:term)
          return ← sequence family imports resultType scope [call, returned]
        let result ← value scope expression (some resultType)
        expect element resultType result.type
        return (#[← `(doElem| return $(result.raw))], #[← `(doElem| return $(result.native))], #[], result)
    | _ => throwError "native source blocks support immutable lets, registered calls, typed conditional/match bindings and return"

private def prepareFunction (family : TSyntax `ident)
    (imports : ImportedPrograms) (stx : TSyntax `sourceFunction) : PrepareM Unit := do
  let `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term
      $termination:suffix) := stx | throwErrorAt stx "unsupported native source declaration"
  let hints ← Lean.Elab.elabTerminationHints termination
  if hints.isNotNone then
    throwErrorAt termination "native operation blocks do not introduce recursive definitions"
  if (← get).functions.any (fun fn => fn.name.getId == name.getId) then
    throwErrorAt name "duplicate native source function"
  let result ← resolveType result
  let mut parsed := #[]
  let mut scope := []
  for parameter in parameters do
    let `(sourceParameter| ($parameterName:ident : $type:term)) := parameter
      | throwErrorAt parameter "expected an explicitly typed native parameter"
    if scope.any (fun binding : Binding => binding.name.getId == parameterName.getId) then
      throwErrorAt parameterName "duplicate native source parameter"
    let type ← resolveType type
    let rawName := mkIdent (← mkFreshUserName (parameterName.getId.appendAfter "_source"))
    let relation := mkIdent (← mkFreshUserName (parameterName.getId.appendAfter "_represented"))
    let rawModel := if type.isPure then ⟨parameterName.raw⟩ else ⟨rawName.raw⟩
    let parameter : Parameter := { name := parameterName, type, rawName, relationName := relation }
    parsed := parsed.push parameter
    let binding : Binding := {
      toParameter := parameter,
      model := ⟨parameterName.raw⟩, rawModel,
      observation := if type.isPure then .refl else .named relation.getId }
    scope := binding :: scope
  let elements ← match body with
    | `(do $elements:doSeq) => pure (getDoElems elements).toList
    | _ => pure [← `(doElem| return $body:term)]
  let (raw, native, calls, returned) ← sequence family imports result scope elements
  let fn : Function := {
    name, parameters := parsed, result,
    rawBody := ← doTerm raw, nativeBody := ← doTerm native, calls, returned }
  modify fun state => { state with functions := state.functions.push fn }

private def kindTerm (kind : CellTy) : TermElabM (TSyntax `term) :=
  termOfExpr (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)

private def relationalFoldProofDeclarations (registration : FoldRegistration)
    (callbackRelation : Name) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let source := mkCIdent (callback.sourceFamily ++ `program)
  let fn := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "Id")
  let observe := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_observe")
  let native := mkCIdent callback.nativeName
  let same := name `callback_signature
  let evaluated := name `callback_eval
  let contract := name `callback_contract
  let fold := name `fold
  let program := name `program
  let foldId := name `foldId
  let accTy ← termOfExpr (coreTypeExpr callback.accumulator.coreTy)
  let accType ← termOfExpr callback.accumulator.nativeType
  let rawAccType ← actualTypeTerm callback.accumulator.coreTy
  let kind ← kindTerm callback.kind
  let headType ← termOfExpr (match callback.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let representation ← termOfExpr callback.accumulator.representation
  let represented ← `(($representation : Complexity.Language.Representation $accType $accTy))
  let initial := mkIdent `initial
  let actual := mkIdent `actual
  let head := mkIdent `head
  let heap := mkIdent `heap
  let accObserved := mkIdent `accObserved
  let mut callbackArgs : Array (TSyntax `term) := #[⟨initial.raw⟩, ⟨head.raw⟩]
  let mut callbackProof := #[]
  let mut roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let (actualAcc, accProof) ← match callback.accumulator with
    | .pure _ => do
        callbackProof := callbackProof.push (← `(tactic|
          change $initial:ident = $actual:ident at $accObserved:ident))
        callbackProof := callbackProof.push (← `(tactic| subst $actual:ident))
        pure ((⟨initial.raw⟩ : TSyntax `term), ← `(rfl))
    | _ => do
        callbackArgs := callbackArgs.push ⟨actual.raw⟩
        roots := roots.push (← `(bracketedBinder| ($actual:ident : $rawAccType)))
        observations := observations.push (← `(bracketedBinder|
          ($accObserved:ident : ($represented).Rel $initial:ident $actual:ident $heap:ident)))
        pure ((⟨actual.raw⟩ : TSyntax `term), (⟨accObserved.raw⟩ : TSyntax `term))
  callbackArgs := callbackArgs.push ⟨heap.raw⟩
  unless callback.accumulator.isPure do callbackArgs := callbackArgs.push ⟨accObserved.raw⟩
  let invocation := Lean.Syntax.mkApp ⟨(mkCIdent callbackRelation).raw⟩ callbackArgs
  callbackProof := callbackProof.push (← `(tactic|
    obtain ⟨value, finish, executed, related, _⟩ := $invocation))
  callbackProof := callbackProof.push (← `(tactic| refine ⟨value, finish, ?_, related⟩))
  callbackProof := callbackProof.push (← `(tactic|
    change ($source:ident).eval $fn:ident
      (Complexity.Language.Env.cons $actualAcc
        (Complexity.Language.Env.cons $head:ident Complexity.Language.Env.empty)) $heap:ident = _))
  callbackProof := callbackProof.push (← `(tactic| rw [$observe:ident]))
  callbackProof := callbackProof.push (← `(tactic| exact executed))
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    theorem $evaluated:ident ($initial:ident : $accType) ($actual:ident : $rawAccType)
        ($head:ident : $headType) ($heap:ident : Complexity.Language.Heap) (_ : True)
        ($accObserved:ident : ($represented).Rel $initial:ident $actual:ident $heap:ident) :
        ∃ value finish,
          Complexity.Language.List.Fold.calleeEval $source:ident $fn:ident $same:ident
            $actual:ident $head:ident $heap:ident = Part.some (.ok value, finish) ∧
          ($represented).Rel ($native:ident $initial:ident $head:ident) value finish := by
      $callbackProof:tactic*)).raw
  declarations := declarations.push (← `(command|
    theorem $contract:ident : Complexity.Language.List.Fold.Contract $source:ident $fn:ident $same:ident
        $represented $native:ident (fun _ _ => True) :=
      Complexity.Language.List.Fold.Contract.of_eval
        (source := $source:ident) (fn := $fn:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (R := $represented)
        (step := $native:ident) (domain := fun _ _ => True) $evaluated:ident)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.relation):ident ($initial:ident : $accType) (values : List $headType)
        $roots:bracketedBinder* (root : Option (Complexity.Language.NodeRef $kind))
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder*
        (observed : (Complexity.Language.Representation.list $kind).Rel values root $heap:ident) :
        ∃ value finish,
          $fold:ident $actualAcc root $heap:ident = Part.some (.ok value, finish) ∧
          ($represented).Rel (values.foldl $native:ident $initial:ident) value finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨value, finish, executed, related, _, preserved⟩ :=
        Complexity.Language.List.Fold.eval_exists
          (source := $source:ident) (fn := $fn:ident) (same := $same:ident)
          (accTy := $accTy) (kind := $kind) (R := $represented)
          (step := $native:ident) (domain := fun _ _ => True)
          $contract:ident $initial:ident values $actualAcc root $heap:ident
          (by intro processed head suffix equality; trivial) $accProof observed
      exact ⟨value, finish, executed, related, preserved⟩)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $foldId:ident (Complexity.Language.List.Fold.representation $represented $kind)
        (fun _ => True) (fun input => input.2.foldl $native:ident input.1) := by
      intro input _
      exact Complexity.Language.List.Fold.program_refines $contract:ident input
        (by intro processed head suffix equality; trivial))).raw
  return declarations

private def foldDeclarations (registration : FoldRegistration) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let originalProgram := mkCIdent (callback.sourceFamily ++ `program)
  let originalSignatures := mkCIdent (callback.sourceFamily ++ `signatures)
  let originalId := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "Id")
  let originalObserve := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_observe")
  let originalPure := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_action_eq_pure")
  let native := mkCIdent callback.nativeName
  let accTy ← termOfExpr (coreTypeExpr callback.accumulator.coreTy)
  let accType ← termOfExpr callback.accumulator.nativeType
  let rawAccType ← actualTypeTerm callback.accumulator.coreTy
  let kind ← kindTerm callback.kind
  let headType ← termOfExpr (match callback.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let same := name `callback_signature
  let callbackPure := name `callback_pure
  let callbackContract := name `callback_contract
  let foldId := name `foldId
  let fold := name `fold
  let observe := name `fold_observe
  let resultRepresentation ← termOfExpr operation.result.representation
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    theorem $same:ident : $originalSignatures:ident[$originalId:ident] =
        Complexity.Language.List.Fold.stepSignature $accTy $kind := rfl)).raw
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      Complexity.Language.List.Fold.foldSignature $accTy $kind :: $originalSignatures:ident)).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Fold.program $originalProgram:ident $originalId:ident $same:ident)).raw
  declarations := declarations.push (← `(command|
    abbrev $foldId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Fold.entry $accTy $kind $originalSignatures:ident)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $fold:ident (initial : $rawAccType)
        (root : Option (Complexity.Language.NodeRef $kind)) :
        ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part) $rawAccType :=
      Complexity.Language.List.Fold.foldEval $originalProgram:ident $originalId:ident $same:ident
        initial root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Fold.foldSignature $accTy $kind).params,
        ($program:ident).eval $foldId:ident args = $fold:ident args.head args.tail.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro initial
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  if let some relation := callback.relation then
    return declarations ++ (← relationalFoldProofDeclarations registration relation)
  let some equation := operation.equation | throwError "registered pure fold is missing its exact equation"
  declarations := declarations.push (← `(command|
    theorem $callbackPure:ident (initial : $accType) (head : $headType) (_ : True) :
        Complexity.Language.List.Fold.calleeEval $originalProgram:ident $originalId:ident
          $same:ident initial head = pure ($native:ident initial head) := by
      change ($originalProgram:ident).eval $originalId:ident
        (Complexity.Language.Env.cons initial
          (Complexity.Language.Env.cons head Complexity.Language.Env.empty)) = _
      rw [$originalObserve:ident]
      exact $originalPure:ident initial head)).raw
  declarations := declarations.push (← `(command|
    theorem $callbackContract:ident : Complexity.Language.List.Fold.Contract
        $originalProgram:ident $originalId:ident $same:ident
        (Complexity.Language.Representation.ofEmbedding (Function.Embedding.refl $accType))
        $native:ident (fun _ _ => True) :=
      Complexity.Language.List.Fold.Contract.of_pure_eval
        (source := $originalProgram:ident) (fn := $originalId:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (step := $native:ident) (domain := fun _ _ => True)
        (Function.Embedding.refl $accType) $callbackPure:ident)).raw
  declarations := declarations.push (← `(command|
    theorem $equation:ident (initial : $accType) (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        $fold:ident initial root heap = Part.some (.ok (values.foldl $native:ident initial), heap) := by
      exact Complexity.Language.List.Fold.eval_eq_pure_of_contents
        (source := $originalProgram:ident) (fn := $originalId:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (step := $native:ident) (domain := fun _ _ => True)
        (Function.Embedding.refl $accType) $callbackPure:ident initial values root heap
        (by intro processed head suffix equality; trivial) observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.relation):ident (initial : $accType) (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $fold:ident initial root heap = Part.some (.ok returned, finish) ∧
          ($resultRepresentation : Complexity.Language.Representation $accType $accTy).Rel
            (values.foldl $native:ident initial) returned finish ∧
          heap.ShapeExtends finish := by
      exact ⟨_, heap, $equation:ident initial values root heap observed, rfl,
        Complexity.Language.Heap.ShapeExtends.refl heap⟩)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $foldId:ident
        (Complexity.Language.List.Fold.representation
          (Complexity.Language.Representation.ofEmbedding (Function.Embedding.refl $accType)) $kind)
        (fun _ => True) (fun input => input.2.foldl $native:ident input.1) := by
      intro input _
      exact Complexity.Language.List.Fold.program_refines $callbackContract:ident input
        (by intro processed head suffix equality; trivial))).raw
  return declarations

private def consDeclarations (registration : ConsRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let consId := name `consId
  let cons := name `cons
  let observe := name `cons_observe
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.Cons.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Cons.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $consId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Cons.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $cons:ident (head : $headType)
        (tail : Option (Complexity.Language.NodeRef $kind)) :
        ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part)
          (Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.Cons.consEval $kind head tail)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Cons.signature $kind).params,
        ($program:ident).eval $consId:ident args = $cons:ident args.head args.tail.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro head
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro tail
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.relation):ident (head : $headType) (values : List $headType)
        (tail : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values tail heap) :
        ∃ returned finish,
          $cons:ident head tail heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.Representation.list $kind).Rel (head :: values) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Cons.eval_exists $kind head values tail heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $consId:ident (Complexity.Language.List.Cons.representation $kind)
        (fun _ => True) (fun input => input.1 :: input.2) :=
      Complexity.Language.List.Cons.refines $kind)).raw
  return declarations

private def unconsDeclarations (registration : UnconsRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let unconsId := name `unconsId
  let uncons := name `uncons
  let observe := name `uncons_observe
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.Uncons.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Uncons.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $unconsId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Uncons.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $uncons:ident (root : Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.Uncons.unconsEval $kind root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Uncons.signature $kind).params,
        ($program:ident).eval $unconsId:ident args = $uncons:ident args.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $uncons:ident root heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.List.Uncons.resultRepresentation $kind).Rel
            (values.head?.map (fun head => (head, values.tail))) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Uncons.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $unconsId:ident (Complexity.Language.List.Uncons.representation $kind)
        (fun _ => True) (fun values => values.head?.map (fun head => (head, values.tail))) :=
      Complexity.Language.List.Uncons.refines $kind)).raw
  return declarations

private def isEmptyDeclarations (registration : IsEmptyRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let isEmptyId := name `isEmptyId
  let isEmpty := name `isEmpty
  let observe := name `isEmpty_observe
  let some equation := operation.equation
    | throwError "registered emptiness test is missing its unchanged-heap equation"
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.IsEmpty.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.IsEmpty.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $isEmptyId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.IsEmpty.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $isEmpty:ident (root : Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.IsEmpty.isEmptyEval $kind root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.IsEmpty.signature $kind).params,
        ($program:ident).eval $isEmptyId:ident args = $isEmpty:ident args.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $equation:ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        $isEmpty:ident root heap = Part.some (.ok values.isEmpty, heap) := by
      obtain ⟨returned, finish, evaluated, related, unchanged⟩ :=
        Complexity.Language.List.IsEmpty.eval_exists_heap_eq $kind values root heap observed
      change values.isEmpty = returned at related
      rw [← related, unchanged] at evaluated
      exact evaluated)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $isEmpty:ident root heap = Part.some (.ok returned, finish) ∧
          Complexity.Language.Representation.bool.Rel values.isEmpty returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.IsEmpty.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operation.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $isEmptyId:ident (Complexity.Language.List.IsEmpty.representation $kind)
        (fun _ => True) (fun values => values.isEmpty) :=
      Complexity.Language.List.IsEmpty.refines $kind)).raw
  return declarations

private def rawFunction (fn : Function) : TermElabM (TSyntax `sourceFunction) := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← rawTypeTerm parameter.type.coreTy
    `(sourceParameter| ($(parameter.name):ident : $type))
  let result ← rawTypeTerm fn.result.coreTy
  `(sourceFunction| def $(fn.name):ident $parameters:sourceParameter* : $result := $(fn.rawBody))

private def nativeDeclaration (family : TSyntax `ident) (fn : Function) : TermElabM Syntax := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← termOfExpr parameter.type.nativeType
    `(bracketedBinder| ($(parameter.name):ident : $type))
  let result ← termOfExpr fn.result.nativeType
  let name := fieldName family fn.name
  return (← `(command|
    /-- Ordinary mathematical function generated from the same represented source block. -/
    def $name:ident $parameters:bracketedBinder* : $result := Id.run $(fn.nativeBody))).raw

private def normalizeAction : TermElabM (TSyntax `tactic) :=
  `(tactic| simp only [Id.run, Id.instMonad, Bind.bind, Pure.pure,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
    StateT.bind, StateT.pure, Part.bind_some])

/-- Restrict conditional distribution to the action's bind, rather than
distributing arbitrary curried applications during canonicalization. -/
private theorem bind_conditional {m : Type u → Type v} [Bind m] {α β : Type u}
    (condition : Prop) [Decidable condition] (yes no : m α) (next : α → m β) :
    ((if condition then yes else no) >>= next) =
      (if condition then yes >>= next else no >>= next) :=
  apply_ite_left (fun (action : m α) (continuation : α → m β) => action >>= continuation)
    condition yes no next

/-- The same bind distributes over an optional payload without inspecting it. -/
private theorem bind_optionMatch {m : Type u → Type v} [Bind m] {α β γ : Type u}
    (value : Option α) (absent : m β) (present : α → m β) (next : β → m γ) :
    (Option.elim value absent present >>= next) =
      Option.elim value (absent >>= next) (fun payload => present payload >>= next) := by
  cases value <;> rfl

private structure CorrespondenceHeader where
  nativeName : TSyntax `ident
  rawEquation : TSyntax `ident
  heap : TSyntax `ident
  parameters : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  nativeValue : TSyntax `term
  rawAction : TSyntax `term
  relations : Array RetainedObservation

private def correspondenceHeader (family : TSyntax `ident) (fn : Function) :
    TermElabM CorrespondenceHeader := do
  let nativeName := fieldName family fn.name
  let rawName := fieldName (sourceFamily family) fn.name
  let rawEquation := fieldName (sourceFamily family) fn.name "_eq"
  let heap := mkIdent (← mkFreshUserName `initialHeap)
  let mut parameters : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut nativeArguments : Array (TSyntax `term) := #[]
  let mut rawArguments : Array (TSyntax `term) := #[]
  let mut roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut relations : Array RetainedObservation := #[]
  for parameter in fn.parameters do
    let type ← termOfExpr parameter.type.nativeType
    parameters := parameters.push (← `(bracketedBinder| ($(parameter.name):ident : $type)))
    nativeArguments := nativeArguments.push (⟨parameter.name.raw⟩ : TSyntax `term)
    match parameter.type with
    | .pure _ => rawArguments := rawArguments.push ⟨parameter.name.raw⟩
    | _ =>
        let rawType ← actualTypeTerm parameter.type.coreTy
        roots := roots.push (← `(bracketedBinder| ($(parameter.rawName):ident : $rawType)))
        rawArguments := rawArguments.push ⟨parameter.rawName.raw⟩
        let representation ← termOfExpr parameter.type.representation
        observations := observations.push (← `(bracketedBinder|
          ($(parameter.relationName):ident : ($representation).Rel
            $(parameter.name):ident $(parameter.rawName):ident $heap:ident)))
        relations := relations.push ⟨parameter.relationName.getId, parameter.type,
          ⟨parameter.relationName.raw⟩⟩
  let nativeValue := Lean.Syntax.mkApp ⟨nativeName.raw⟩ nativeArguments
  let rawAction := Lean.Syntax.mkApp ⟨rawName.raw⟩ rawArguments
  return ⟨nativeName, rawEquation, heap, parameters, roots, observations,
    nativeValue, rawAction, relations⟩

private partial def observationProof (observation : Observation) (heap : TSyntax `term)
    (relations : Array RetainedObservation) : TermElabM (TSyntax `term) := do
  match observation with
  | .refl => `(rfl)
  | .named name =>
      let some entry := relations.find? (fun entry => entry.name == name)
        | throwError "the value's observation is not available in its current heap"
      pure entry.proof
  | .nil kind => `(Complexity.Language.Representation.list_nil $(← kindTerm kind) $heap)
  | .pair purePair left right =>
      let left ← observationProof left heap relations
      let right ← observationProof right heap relations
      if purePair then `(congrArg₂ Prod.mk $left $right) else `(And.intro $left $right)
  | .projection purePair first pair =>
      let pair ← observationProof pair heap relations
      if purePair then
        if first then `(congrArg Prod.fst $pair) else `(congrArg Prod.snd $pair)
      else if first then `(And.left $pair) else `(And.right $pair)
  | .none payload => do
      let nativeType ← termOfExpr payload.nativeType
      let coreType ← termOfExpr (coreTypeExpr payload.coreTy)
      let representation ← termOfExpr payload.representation
      `(Complexity.Language.Representation.option_none
        ($representation : Complexity.Language.Representation $nativeType $coreType) $heap)
  | .some payload => observationProof payload heap relations
  | .binary operation left right =>
      `(congrArg₂ $operation $(← observationProof left heap relations)
        $(← observationProof right heap relations))

private def observationAt (argument : Value) (heap : TSyntax `term)
    (relations : Array RetainedObservation) : TermElabM (TSyntax `term) :=
  observationProof argument.observation heap relations

private partial def preservation (type : NativeType) (initial finish shape : TSyntax `term)
    (contents : Option (TSyntax `term) := none) :
    TermElabM (TSyntax `term) := do
  let nativeType ← termOfExpr type.nativeType
  let coreType ← termOfExpr (coreTypeExpr type.coreTy)
  let represented ← termOfExpr type.representation
  let proof ← match type with
    | .pure _ => `(by
        intro a sourceValue observed
        exact observed)
    | .list kind => do
        `(Complexity.Language.Representation.Preserves.list $(← kindTerm kind) $shape)
    | .array _ => do
        let some contents := contents
          | throwError "this call has no proof that it preserves the previously observed array contents"
        `(by
          intro values view observed
          exact $contents view values observed)
    | .prod left right => do
        `(Complexity.Language.Representation.Preserves.prod
          $(← preservation left initial finish shape contents)
          $(← preservation right initial finish shape contents))
    | .option payload => do
        `(Complexity.Language.Representation.Preserves.option
          $(← preservation payload initial finish shape contents))
    | .record _ layout embedding => do
        `(Complexity.Language.Representation.Preserves.comap $(← termOfExpr embedding)
          $(← preservation layout initial finish shape contents))
  `(($proof : Complexity.Language.Representation.Preserves
    ($represented : Complexity.Language.Representation $nativeType $coreType) $initial $finish))

/-- Reassociate the same named source observations for proof composition. The
generated source equation checks this expression against the actual lowered body. -/
private def resolveRaw (term : TSyntax `term) (known : Array (Name × TSyntax `term)) :
    TSyntax `term := ⟨term.raw.rewriteBottomUp fun stx =>
  if stx.isIdent then
    ((known.find? (fun entry => entry.1 == stx.getId)).map (·.2.raw)).getD stx
  else stx⟩

private partial def traceAction (trace : List Trace) (returned : Value)
    (known : Array (Name × TSyntax `term) := #[]) :
    TermElabM (TSyntax `term) := do
  let action ← match trace with
    | [] => `(pure $(resolveRaw returned.rawModel known))
    | .call invocation :: rest => do
        let name := mkIdentFrom invocation.operation.family
          (invocation.operation.family.getId ++ invocation.operation.sourceName)
        let called := Lean.Syntax.mkApp ⟨name.raw⟩
          (invocation.arguments.map (fun argument => resolveRaw argument.rawModel known))
        let type ← actualTypeTerm invocation.result.type.coreTy
        let next ← traceAction rest returned known
        `(do
          let $(invocation.result.rawName):ident : $type ← ($called:term)
          $next:term)
    | .conditional condition yes no yesResult noResult result :: rest => do
        let yesAction ← traceAction yes.toList yesResult known
        let noAction ← traceAction no.toList noResult known
        let next ← traceAction rest returned known
        let type ← actualTypeTerm result.type.coreTy
        let selected ← `(if $(resolveRaw condition.rawModel known) then $yesAction:term
          else $noAction:term)
        `(do
          let $(result.rawName):ident : $type ← ($selected:term)
          $next:term)
    | .optionMatch discriminant payload absent present noneResult someResult result :: rest => do
        let noneAction ← traceAction absent.toList noneResult known
        let someAction ← traceAction present.toList someResult known
        let next ← traceAction rest returned known
        let type ← actualTypeTerm result.type.coreTy
        let payloadType ← actualTypeTerm payload.type.coreTy
        let selected ← `(Option.elim $(resolveRaw discriminant.rawModel known) $noneAction:term
          (fun ($(payload.rawName):ident : $payloadType) => $someAction:term))
        `(do
          let $(result.rawName):ident : $type ← ($selected:term)
          $next:term)
  let type ← actualTypeTerm returned.type.coreTy
  `(($action : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $type))

private partial def relationTrace (trace : Array Trace) (returnedValue : Value)
    (initialHeap : TSyntax `term) (initialRelations : Array RetainedObservation)
    (initialKnown : Array (Name × TSyntax `term) := #[]) (preserveArrays : Bool := false) :
    TermElabM (Array (TSyntax `tactic)) := do
  let mut relations := initialRelations
  let mut known := initialKnown
  let mut currentHeap := initialHeap
  let mut preserved ← `(Complexity.Language.Heap.ShapeExtends.refl $initialHeap)
  let mut preservedContents ← `((by
    intro kind view values observed
    exact observed : Complexity.Language.Buffer.PreservesContents $initialHeap $initialHeap))
  let mut tactics := #[← normalizeAction]
  for instruction in trace do
    let (result, relationProof) ← match instruction with
      | .call invocation => do
          let mut applied := invocation.arguments.map (·.model)
          let mut hypotheses := #[]
          for argument in invocation.arguments do
            if argument.type.isPure then
              let observed ← observationAt argument currentHeap relations
              let equality := mkIdent (← mkFreshUserName `argumentEqual)
              let raw := resolveRaw argument.rawModel known
              tactics := tactics.push (← `(tactic|
                have $equality:ident : $(argument.model) = $raw := $observed))
              tactics := tactics.push (← `(tactic|
                simp (config := { failIfUnchanged := false }) only [← $equality:ident]))
            else
              applied := applied.push argument.rawModel
              hypotheses := hypotheses.push (← observationAt argument currentHeap relations)
          applied := applied.push currentHeap ++ hypotheses
          let relation ← if preserveArrays then do
              let some strong := invocation.operation.preservingRelation
                | throwError "native array composition requires a proved contents-preserving call"
              pure strong
            else pure invocation.operation.relation
          pure (invocation.result, Lean.Syntax.mkApp ⟨relation.raw⟩ applied)
      | .conditional condition yes no yesResult noResult result => do
          let yesAction ← traceAction yes.toList yesResult known
          let noAction ← traceAction no.toList noResult known
          let type ← actualTypeTerm result.type.coreTy
          let coreType ← termOfExpr (coreTypeExpr result.type.coreTy)
          let nativeType ← termOfExpr result.type.nativeType
          let representation ← termOfExpr result.type.representation
          let summary := mkIdent (← mkFreshUserName `branchRelated)
          let test := mkIdent (← mkFreshUserName `branchSelected)
          let yesProof ← relationTrace yes yesResult currentHeap relations known preserveArrays
          let noProof ← relationTrace no noResult currentHeap relations known preserveArrays
          let heapPost ← if preserveArrays then
              `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish ∧
                Complexity.Language.Buffer.PreservesContents $currentHeap finish)
            else `(fun finish => Complexity.Language.Heap.ShapeExtends $currentHeap finish)
          tactics := tactics.push (← `(tactic|
            have $summary:ident : ∃ (returned : $type) (finish : Complexity.Language.Heap),
                (if $(condition.model) then $yesAction else $noAction) $currentHeap =
                  Part.some (.ok returned, finish) ∧
                ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
                  $(result.model) returned finish ∧
                $heapPost finish := by
              by_cases $test:ident : $(condition.model) = true
              · simp only [if_pos $test:ident]
                $yesProof:tactic*
              · simp only [if_neg $test:ident]
                $noProof:tactic*))
          pure (result, (⟨summary.raw⟩ : TSyntax `term))
      | .optionMatch discriminant payload absent present noneResult someResult result => do
          let noneAction ← traceAction absent.toList noneResult known
          let someAction ← traceAction present.toList someResult known
          let raw := resolveRaw discriminant.rawModel known
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
          let noneProof ← relationTrace absent noneResult currentHeap relations known preserveArrays
          let mut someRelations := relations
          let mut someKnown := known
          let mut somePrefix := #[]
          if payload.type.isPure then
            somePrefix := somePrefix.push (← `(tactic|
              change $(payload.model) = $(payload.rawName):ident at $payloadObserved:ident))
            somePrefix := somePrefix.push (← `(tactic| subst $(payload.rawName):ident))
            someKnown := someKnown.push (payload.rawName.getId, payload.model)
          else
            someRelations := someRelations.push ⟨payloadObserved.getId, payload.type,
              ⟨payloadObserved.raw⟩⟩
          let someProof := somePrefix ++
            (← relationTrace present someResult currentHeap someRelations someKnown preserveArrays)
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
                  $(result.model) returned finish ∧
                $heapPost finish := by
              have $observed:ident :
                  ($discriminantRepresentation : Complexity.Language.Representation
                    $discriminantType $discriminantCore).Rel $(discriminant.model) $raw $currentHeap :=
                $observation
              cases $rawCase:ident : $raw:term with
              | none =>
                  cases $nativeCase:ident : $(discriminant.model):term with
                  | none =>
                      simp (config := { failIfUnchanged := false }) only [$rawCase:ident, $nativeCase:ident,
                        Option.elim_none, Option.elim_some]
                      $noneProof:tactic*
                  | some $impossible:ident =>
                      simp only [Complexity.Language.Representation.option, $rawCase:ident,
                        $nativeCase:ident] at $observed:ident
              | some $(payload.rawName):ident =>
                  cases $nativeCase:ident : $(discriminant.model):term with
                  | none =>
                      simp only [Complexity.Language.Representation.option, $rawCase:ident,
                        $nativeCase:ident] at $observed:ident
                  | some $(payload.name):ident =>
                      have $payloadObserved:ident :
                          ($payloadRepresentation : Complexity.Language.Representation
                            $payloadType $payloadCore).Rel
                            $(payload.name):ident $(payload.rawName):ident $currentHeap := by
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
    tactics := tactics.push (← `(tactic|
      obtain ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident, $extended:ident⟩ :=
        $relationProof))
    if preserveArrays then
      tactics := tactics.push (← `(tactic|
        obtain ⟨$extended:ident, $contents:ident⟩ := $extended:ident))
    if let .pure _ := result.type then
      tactics := tactics.push (← `(tactic| change $(result.model) = $returned:ident at $observed:ident))
      tactics := tactics.push (← `(tactic| subst $returned:ident))
      known := known.push (result.rawName.getId, result.model)
    tactics := tactics.push (← `(tactic|
      simp (config := { failIfUnchanged := false }) only [Id.run, Id.instMonad, Bind.bind, Pure.pure,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
        StateT.bind, StateT.pure, Part.bind_some] at $executed:ident))
    tactics := tactics.push (← `(tactic| rw [$executed:ident]))
    tactics := tactics.push (← normalizeAction)
    let mut nextRelations := #[]
    for entry in relations do
      let transported := mkIdent (← mkFreshUserName `retainedList)
      let keeps ← preservation entry.type currentHeap ⟨finish.raw⟩ ⟨extended.raw⟩
        (if preserveArrays then some ⟨contents.raw⟩ else none)
      tactics := tactics.push (← `(tactic|
        have $transported:ident := $keeps $(entry.proof)))
      nextRelations := nextRelations.push ⟨entry.name, entry.type, ⟨transported.raw⟩⟩
    relations := nextRelations
    unless result.type.isPure do
      relations := relations.push ⟨observed.getId, result.type, ⟨observed.raw⟩⟩
    preserved ← `(Complexity.Language.Heap.ShapeExtends.trans $preserved $extended:ident)
    if preserveArrays then
      preservedContents ← `(fun {kind} view values observed =>
        $contents:ident (kind := kind) view values ($preservedContents view values observed))
    currentHeap := ⟨finish.raw⟩
  let observed ← observationAt returnedValue currentHeap relations
  let result := resolveRaw returnedValue.rawModel known
  let heapPost ← if preserveArrays then `(And.intro $preserved $preservedContents) else pure preserved
  tactics := tactics.push (← `(tactic|
    exact ⟨$result, $currentHeap, rfl, $observed, $heapPost⟩))
  return tactics

private def equationDeclaration (family : TSyntax `ident) (fn : Function) : TermElabM Syntax := do
  let header ← correspondenceHeader family fn
  let ⟨nativeName, rawEquation, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let equationName := fieldName family fn.name "_action_eq_native"
  let mut tactics := #[← `(tactic| rw [$rawEquation:ident]),
    ← `(tactic| unfold $nativeName:ident), ← normalizeAction]
  for instruction in fn.calls do
    let .call invocation := instruction
      | throwError "a conditional block uses relational correspondence"
    let operation := invocation.operation
    let arguments := invocation.arguments
    let mut applied := arguments.map (·.model)
    let mut relations := #[]
    for argument in arguments do
      unless argument.type.isPure do
        applied := applied.push argument.rawModel
        relations := relations.push (← observationAt argument ⟨heap.raw⟩ inputRelations)
    applied := applied.push ⟨heap.raw⟩ ++ relations
    let some equation := operation.equation
      | throwError "an allocating operation has no unchanged-heap equation"
    let rule := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
    tactics := tactics.push (← `(tactic| rw [($rule)]))
    tactics := tactics.push (← normalizeAction)
  tactics := tactics.push (← `(tactic| all_goals rfl))
  return (← `(command|
    /-- Conditional correspondence on actual list representations in the supplied heap. -/
    theorem $equationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
        $rawAction $heap:ident = Part.some (.ok $nativeValue, $heap:ident) := by
      $tactics:tactic*)).raw

private def relationDeclaration (family : TSyntax `ident) (fn : Function)
    (preserveArrays : Bool := false) : TermElabM Syntax := do
  let header ← correspondenceHeader family fn
  let ⟨nativeName, rawEquation, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let relationName := fieldName family fn.name
    (if preserveArrays then "_action_rel_native_preserving" else "_action_rel_native")
  let resultType ← actualTypeTerm fn.result.coreTy
  let resultCoreType ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeResultType ← termOfExpr fn.result.nativeType
  let resultRepresentation ← termOfExpr fn.result.representation
  let heapPost ← if preserveArrays then
      `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
        Complexity.Language.Buffer.PreservesContents $heap:ident finish)
    else `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish)
  let declaration (tactics : Array (TSyntax `tactic)) : TermElabM Syntax := do
    return (← `(command|
      /-- Successful execution observes the native result in its actual final heap
      and retains every previously represented immutable list. -/
      theorem $relationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
          ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
          ∃ (returned : $resultType) (finish : Complexity.Language.Heap),
            $rawAction $heap:ident = Part.some (.ok returned, finish) ∧
            ($resultRepresentation : Complexity.Language.Representation
              $nativeResultType $resultCoreType).Rel $nativeValue returned finish ∧
            $heapPost finish := by
        $tactics:tactic*)).raw
  if fn.hasExactEquation then
    let equation := fieldName family fn.name "_action_eq_native"
    let mut applied := fn.parameters.map (fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term))
    for parameter in fn.parameters do
      unless parameter.type.isPure do applied := applied.push ⟨parameter.rawName.raw⟩
    applied := applied.push ⟨heap.raw⟩ ++ inputRelations.map (·.proof)
    let correct := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
    let frame ← if preserveArrays then
        `(And.intro (Complexity.Language.Heap.ShapeExtends.refl $heap:ident)
          (by intro kind view values observed; exact observed))
      else `(Complexity.Language.Heap.ShapeExtends.refl $heap:ident)
    return ← declaration #[← `(tactic|
      exact ⟨$nativeValue, $heap:ident, $correct, rfl, $frame⟩)]
  if fn.preservesArrays && !preserveArrays then
    let strong := fieldName family fn.name "_action_rel_native_preserving"
    let mut applied := fn.parameters.map (fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term))
    for parameter in fn.parameters do
      unless parameter.type.isPure do applied := applied.push ⟨parameter.rawName.raw⟩
    applied := applied.push ⟨heap.raw⟩ ++ inputRelations.map (·.proof)
    let correct := Lean.Syntax.mkApp ⟨strong.raw⟩ applied
    return ← declaration #[
      ← `(tactic| obtain ⟨returned, finish, executed, related, shape, _⟩ := $correct),
      ← `(tactic| exact ⟨returned, finish, executed, related, shape⟩)]
  let mut tactics := #[]
  if fn.calls.any (fun | .call _ => false | _ => true) then
    let action ← traceAction fn.calls.toList fn.returned
    let canonical := mkIdent (← mkFreshUserName `sourceComposition)
    tactics := tactics.push (← `(tactic|
      have $canonical:ident : $rawAction = $action := by
        rw [$rawEquation:ident]
        simp only [Id.run, Id.instMonad, pure_bind, bind_pure, bind_assoc,
          bind_conditional, bind_optionMatch]
        all_goals repeat' first
          | rfl
          | (split <;> simp_all only [Option.some.injEq, reduceCtorEq,
              Option.elim_none, Option.elim_some])
          | (congr 1; funext value)
        all_goals rfl))
    tactics := tactics.push (← `(tactic| rw [$canonical:ident]))
  else
    tactics := tactics.push (← `(tactic| rw [$rawEquation:ident]))
  tactics := tactics.push (← `(tactic| unfold $nativeName:ident))
  tactics := tactics ++ (← relationTrace fn.calls fn.returned ⟨heap.raw⟩ inputRelations #[] preserveArrays)
  declaration tactics

private partial def inputType : List Parameter → TermElabM (TSyntax `term)
  | [] => `(Unit)
  | [parameter] => termOfExpr parameter.type.nativeType
  | parameter :: rest => do `($(← termOfExpr parameter.type.nativeType) × $(← inputType rest))

private partial def inputRepresentation : List Parameter → TermElabM (TSyntax `term)
  | [] => `(Complexity.Language.ArgumentRepresentation.nil)
  | [parameter] => do
      `(Complexity.Language.ArgumentRepresentation.single $(← termOfExpr parameter.type.representation))
  | parameter :: rest => do
      `(Complexity.Language.ArgumentRepresentation.cons
        $(← termOfExpr parameter.type.representation) $(← inputRepresentation rest))

private def inputFields (count : Nat) (input : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  let mut fields := #[]
  let mut rest := input
  for index in [:count] do
    if index + 1 == count then fields := fields.push rest
    else
      fields := fields.push (← `(Prod.fst $rest))
      rest ← `(Prod.snd $rest)
  return fields

private def refinementDeclarations (family : TSyntax `ident) (fn : Function) :
    TermElabM (Array Syntax) := do
  let program := mkIdentFrom family (family.getId ++ `program)
  let id := fieldName family fn.name "Id"
  let rawId := fieldName (sourceFamily family) fn.name "Id"
  let native := fieldName family fn.name
  let representation := fieldName family fn.name "_representation"
  let refinement := fieldName family fn.name "_refines"
  let equation := fieldName family fn.name "_action_rel_native"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let result ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeInputType ← inputType fn.parameters.toList
  let nativeResultType ← termOfExpr fn.result.nativeType
  let argumentRepresentation ← inputRepresentation fn.parameters.toList
  let resultRepresentation ← termOfExpr fn.result.representation
  let input := mkIdent (← mkFreshUserName `input)
  let heap := mkIdent (← mkFreshUserName `heap)
  let represented := mkIdent (← mkFreshUserName `represented)
  let fields ← inputFields fn.parameters.size ⟨input.raw⟩
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ fields
  let mut tactics := #[← `(tactic| intro $input:ident _),
    ← `(tactic| apply Complexity.Language.FunctionTotal.iff_eval.mpr)]
  for parameter in fn.parameters, index in [:fn.parameters.size] do
    let type := params[index]!
    let tail := params.extract (index + 1) params.size
    tactics := tactics.push (← `(tactic|
      refine (Complexity.Language.Env.forall_cons (τ := $type) (Γ := [$tail,*]) _).mpr ?_))
    tactics := tactics.push (← `(tactic| intro $(parameter.rawName):ident))
  tactics := tactics.push (← `(tactic| refine (Complexity.Language.Env.forall_nil _).mpr ?_))
  tactics := tactics.push (← `(tactic| intro $heap:ident $represented:ident))
  let mut relationRest : TSyntax `term := ⟨represented.raw⟩
  let mut rawRoots := #[]
  let mut relations := #[]
  for parameter in fn.parameters, index in [:fn.parameters.size] do
    let sourceRelation ← if index + 1 == fn.parameters.size then pure relationRest
      else `(And.left $relationRest)
    if index + 1 < fn.parameters.size then relationRest ← `(And.right $relationRest)
    let representation ← termOfExpr parameter.type.representation
    let field := fields[index]!
    let relation := parameter.relationName
    tactics := tactics.push (← `(tactic|
      have $relation:ident : ($representation).Rel $field $(parameter.rawName):ident $heap:ident :=
        $sourceRelation))
    match parameter.type with
    | .pure _ =>
        tactics := tactics.push (← `(tactic| change $field = $(parameter.rawName):ident at $relation:ident))
        tactics := tactics.push (← `(tactic| subst $(parameter.rawName):ident))
    | _ =>
        rawRoots := rawRoots.push (⟨parameter.rawName.raw⟩ : TSyntax `term)
        relations := relations.push (⟨relation.raw⟩ : TSyntax `term)
  let applied := fields ++ rawRoots ++ #[⟨heap.raw⟩] ++ relations
  let correct := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
  let returned := mkIdent (← mkFreshUserName `returned)
  let finish := mkIdent (← mkFreshUserName `finish)
  let executed := mkIdent (← mkFreshUserName `executed)
  let observed := mkIdent (← mkFreshUserName `observed)
  tactics := tactics.push (← `(tactic|
    obtain ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident, _⟩ := $correct))
  tactics := tactics.push (← `(tactic| exact ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident⟩))
  let idDeclaration ← `(command|
    abbrev $id:ident := $rawId:ident)
  let representationDeclaration ← `(command|
    /-- Ordinary arguments and the actual result observed in their real source heaps. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $nativeInputType (fun _ => $nativeResultType) { params := [$params,*], result := $result } :=
      Complexity.Language.FunctionRepresentation.ofResult $argumentRepresentation
        (fun _ => $resultRepresentation))
  let refinementDeclaration ← `(command|
    /-- Automatic correspondence for the same generated source function, without a machine budget. -/
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $id:ident $representation:ident (fun _ => True)
        (fun ($input:ident : $nativeInputType) => $nativeValue) := by
      $tactics:tactic*)
  return #[idDeclaration.raw, representationDeclaration.raw, refinementDeclaration.raw]

private def emitDeclarations (declarations : Array Syntax) : CommandElabM Unit :=
  elabCommand (mkNullNode declarations)

private def readImports (libraries : Array (TSyntax `ident)) : CommandElabM ImportedPrograms := do
  let mut imports : ImportedPrograms := {}
  for family in libraries do
    let program := mkIdentFrom family (family.getId ++ `program)
    let programName ← resolveGlobalConstNoOverload program
    if let some native := getNativeProgramInfo? (← getEnv) programName then
      imports := { imports with native := imports.native ++ native }
    else
      imports := { imports with source := imports.source.push (← getProgramInfo family) }
  return imports

private def registerNativeProgram (family rawFamily : TSyntax `ident) (functions : Array Function) :
    CommandElabM Unit := do
  let programName ← resolveGlobalConstNoOverload (mkIdentFrom family (family.getId ++ `program))
  let sourceProgramName ← resolveGlobalConstNoOverload (mkIdentFrom rawFamily (rawFamily.getId ++ `program))
  let headers ← functions.mapM fun fn => do
    let nativeName ← resolveGlobalConstNoOverload (fieldName family fn.name)
    let relation ← resolveGlobalConstNoOverload (fieldName family fn.name "_action_rel_native")
    let refinement ← resolveGlobalConstNoOverload (fieldName family fn.name "_refines")
    let equation ← if fn.hasExactEquation then
        some <$> resolveGlobalConstNoOverload (fieldName family fn.name "_action_eq_native")
      else pure none
    let preservingRelation ← if fn.preservesArrays then
        some <$> resolveGlobalConstNoOverload (fieldName family fn.name "_action_rel_native_preserving")
      else pure none
    pure ({
      sourceFamily := sourceProgramName.getPrefix
      sourceName := fn.name.getId
      nativeName
      parameters := fn.parameters.map (fun parameter => (parameter.name.getId, parameter.type))
      result := fn.result
      equation
      relation
      refinement
      preservingRelation } : NativeFunctionInfo)
  modifyEnv fun env => nativeProgramInfoExt.addEntry env (programName, headers)

private def elaborate (family : TSyntax `ident) (libraries : Array (TSyntax `ident))
    (functions : Array (TSyntax `sourceFunction)) : CommandElabM Unit := do
  let imports ← readImports libraries
  let prepared ← liftTermElabM do
    let (_, state) ← (functions.forM (prepareFunction family imports)).run {}
    return state
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
  let rawFamily := sourceFamily family
  let operationFamilies := prepared.folds.map (·.operation.family) ++
    prepared.constructors.map (·.operation.family) ++ prepared.deconstructors.map (·.operation.family) ++
    prepared.emptinessTests.map (·.operation.family) ++ prepared.calledFamilies
  let rawCommand ← if operationFamilies.isEmpty then
      `(command| source_program $rawFamily:ident where
        $rawFunctions:sourceFunction*)
    else
      `(command| source_program $rawFamily:ident importing $operationFamilies:ident,* where
        $rawFunctions:sourceFunction*)
  elabCommand rawCommand
  let signatures := mkIdentFrom family (family.getId ++ `signatures)
  let program := mkIdentFrom family (family.getId ++ `program)
  let rawSignatures := mkIdentFrom family (rawFamily.getId ++ `signatures)
  let rawProgram := mkIdentFrom family (rawFamily.getId ++ `program)
  emitDeclarations #[
    (← `(command| abbrev $signatures:ident := $rawSignatures:ident)).raw,
    (← `(command| def $program:ident : Complexity.Language.Program $signatures:ident := $rawProgram:ident)).raw]
  for fn in prepared.functions do
    elabCommand (← liftTermElabM (nativeDeclaration family fn))
    if fn.hasExactEquation then elabCommand (← liftTermElabM (equationDeclaration family fn))
    if fn.preservesArrays then elabCommand (← liftTermElabM (relationDeclaration family fn true))
    elabCommand (← liftTermElabM (relationDeclaration family fn))
    emitDeclarations (← liftTermElabM (refinementDeclarations family fn))
  registerNativeProgram family rawFamily prepared.functions

/-- Generate native mathematical functions and checked node-backed source
implementations from the same immutable blocks and registered operations. -/
syntax (name := nativeSourceProgram) "source_program " "(" &"native" ") " ident " where" ppLine
  many1Indent(sourceFunction) : command

/-- Import completed native operation families or verified pure source callbacks.
Native callbacks retain their actual source identities and heap-indexed relations. -/
syntax (name := importingNativeSourceProgram)
  "source_program " "(" &"native" ") " ident " importing " ident,+ " where" ppLine
  many1Indent(sourceFunction) : command

elab_rules : command
  | `(command| source_program (native) $family:ident where $functions:sourceFunction*) =>
      elaborate family #[] functions
  | `(command| source_program (native) $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => elaborate family libraries.getElems functions

end Complexity.Language.Syntax.Represented
