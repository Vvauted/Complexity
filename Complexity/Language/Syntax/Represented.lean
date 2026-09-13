/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.Syntax.Represented.Types
import Complexity.Language.Syntax.Represented.Imports
import Complexity.Language.Buffer.Copy.Native
import Complexity.Language.Buffer.RepresentedCopy
import Complexity.Language.List.Fold.Native
import Complexity.Language.List.Cons.Native
import Complexity.Language.Representation.Preservation
import Complexity.Language.List.Uncons.Native
import Complexity.Language.List.IsEmpty.Native
import Complexity.Language.Range.Fold

/-!
# Native mathematical views of represented source operations

This frontend retains ordinary mathematical types alongside actual source types.
Heap-backed arrays and lists carry relations, not heap-independent encodings.
Mutable local versions, conditionals and normal finite ranges compose the same
registered operations and their checked heap relations. A finite range lowers
to the shared source while and real body calls; its mathematical fold is never
a runtime primitive. Nonlocal loop exits and mutable-name shadowing are not yet
supported by this correspondence generator.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

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
  | unary (operation : TSyntax `term) (argument : Observation)
  | binary (operation : TSyntax `term) (left right : Observation)
  | arraySize (array : Observation)

private structure RetainedObservation where
  name : Name
  type : NativeType
  proof : TSyntax `term

private structure BindingModel where
  model : TSyntax `term
  rawModel : TSyntax `term
  observation : Observation := .refl

private structure Binding extends Parameter where
  model? : Option BindingModel := none
  mutable : Bool := false

private structure Callback where
  sourceFamily : Name
  sourceName : Name
  nativeName : Name
  accumulator : NativeType
  kind : CellTy
  relation : Option Name := none

private structure OperationModel where
  native : TSyntax `term
  equation : Option (TSyntax `ident)
  relation : TSyntax `ident
  refinement : TSyntax `ident
  preservingRelation : Option (TSyntax `ident) := none
  /-- Internal finite-range helpers require their actual stride to be positive. -/
  positiveStride : Option Nat := none

/-- Actual source identity and mathematical types do not require a total-function
model. Model names are checked before they enter the public function registry. -/
private structure Operation where
  family : TSyntax `ident
  sourceName : Name
  inputs : Array NativeType
  result : NativeType
  model? : Option OperationModel := none
  /-- Proof-side observation only; the source call still uses `sourceName`. -/
  actionName : Option Name := none

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

private structure ValueModel extends BindingModel where
  native : TSyntax `term

private structure Value where
  type : NativeType
  raw : TSyntax `term
  model? : Option ValueModel := none

/-- Absence propagates through source preparation, without catching elaboration
or correspondence failures. -/
private def mapModelsM {α β γ : Type} (left : Option α) (right : Option β)
    (f : α → β → TermElabM γ) : TermElabM (Option γ) := do
  match left, right with
  | some left, some right => return some (← f left right)
  | _, _ => return none

private def Value.requireModel (value : Value) : TermElabM ValueModel := do
  let some model := value.model?
    | throwError "internal correspondence construction requires a prepared value model"
  return model

private def Binding.requireModel (binding : Binding) : TermElabM BindingModel := do
  let some model := binding.model?
    | throwError "internal correspondence construction requires a prepared binding model"
  return model

private def Operation.requireModel (operation : Operation) : TermElabM OperationModel := do
  let some model := operation.model?
    | throwError "internal correspondence construction requires a prepared operation model"
  return model

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
      (build : TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
      (nativeBuild : Option (TSyntax `term → TSyntax `term → TermElabM (TSyntax `term)) := none) := do
    let left ← value scope left
    let right ← value scope right
    let inputSyntax := input
    let input ← resolveType input
    expect stx input left.type
    expect stx input right.type
    let first := mkIdent (← mkFreshUserName `left)
    let second := mkIdent (← mkFreshUserName `right)
    let nativeBuild := nativeBuild.getD build
    let operationBody ← nativeBuild ⟨first.raw⟩ ⟨second.raw⟩
    let operation ← `(fun ($first:ident $second:ident : $inputSyntax) => $operationBody)
    return ({
      type := ← resolveType output, raw := ← build left.raw right.raw,
      model? := ← mapModelsM left.model? right.model? fun left right => do
        return {
          native := ← nativeBuild left.native right.native
          model := ← nativeBuild left.model right.model
          rawModel := ← nativeBuild left.rawModel right.rawModel
          observation := .binary operation left.observation right.observation } } : Value)
  let comparison (left right : TSyntax `term)
      (build : TSyntax `term → TSyntax `term → TermElabM (TSyntax `term)) := do
    binary left right (← `(Nat)) (← `(Bool)) build
      (some fun left right => do `(decide $(← build left right)))
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
      raw := apply pair.raw
      model? := pair.model?.map fun model => {
        native := apply model.native
        model := apply model.model, rawModel := apply model.rawModel
        observation := .projection pair.type.isPure first model.observation } } : Value)
  let projectRecord (expression : TSyntax `term) (fieldName : Name) := do
    let record ← value scope expression
    if let .array _ := record.type then
      unless fieldName == `size || fieldName == ``Array.size do
        throwErrorAt expression "unknown native array field '{fieldName}'"
      return ({
        type := ← resolveType (← `(Nat))
        raw := ← `(($(record.raw)).$(mkIdent `length):ident)
        model? := ← record.model?.mapM fun model => do
          return {
            rawModel := ← `(($(model.rawModel)).length)
            native := ← `(Array.size $(model.native))
            model := ← `(Array.size $(model.model))
            observation := .arraySize model.observation } } : Value)
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
      model? := ← record.model?.mapM fun model => do
        return {
          rawModel := ← fieldProjection fields.size index model.rawModel
          native := Lean.Syntax.mkCApp field.projection #[model.native]
          model := Lean.Syntax.mkCApp field.projection #[model.model]
          observation := fieldObservation fields.size index model.observation } } : Value)
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
    let models : Option (Array ValueModel) := values.mapM (·.model?)
    return ({
      type
      raw := ← fieldsTerm (values.map (·.raw)).toList
      model? := ← models.mapM fun models => do
        return {
          rawModel := ← fieldsTerm (models.map (·.rawModel)).toList
          native := Lean.Syntax.mkCApp constructor (models.map (·.native))
          model := Lean.Syntax.mkCApp constructor (models.map (·.model))
          observation := fieldsObservation (models.map (·.observation)).toList } } : Value)
  match stx with
  | `(($expression:term)) => value scope expression expected
  | `(($expression:term : $type:term)) =>
      let expected ← resolveType type
      if let .list kind := expected then
        if let `([]) := expression then
          return {
            type := expected, raw := ← `(none)
            model? := some {
              native := stx
              model := stx, rawModel := ← `(none), observation := .nil kind } }
      if let .option payload := expected then
        if let `(none) := expression then
          return {
            type := expected, raw := ← `(none)
            model? := some {
              native := stx
              model := stx, rawModel := ← `(none), observation := .none payload } }
      let result ← value scope expression (some expected)
      expect type expected result.type
      return result
  | `($name:ident) =>
      if name.getId == `true || name.getId == `false then
        return {
          type := ← resolveType (← `(Bool)), raw := stx
          model? := some { native := stx, model := stx, rawModel := stx } }
      if let .str receiver field := name.getId then
        if scope.any (fun binding => binding.name.getId.isPrefixOf receiver) then
          return ← projectRecord ⟨(mkIdent receiver).raw⟩ (Name.mkSimple field)
      let parameter ← lookup scope name
      return {
        type := parameter.type, raw := stx
        model? := parameter.model?.map fun model => { toBindingModel := model, native := stx } }
  | `($(pair).$field:fieldIdx) =>
      match field.raw.isFieldIdx? with
      | some 1 => project pair true
      | some 2 => project pair false
      | _ => throwError "a native product projection must select field 1 or 2"
  | `(Prod.fst $pair:term) => project pair true
  | `(Prod.snd $pair:term) => project pair false
  | `($receiver:term.$field:ident) => projectRecord receiver field.getId
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
        type := .option result.type, raw := ← `(some $(result.raw))
        model? := ← result.model?.mapM fun model => do
          return {
            native := ← `(some $(model.native)), model := ← `(some $(model.model))
            rawModel := ← `(some $(model.rawModel)), observation := .some model.observation } }
  | `($_:num) => return {
      type := ← resolveType (← `(Nat)), raw := stx
      model? := some { native := stx, model := stx, rawModel := stx } }
  | `(()) => return {
      type := ← resolveType (← `(Unit)), raw := stx
      model? := some { native := stx, model := stx, rawModel := stx } }
  | `(($left, $right)) =>
      let left ← value scope left
      let right ← value scope right
      let type ← mkAppM ``Prod #[left.type.nativeType, right.type.nativeType]
      let type ← resolveNativeType type
      return {
        type,
        raw := ← `(($(left.raw), $(right.raw)))
        model? := ← mapModelsM left.model? right.model? fun left right => do
          return {
            native := ← `(($(left.native), $(right.native)))
            model := ← `(($(left.model), $(right.model)))
            rawModel := ← `(($(left.rawModel), $(right.rawModel)))
            observation := .pair type.isPure left.observation right.observation } }
  | `($left + $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a + $b)
  | `($left * $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a * $b)
  | `($left - $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a - $b)
  | `($left / $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a / $b)
  | `($left % $right) => binary left right (← `(Nat)) (← `(Nat)) fun a b => `($a % $b)
  | `($left < $right) => comparison left right fun a b => `($a < $b)
  | `($left ≤ $right) | `($left <= $right) => comparison left right fun a b => `($a ≤ $b)
  | `($left > $right) => comparison left right fun a b => `($a > $b)
  | `($left ≥ $right) | `($left >= $right) => comparison left right fun a b => `($a ≥ $b)
  | `($left == $right) | `($left = $right) | `($left != $right) | `($left ≠ $right) =>
      let leftValue ← value scope left
      let input ← if ← isDefEq leftValue.type.nativeType (mkConst ``Bool) then `(Bool) else `(Nat)
      match stx with
      | `($_ == $_) | `($_ = $_) =>
          binary left right input (← `(Bool)) (fun a b => `($a == $b))
            (some fun a b => `(decide ($a = $b)))
      | _ =>
          binary left right input (← `(Bool)) (fun a b => `($a != $b))
            (some fun a b => `(decide ($a ≠ $b)))
  | `($left && $right) => binary left right (← `(Bool)) (← `(Bool)) fun a b => `($a && $b)
  | `($left || $right) => binary left right (← `(Bool)) (← `(Bool)) fun a b => `($a || $b)
  | `(!$expression) =>
      let argument ← value scope expression
      expect expression (← resolveType (← `(Bool))) argument.type
      return { argument with
        raw := ← `(!$(argument.raw))
        model? := ← argument.model?.mapM fun model => do
          return {
            native := ← `(!$(model.native))
            model := ← `(!$(model.model)), rawModel := ← `(!$(model.rawModel))
            observation := .unary (← `(Bool.not)) model.observation } }
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

private structure RangeRegistration where
  callback : Operation
  embedding : TSyntax `term
  mutableStep : TSyntax `term
  initialMutable : TSyntax `term
  indices : TSyntax `term
  emptyState : Bool

private structure FunctionModel where
  nativeBody : TSyntax `term
  calls : Array Trace
  returned : Value
  termination : TSyntax ``Lean.Parser.Termination.suffix
  recursive : Bool := false
  range : Option RangeRegistration := none

private structure Function where
  name : TSyntax `ident
  parameters : Array Parameter
  result : NativeType
  rawBody : TSyntax `term
  model? : Option FunctionModel := none
  exposed : Bool := true

private def Function.hasExactEquation (fn : Function) : Bool :=
  match fn.model? with
  | none => false
  | some model =>
    let scalarArguments := fn.parameters.all fun parameter =>
      match parameter.type with | .pure _ | .list _ => true | _ => false
    match fn.result with
    | .pure _ => model.range.isNone && !model.recursive && scalarArguments && model.calls.all fun
        | .call invocation => invocation.operation.model?.any (·.equation.isSome)
        | _ => false
    | _ => false

private partial def Trace.preservesArrays : Trace → Bool
  | .call invocation => invocation.operation.model?.any (·.preservingRelation.isSome)
  | .conditional _ yes no _ _ _ => yes.all Trace.preservesArrays && no.all Trace.preservesArrays
  | .optionMatch _ _ absent present _ _ _ =>
      absent.all Trace.preservesArrays && present.all Trace.preservesArrays

private def Function.preservesArrays (fn : Function) : Bool :=
  match fn.model? with
  | none => false
  | some model => match model.range with
    | some range => range.callback.model?.any (·.preservingRelation.isSome)
    | none => fn.hasExactEquation || model.calls.all Trace.preservesArrays

private structure Preparation where
  folds : Array FoldRegistration := #[]
  constructors : Array ConsRegistration := #[]
  deconstructors : Array UnconsRegistration := #[]
  emptinessTests : Array IsEmptyRegistration := #[]
  functions : Array Function := #[]
  calledFamilies : Array (TSyntax `ident) := #[]
  current : Option Operation := none
  currentRecursive : Bool := false
  declarationNames : NameSet := {}
  declarationGenerator : Lean.DeclNameGenerator := {}

private abbrev PrepareM := StateT Preparation TermElabM

/-- Reserve family-local helper declarations before their bodies are emitted.
The generator sees public names only for naming purposes; declaration visibility
is unchanged. Explicit reservations also protect later user-written functions. -/
private partial def freshHelperName (kind : Name) : PrepareM (TSyntax `ident) := do
  let state ← get
  let (name, generator) := state.declarationGenerator.mkUniqueName
    ((← getEnv).setExporting true) kind
  modify fun state => { state with declarationGenerator := generator.next }
  if state.declarationNames.contains name then return ← freshHelperName kind
  modify fun state => { state with declarationNames := state.declarationNames.insert name }
  return mkIdent name

private def fieldName (family name : TSyntax `ident) (suffix : String := "") : TSyntax `ident :=
  mkIdentFrom name ((family.getId ++ name.getId).appendAfter suffix)

private def sourceFamily (family : TSyntax `ident) : TSyntax `ident :=
  mkIdentFrom family (family.getId ++ `Source)

private def functionOperation (family : TSyntax `ident) (fn : Function) : Operation := {
  family := sourceFamily family
  sourceName := fn.name.getId
  inputs := fn.parameters.map (·.type)
  result := fn.result
  model? := fn.model?.map fun model => {
    native := ⟨(fieldName family fn.name).raw⟩
    equation := if fn.hasExactEquation then some (fieldName family fn.name "_action_eq_native") else none
    relation := fieldName family fn.name "_action_rel_native"
    refinement := fieldName family fn.name "_refines"
    preservingRelation := if fn.preservesArrays then
      some (fieldName family fn.name "_action_rel_native_preserving") else none
    positiveStride := if model.range.isSome then some 2 else none } }

private def importedOperation (info : NativeFunctionInfo) : Operation := {
  family := mkIdent info.sourceFamily
  sourceName := info.sourceName
  inputs := info.parameters.map (·.2)
  result := info.result
  actionName := info.actionName
  model? := some {
    native := ⟨(mkCIdent info.nativeName).raw⟩
    equation := info.equation.map mkCIdent
    relation := mkCIdent info.relation
    refinement := mkCIdent info.refinement
    preservingRelation := info.preservingRelation.map mkCIdent } }

private def findImportedNative? (imports : ImportedPrograms) (name : TSyntax `ident) :
    TermElabM (Option NativeFunctionInfo) := do
  let resolved? ← try pure (some (← resolveGlobalConstNoOverload name)) catch _ => pure none
  let some resolved := resolved? | return none
  return imports.native.find? (fun info => info.nativeName == resolved)

private def findCallback (imports : ImportedPrograms)
    (name : TSyntax `ident) : TermElabM Callback := do
  let resolved ← resolveGlobalConstNoOverload name
  let pureView (family : Name) (info : FunctionInfo) :=
    info.pure && (family ++ info.name == resolved ||
      info.model?.any (fun model => model.name == resolved))
  -- Direct pure calls also have a relational adapter. A fold keeps the stronger
  -- original unchanged-heap contract and its existing compiled equation API.
  let preferPure := imports.source.any fun (family, functions) => functions.any (pureView family)
  if let some info := imports.native.find? (fun info => info.nativeName == resolved && !preferPure) then
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
      if pureView family info then
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
    inputs := #[callback.accumulator, .list callback.kind]
    result := callback.accumulator
    model? := some {
      native
      equation := if callback.relation.isNone then
        some (mkIdentFrom name (operationFamily.getId ++ `fold_eq)) else none
      relation := mkIdentFrom name (operationFamily.getId ++ `fold_rel)
      refinement := mkIdentFrom name (operationFamily.getId ++ `fold_refines) } }
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
    inputs := #[head, .list kind]
    result := .list kind
    model? := some {
      native := ⟨(mkCIdent ``List.cons).raw⟩
      equation := none
      relation := mkIdentFrom family (operationFamily.getId ++ `cons_rel)
      refinement := mkIdentFrom family (operationFamily.getId ++ `cons_refines) } }
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
    family := operationFamily, sourceName := `uncons
    inputs := #[.list kind], result := .option (.prod head (.list kind))
    model? := some {
      native, equation := none
      relation := mkIdentFrom family (operationFamily.getId ++ `uncons_rel)
      refinement := mkIdentFrom family (operationFamily.getId ++ `uncons_refines) } }
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
    inputs := #[.list kind], result,
    model? := some {
      native := ⟨(mkCIdent ``List.isEmpty).raw⟩
      equation := some (mkIdentFrom family (operationFamily.getId ++ `isEmpty_eq))
      relation := mkIdentFrom family (operationFamily.getId ++ `isEmpty_rel)
      refinement := mkIdentFrom family (operationFamily.getId ++ `isEmpty_refines) } }
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
    inputs := if append then #[.array .nat, .array .nat] else #[.array .nat]
    result := .array .nat
    model? := some {
      native
      equation := none
      relation := mkCIdent (if append then ``Complexity.Language.Buffer.Copy.append_eval_exists
        else ``Complexity.Language.Buffer.Copy.copy_eval_exists)
      refinement := mkCIdent (if append then ``Complexity.Language.Buffer.append_array_refines
        else ``Complexity.Language.Buffer.copy_array_refines)
      preservingRelation := some (mkCIdent (if append then
        ``Complexity.Language.Buffer.Copy.append_eval_exists_preserving
        else ``Complexity.Language.Buffer.Copy.copy_eval_exists_preserving)) } }

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
      if (← get).current.any (fun operation => operation.sourceName == called.getId) then
        return some expression
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

/-- A value branch and a block with a final return share the same lowering. -/
private def returnElements (body : TSyntax `term) : TermElabM (Array (TSyntax `doElem)) :=
  match body with
  | `(do $elements:doSeq) => pure (getDoElems elements)
  | _ => return #[← `(doElem| return $body:term)]

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

private def needsGuardedJoin : Ty → Bool
  | .buffer _ | .node _ => true
  | .prod left right => needsGuardedJoin left || needsGuardedJoin right
  | _ => false

/-- A result slot never invents a heap handle. An optional slot is initialized
empty and receives only the value computed by the selected branch. -/
private structure JoinSlot where
  name : TSyntax `ident
  type : TSyntax `term
  initial : TSyntax `term
  guarded : Bool

private def makeJoinSlot (name : TSyntax `ident) (type : Ty) : TermElabM JoinSlot := do
  let rawType ← rawTypeTerm type
  if needsGuardedJoin type then
    return { name, type := ← `(Option $rawType), initial := ← `(none), guarded := true }
  return { name, type := rawType, initial := ← rawDefaultTerm type, guarded := false }

private partial def JoinSlot.branch (slot : JoinSlot) (elements : Array (TSyntax `doElem)) :
    TermElabM (TSyntax ``doSeq) := do
  let rec replace (stx : Syntax) : TermElabM Syntax := do
    if let `(doElem| return $value:term) := stx then
      let value ← if slot.guarded then `(some $value) else pure value
      return (← `(doElem| $(slot.name):ident := $value)).raw
    if let .node info kind args := stx then
      return .node info kind (← args.mapM replace)
    return stx
  return ⟨Lean.Elab.Term.Do.mkDoSeq (← elements.mapM fun element => replace element.raw)⟩

private def JoinSlot.continuation (slot : JoinSlot) (name : TSyntax `ident)
    (elements : Array (TSyntax `doElem)) : TermElabM (Array (TSyntax `doElem)) := do
  if slot.guarded then
    let absent : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩
    let present : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩
    return #[← `(doElem| match $(slot.name):ident with
      | none => $absent:doSeq
      | some $name:ident => $present:doSeq)]
  return #[← `(doElem| let $name:ident : $(slot.type) := $(slot.name):ident)] ++ elements

/-- Shadowed locals are not accessible; distinct visible aliases remain distinct
state fields even when they happen to hold the same heap handle. -/
private def visibleBindings (scope : List Binding) : Array Binding := Id.run do
  let mut visible := #[]
  for binding in scope do
    unless visible.any (fun previous : Binding => previous.name.getId == binding.name.getId) do
      visible := visible.push binding
  return visible

private partial def stateType (bindings : List Binding) : TermElabM (TSyntax `term) :=
  match bindings with
  | [] => `(Unit)
  | [binding] => termOfExpr binding.type.nativeType
  | binding :: rest => do `($(← termOfExpr binding.type.nativeType) × $(← stateType rest))

private def stateValue (bindings : Array Binding) : TermElabM (TSyntax `term) :=
  fieldsTerm (bindings.map (fun binding => (⟨binding.name.raw⟩ : TSyntax `term))).toList

private def returnedState (bindings : Array Binding) (initial : TSyntax `ident) :
    TermElabM (TSyntax `term) := do
  let fields ← bindings.mapIdxM fun index binding =>
    if binding.mutable then pure (⟨binding.name.raw⟩ : TSyntax `term)
    else fieldProjection bindings.size index ⟨initial.raw⟩
  fieldsTerm fields.toList

/-- Mathematical loop coordinates contain only locals that the body can update. -/
private def mutableState (bindings : Array Binding) (state : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut fields := #[]
  for binding in bindings, index in [:bindings.size] do
    if binding.mutable then fields := fields.push (← fieldProjection bindings.size index state)
  fieldsTerm fields.toList

/-- Captures are closed over at loop entry, not selected again from each step's
mathematical result. The actual source accumulator still contains every field. -/
private def packMutableState (bindings : Array Binding) (captured mutable : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let count := (bindings.filter (·.mutable)).size
  let mut nextMutable := 0
  let mut fields := #[]
  for binding in bindings, index in [:bindings.size] do
    if binding.mutable then
      fields := fields.push (← fieldProjection count nextMutable mutable)
      nextMutable := nextMutable + 1
    else fields := fields.push (← fieldProjection bindings.size index captured)
  fieldsTerm fields.toList

/-- Normal range bodies and statement branches do not erase nonlocal exits.
Their eventual extension needs an explicit control result in the source iterator. -/
private partial def requireNormalBlock (stx : Syntax) : TermElabM Unit := do
  let localBinding := match stx with
    | `(doElem| let $_:ident $[: $_:term]? := $_:term) |
      `(doElem| let $_:ident $[: $_:term]? ← $_:term) |
      `(doElem| let $_:ident $[: $_:term]? ← $_:doElem) |
      `(doElem| let mut $_:ident $[: $_:term]? := $_:term) |
      `(doElem| let mut $_:ident $[: $_:term]? ← $_:term) |
      `(doElem| let mut $_:ident $[: $_:term]? ← $_:doElem) => true
    | _ => false
  -- A return inside a bound `do` expression belongs to that expression.
  if localBinding then return ()
  let isExit := match stx with
    | `(doElem| return $_:term) | `(doElem| return) |
      `(doElem| break) | `(doElem| continue) => true
    | _ => false
  if isExit then
    throwErrorAt stx "this finite native block does not yet support return, break or continue"
  if let .node _ _ arguments := stx then arguments.forM requireNormalBlock

private def parameterBinding (name : TSyntax `ident) (type : NativeType) : TermElabM Binding := do
  let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
  let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
  return {
    name, type, rawName, relationName
    model? := some {
      model := ⟨name.raw⟩
      rawModel := if type.isPure then ⟨name.raw⟩ else ⟨rawName.raw⟩
      observation := if type.isPure then .refl else .named relationName.getId } }

private def restoreState (bindings : Array Binding) (state : TSyntax `ident)
    (existing : Bool := false) :
    TermElabM (Array (TSyntax `doElem)) := do
  let mut elements := #[]
  for binding in bindings, index in [:bindings.size] do
    if existing && !binding.mutable then continue
    let field ← fieldProjection bindings.size index ⟨state.raw⟩
    let type ← termOfExpr binding.type.nativeType
    let element ← if existing then
        `(doElem| $(binding.name):ident := $field)
      else if binding.mutable then
        `(doElem| let mut $(binding.name):ident : $type := $field)
      else `(doElem| let $(binding.name):ident : $type := $field)
    elements := elements.push element
  return elements

private partial def sequence (family : TSyntax `ident)
    (imports : ImportedPrograms) (resultType : NativeType)
    (scope : List Binding) (elements : List (TSyntax `doElem))
    (bindingMutable : Bool := false) :
    PrepareM (Array (TSyntax `doElem) × Option (Array (TSyntax `doElem)) ×
      Option (Array Trace) × Value) := do
  let bindAndContinue (binding : Binding) (raw : TSyntax `doElem)
      (native : Option (TSyntax `doElem)) (calls : Option (Array Trace))
      (rest : List (TSyntax `doElem)) := do
    let binding := { binding with mutable := bindingMutable }
    let (rawRest, nativeRest, later, returned) ← sequence family imports resultType (binding :: scope) rest
    return (#[raw] ++ rawRest,
      (fun native rest => #[native] ++ rest) <$> native <*> nativeRest,
      (· ++ ·) <$> calls <*> later, returned)
  match elements with
  | [] => throwError "every native source function must end with a return"
  | element :: rest => withRef element do
    -- Static local versions lower to actual source copies. The ordinary source
    -- equation is checked against the relational trace after every version change.
    if let `(doElem| let mut $name:ident $[: $annotation:term]? := $expression:term) := element then
      if (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
        throwErrorAt name "shadowing a mutable native local is not yet supported; assign it or use a fresh name"
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? := $expression)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $expression:term) := element then
      if (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
        throwErrorAt name "shadowing a mutable native local is not yet supported; assign it or use a fresh name"
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      if (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
        throwErrorAt name "shadowing a mutable native local is not yet supported; assign it or use a fresh name"
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| $name:ident := $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type := $expression)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| $name:ident ← $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $expression:term)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| $name:ident ← $rhs:doElem) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $rhs:doElem)
      return ← sequence family imports resultType scope (normalized :: rest) true
    if let `(doElem| for $pattern:term in $collection:term do $body:doSeq) := element then
      let index ← match pattern with
        | `($name:ident) => pure name
        | `(_) => pure (mkIdent (← mkFreshUserName `index))
        | _ => throwErrorAt pattern "a finite Nat range binds one index or _"
      requireNormalBlock body.raw
      let (start, stop, stride) ← match collection with
        | `([ : $stop ]) => pure (← `(0), stop, ← `(1))
        | `([ $start : $stop ]) => pure (start, stop, ← `(1))
        | `([ : $stop : $stride ]) => pure (← `(0), stop, stride)
        | `([ $start : $stop : $stride ]) => pure (start, stop, stride)
        | _ => throwErrorAt collection "represented for currently expects a finite Nat range"
      let captured := (visibleBindings scope).filter (fun binding => binding.name.getId != index.getId)
      let stateSyntax ← stateType captured.toList
      let stateNativeType ← resolveType stateSyntax
      let natType ← resolveType (← `(Nat))
      let bodyName ← freshHelperName `_rangeBody
      let rangeName ← freshHelperName `_rangeFold
      let cursor := mkIdent (← mkFreshUserName `rangeIndex)
      let initial := mkIdent (← mkFreshUserName `rangeState)
      let indexBinding ← parameterBinding cursor natType
      let stateBinding ← parameterBinding initial stateNativeType
      let bodyElements := (← restoreState captured initial) ++
        #[← `(doElem| let $index:ident : Nat := $cursor:ident)] ++ getDoElems body ++
        #[← `(doElem| return $(← returnedState captured initial))]
      let previousCurrent := (← get).current
      let previousRecursive := (← get).currentRecursive
      -- A loop helper is a genuine separately called source function. Calling
      -- its enclosing recursive function would require a mutual descent proof.
      modify fun state => { state with current := none, currentRecursive := false }
      let (bodyRaw, bodyNative, bodyCalls, bodyReturned) ← sequence family imports stateNativeType
        [stateBinding, indexBinding] bodyElements.toList
      modify fun state => { state with current := previousCurrent, currentRecursive := previousRecursive }
      let helper : Function := {
        name := bodyName, parameters := #[indexBinding.toParameter, stateBinding.toParameter]
        result := stateNativeType, rawBody := ← doTerm bodyRaw
        model? := ← mapModelsM bodyNative bodyCalls fun native calls => do
          return {
            nativeBody := ← doTerm native, calls, returned := bodyReturned
            termination := ← `(Lean.Parser.Termination.suffix|) }
        exposed := false }
      modify fun state => { state with functions := state.functions.push helper }
      let startName := mkIdent (← mkFreshUserName `rangeStart)
      let stopName := mkIdent (← mkFreshUserName `rangeStop)
      let strideName := mkIdent (← mkFreshUserName `rangeStride)
      let startBinding ← parameterBinding startName natType
      let stopBinding ← parameterBinding stopName natType
      let strideBinding ← parameterBinding strideName natType
      let next := mkIdent (← mkFreshUserName `rangeNext)
      let rawStateType ← rawTypeTerm stateNativeType.coreTy
      let bodyNativeName := fieldName family bodyName
      let indices ← `(List.range' $startName:ident
        (($stopName:ident - $startName:ident + $strideName:ident - 1) / $strideName:ident)
        $strideName:ident)
      let mutableType ← stateType (captured.filter (·.mutable)).toList
      let mutableName := mkIdent (← mkFreshUserName `mutableState)
      let stepIndex := mkIdent (← mkFreshUserName `index)
      let packedMutable ← packMutableState captured ⟨initial.raw⟩ ⟨mutableName.raw⟩
      let embedding ← `(fun ($mutableName:ident : $mutableType) => $packedMutable)
      let nextState ← `($bodyNativeName:ident $stepIndex:ident $packedMutable)
      let nextMutable ← mutableState captured nextState
      let mutableStep ← `(fun ($mutableName:ident : $mutableType) ($stepIndex:ident : Nat) => $nextMutable)
      let initialMutable ← mutableState captured ⟨initial.raw⟩
      let nativeFold ← `(($indices).foldl $mutableStep $initialMutable)
      let nativeResult := Lean.Syntax.mkApp embedding #[nativeFold]
      let wrapper : Function := {
        name := rangeName
        parameters := #[startBinding.toParameter, stopBinding.toParameter,
          strideBinding.toParameter, stateBinding.toParameter]
        result := stateNativeType
        rawBody := ← `(do
          let mut $cursor:ident : Nat := $startName:ident
          let mut rangeAccumulator : $rawStateType := $initial:ident
          while $cursor:ident < $stopName:ident do
            let $next:ident : $rawStateType ← $bodyName:ident $cursor:ident rangeAccumulator
            rangeAccumulator := $next:ident
            $cursor:ident := $cursor:ident + $strideName:ident
          return rangeAccumulator)
        model? := ← helper.model?.mapM fun _ => do
          return {
            nativeBody := ← `(do return $nativeResult)
            calls := #[], returned := bodyReturned, termination := ← `(Lean.Parser.Termination.suffix|)
            range := some {
              callback := functionOperation family helper
              embedding, mutableStep, initialMutable, indices, emptyState := captured.isEmpty } }
        exposed := false }
      modify fun state => { state with functions := state.functions.push wrapper }
      let packed := mkIdent (← mkFreshUserName `rangeInput)
      let result := mkIdent (← mkFreshUserName `rangeOutput)
      let normalized := #[← `(doElem| let $packed:ident : $stateSyntax := $(← stateValue captured)),
        ← `(doElem| let $result:ident : $stateSyntax ←
          $rangeName:ident $start:term $stop:term $stride:term $packed:ident)] ++
        (← restoreState captured result true)
      return ← sequence family imports resultType scope (normalized.toList ++ rest)
    let statementConditional? ← match element with
      | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
          pure (some (condition, yes, no))
      | `(doElem| if $condition:term then $yes:doSeq) =>
          pure (some (condition, yes, (⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩ : TSyntax ``doSeq)))
      | _ => pure none
    if !rest.isEmpty then
      if let some (condition, yes, no) := statementConditional? then
        requireNormalBlock yes.raw
        requireNormalBlock no.raw
        let mutableBindings := (visibleBindings scope).filter (·.mutable)
        let stateSyntax ← stateType mutableBindings.toList
        let stateTerm ← stateValue mutableBindings
        let yesBody ← doTerm (getDoElems yes |>.push (← `(doElem| return $stateTerm)))
        let noBody ← doTerm (getDoElems no |>.push (← `(doElem| return $stateTerm)))
        let joined := mkIdent (← mkFreshUserName `mutableJoin)
        let normalized := #[← `(doElem| let $joined:ident : $stateSyntax ←
          (if $condition:term then $yesBody:term else $noBody:term))] ++
          (← restoreState mutableBindings joined true)
        return ← sequence family imports resultType scope (normalized.toList ++ rest)
    if rest.isEmpty then
      let terminal? ← match element with
        | `(doElem| if $test:term then $yes:doSeq else $no:doSeq) => do
            let yesTerm ← branchTerm yes
            let noTerm ← branchTerm no
            pure (some (← `(if $test:term then $yesTerm:term else $noTerm:term)))
        | `(doElem| match $discriminant:term with
            | $first:term => $firstBody:doSeq
            | $second:term => $secondBody:doSeq) => do
            let firstTerm ← branchTerm firstBody
            let secondTerm ← branchTerm secondBody
            pure (some (← `(match $discriminant:term with
              | $first:term => $firstTerm:term
              | $second:term => $secondTerm:term)))
        | `(doElem| return $expression:term) =>
            pure (if (conditionalParts? expression).isSome || (matchParts? expression).isSome then
              some expression else none)
        | _ => pure none
      if let some expression := terminal? then
        let temporary := mkIdent (← mkFreshUserName `branchResult)
        let type ← termOfExpr resultType.nativeType
        return ← sequence family imports resultType scope [
          ← `(doElem| let $temporary:ident : $type ← ($expression:term)),
          ← `(doElem| return $temporary:ident)]
    -- An unparenthesized `if` after `←` is a `doIf`, not a term.
    -- Normalize that parser shape before the shared typed conditional path.
    if let `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      if let `(doElem| if $test:term then $yes:doSeq else $no:doSeq) := rhs then
        let yesTerm ← branchTerm yes
        let noTerm ← branchTerm no
        let expression ← `(if $test:term then $yesTerm:term else $noTerm:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence family imports resultType scope (normalized :: rest) bindingMutable
      if let `(doElem| match $discriminant:term with
          | $first:term => $firstBody:doSeq
          | $second:term => $secondBody:doSeq) := rhs then
        let firstBody ← branchTerm firstBody
        let secondBody ← branchTerm secondBody
        let expression ← `(match $discriminant:term with
          | $first:term => $firstBody:term
          | $second:term => $secondBody:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence family imports resultType scope (normalized :: rest) bindingMutable
    let binding? := match element with
      | `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term) =>
          some (name, annotation, expression)
      | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
          some (name, annotation, expression)
      | _ => none
    if let some (name, annotation, expression) := binding? then
      if !bindingMutable &&
          (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
        throwErrorAt name "shadowing a mutable native local is not yet supported; assign it or use a fresh name"
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
          let consElements ← returnElements consBody
          let inspected := mkIdent (← mkFreshUserName `listParts)
          let payload := mkIdent (← mkFreshUserName `listFields)
          let someElements := #[
            ← `(doElem| let $head:ident := $payload:ident.1),
            ← `(doElem| let $tail:ident := $payload:ident.2)] ++ consElements
          let someBody ← doTerm someElements
          let optionMatch ← `(match ($inspected:ident) with
            | none => $nilBody:term
            | some $payload:ident => $someBody:term)
          let read ← `(doElem| let $inspected:ident := List.uncons $matched:term)
          let select ← if bindingMutable then
              if (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
                `(doElem| $name:ident ← ($optionMatch:term))
              else `(doElem| let mut $name:ident : $annotation ← ($optionMatch:term))
            else `(doElem| let $name:ident : $annotation ← ($optionMatch:term))
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
        let noneElements ← returnElements noneBody
        let someElements ← returnElements someBody
        let payloadRaw := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_source"))
        let payloadRelation := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_represented"))
        let payload : Binding := {
          name := payloadName, type := payloadType, rawName := payloadRaw,
          relationName := payloadRelation
          model? := discriminant.model?.map fun _ => {
            model := ⟨payloadName.raw⟩, rawModel := ⟨payloadRaw.raw⟩
            observation := if payloadType.isPure then .refl else .named payloadRelation.getId } }
        let (noneRaw, noneNative, noneCalls, noneResult) ←
          sequence family imports selectedType scope noneElements.toList
        let (someRaw, someNative, someCalls, someResult) ←
          sequence family imports selectedType (payload :: scope) someElements.toList
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let joinSlot ← makeJoinSlot slot selectedType.coreTy
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let noneBlock ← joinSlot.branch noneRaw
        let someBlock ← joinSlot.branch someRaw
        let payloadNativeType ← termOfExpr payloadType.nativeType
        let choiceInputs := do
          let discriminant ← discriminant.model?
          let noneNative ← noneNative
          let someNative ← someNative
          let noneResult ← noneResult.model?
          let someResult ← someResult.model?
          pure (discriminant, noneNative, someNative, noneResult, someResult)
        let choice ← choiceInputs.mapM fun (discriminant, noneNative, someNative, noneResult, someResult) => do
          let noneNativeBody ← doTerm noneNative
          let someNativeBody ← doTerm someNative
          let nativeChoice ← `(Option.elim $(discriminant.native) (Id.run $noneNativeBody:term)
            (fun ($payloadName:ident : $payloadNativeType) => Id.run $someNativeBody:term))
          let model ← `(Option.elim $(discriminant.model) $(noneResult.model)
            (fun ($payloadName:ident : $payloadNativeType) => $(someResult.model)))
          pure (nativeChoice, ({
            model, rawModel := ⟨rawName.raw⟩
            observation := if selectedType.isPure then .refl else .named relationName.getId } : BindingModel))
        let binding : Binding := {
          name, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          mutable := bindingMutable }
        let (rawRest, nativeRest, later, returned) ←
          sequence family imports resultType (binding :: scope) rest
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $(joinSlot.type) := $(joinSlot.initial)),
          ← `(doElem| match $(discriminant.raw):term with
            | none => $noneBlock:doSeq
            | some $payloadName:ident => $someBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $name:ident : $nativeType := $nativeChoice)
        let calls : Option (Array Trace) := do
          let _ ← choice
          let noneCalls ← noneCalls
          let someCalls ← someCalls
          let later ← later
          pure (#[.optionMatch discriminant payload noneCalls someCalls noneResult someResult binding] ++ later)
        return (rawPrefix ++ (← joinSlot.continuation name rawRest),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest, calls, returned)
      if let some (test, yes, no) := conditionalParts? expression then
        let some annotation := annotation
          | throwErrorAt name "a native conditional binding requires an explicit result type"
        let selectedType ← resolveType annotation
        let condition ← value scope test
        expect test (← resolveType (← `(Bool))) condition.type
        let yesElements ← returnElements yes
        let noElements ← returnElements no
        let (yesRaw, yesNative, yesCalls, yesResult) ←
          sequence family imports selectedType scope yesElements.toList
        let (noRaw, noNative, noCalls, noResult) ←
          sequence family imports selectedType scope noElements.toList
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let joinSlot ← makeJoinSlot slot selectedType.coreTy
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let yesBlock ← joinSlot.branch yesRaw
        let noBlock ← joinSlot.branch noRaw
        let choiceInputs := do
          let condition ← condition.model?
          let yesNative ← yesNative
          let noNative ← noNative
          let yesResult ← yesResult.model?
          let noResult ← noResult.model?
          pure (condition, yesNative, noNative, yesResult, noResult)
        let choice ← choiceInputs.mapM fun (condition, yesNative, noNative, yesResult, noResult) => do
          let yesNativeBody ← doTerm yesNative
          let noNativeBody ← doTerm noNative
          let nativeChoice ← `(if $(condition.native) then Id.run $yesNativeBody:term
            else Id.run $noNativeBody:term)
          let model ← `(if $(condition.model) then $(yesResult.model) else $(noResult.model))
          pure (nativeChoice, ({
            model, rawModel := ⟨rawName.raw⟩
            observation := if selectedType.isPure then .refl else .named relationName.getId } : BindingModel))
        let binding : Binding := {
          name, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          mutable := bindingMutable }
        let (rawRest, nativeRest, later, returned) ←
          sequence family imports resultType (binding :: scope) rest
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $(joinSlot.type) := $(joinSlot.initial)),
          ← `(doElem| if $(condition.raw) then $yesBlock:doSeq else $noBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $name:ident : $nativeType := $nativeChoice)
        let calls : Option (Array Trace) := do
          let _ ← choice
          let yesCalls ← yesCalls
          let noCalls ← noCalls
          let later ← later
          pure (#[.conditional condition yesCalls noCalls yesResult noResult binding] ++ later)
        return (rawPrefix ++ (← joinSlot.continuation name rawRest),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest, calls, returned)
    match element with
    | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
        if let some call ← canonicalCall? imports scope expression then
          let binding ← `(doElem| let $name:ident $[: $annotation:term]? ← $call:term)
          return ← sequence family imports resultType scope (binding :: rest) bindingMutable
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceValue)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let binding ← if bindingMutable then
              if (scope.find? (fun binding => binding.name.getId == name.getId)).any (·.mutable) then
                `(doElem| $name:ident := $rewritten:term)
              else `(doElem| let mut $name:ident $[: $annotation:term]? := $rewritten:term)
            else `(doElem| let $name:ident $[: $annotation:term]? := $rewritten:term)
          return ← sequence family imports resultType scope (call :: binding :: rest)
        let result ← value scope expression (← annotation.mapM fun stx => return ← resolveType stx)
        if let some annotation := annotation then expect annotation (← resolveType annotation) result.type
        let rawType ← rawTypeTerm result.type.coreTy
        let nativeType ← termOfExpr result.type.nativeType
        bindAndContinue {
          name, type := result.type, rawName := name, relationName := name,
          model? := result.model?.map (·.toBindingModel) }
          (← `(doElem| let $name:ident : $rawType := $(result.raw)))
          (← result.model?.mapM fun model =>
            `(doElem| let $name:ident : $nativeType := $(model.native))) (some #[]) rest
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
              if let some operation := (← get).current.filter
                  (fun operation => operation.sourceName == called.getId) then
                modify fun state => { state with currentRecursive := true }
                pure (operation, arguments)
              else if let some fn := (← get).functions.find? (fun fn => fn.name.getId == called.getId) then
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
        let rawType ← rawTypeTerm operation.result.coreTy
        let nativeType ← termOfExpr operation.result.nativeType
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let models : Option (Array ValueModel) := arguments.mapM (·.model?)
        let callModel : Option (TSyntax `term × BindingModel) := do
          let operationModel ← operation.model?
          let arguments : Array ValueModel ← models
          let native := Lean.Syntax.mkApp operationModel.native (arguments.map (·.native))
          let model := Lean.Syntax.mkApp operationModel.native (arguments.map (·.model))
          pure (native, ({
            model, rawModel := ⟨rawName.raw⟩
            observation := if operation.result.isPure then .refl else .named relationName.getId } : BindingModel))
        let binding : Binding := {
          name, type := operation.result, rawName, relationName,
          model? := callModel.map (·.2) }
        bindAndContinue binding
          (← `(doElem| let $name:ident : $rawType ← $raw:term))
          (← callModel.mapM fun (native, _) => `(doElem| let $name:ident : $nativeType := $native))
          (callModel.map fun _ => #[.call ⟨operation, arguments, binding⟩]) rest
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
        let native ← result.model?.mapM fun model => do
          return #[← `(doElem| return $(model.native))]
        return (#[← `(doElem| return $(result.raw))], native, some #[], result)
    | _ => throwError "native source blocks support lets, let mut and assignment, registered calls, \
        conditional/match bindings, normal finite Nat ranges and a final return; \
        general while requires an explicit source contract, and break/continue are not supported here"

private def prepareFunction (family : TSyntax `ident)
    (imports : ImportedPrograms) (declaration : ParsedDeclaration) : PrepareM Unit := do
  let name := declaration.name
  let body := declaration.body
  let termination := declaration.termination
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
    let rawModel := if type.isPure then ⟨parameterName.raw⟩ else ⟨rawName.raw⟩
    let parameter : Parameter := { name := parameterName, type, rawName, relationName := relation }
    parsed := parsed.push parameter
    let binding : Binding := {
      toParameter := parameter,
      model? := some {
        model := ⟨parameterName.raw⟩, rawModel
        observation := if type.isPure then .refl else .named relation.getId } }
    scope := binding :: scope
  let elements ← match body with
    | `(do $elements:doSeq) => pure (getDoElems elements).toList
    | _ => pure [← `(doElem| return $body:term)]
  -- This header is only a recursive declaration target. The generated theorem
  -- proves its self calls with the same user-written descent argument; it is
  -- not registered as an already proved imported operation.
  let current : Operation := {
    family := sourceFamily family
    sourceName := name.getId
    inputs := parsed.map (·.type)
    result
    model? := some {
      native := ⟨(fieldName family name).raw⟩
      equation := none
      relation := fieldName family name "_action_rel_native"
      refinement := fieldName family name "_refines"
      preservingRelation := some (fieldName family name "_action_rel_native_preserving") } }
  modify fun state => { state with current := some current, currentRecursive := false }
  let (raw, native, calls, returned) ← sequence family imports result scope elements
  let recursive := (← get).currentRecursive
  let fn : Function := {
    name := name
    parameters := parsed
    result := result
    rawBody := ← doTerm raw
    model? := ← mapModelsM native calls fun native calls => do
      return {
        nativeBody := ← doTerm native, calls, returned, termination, recursive } }
  modify fun state => { state with
    functions := state.functions.push fn
    current := none
    currentRecursive := false }

private def kindTerm (kind : CellTy) : TermElabM (TSyntax `term) :=
  termOfExpr (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)

private def relationalFoldProofDeclarations (registration : FoldRegistration)
    (callbackRelation : Name) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let operationModel ← operation.requireModel
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
    theorem $(operationModel.relation):ident ($initial:ident : $accType) (values : List $headType)
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
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $foldId:ident (Complexity.Language.List.Fold.representation $represented $kind)
        (fun _ => True) (fun input => input.2.foldl $native:ident input.1) := by
      intro input _
      exact Complexity.Language.List.Fold.program_refines $contract:ident input
        (by intro processed head suffix equality; trivial))).raw
  return declarations

private def foldDeclarations (registration : FoldRegistration) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let operationModel ← operation.requireModel
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
  let some equation := operationModel.equation | throwError "registered pure fold is missing its exact equation"
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
    theorem $(operationModel.relation):ident (initial : $accType) (values : List $headType)
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
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
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
  let operationModel ← operation.requireModel
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
    theorem $(operationModel.relation):ident (head : $headType) (values : List $headType)
        (tail : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values tail heap) :
        ∃ returned finish,
          $cons:ident head tail heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.Representation.list $kind).Rel (head :: values) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Cons.eval_exists $kind head values tail heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $consId:ident (Complexity.Language.List.Cons.representation $kind)
        (fun _ => True) (fun input => input.1 :: input.2) :=
      Complexity.Language.List.Cons.refines $kind)).raw
  return declarations

private def unconsDeclarations (registration : UnconsRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let operationModel ← operation.requireModel
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
    theorem $(operationModel.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $uncons:ident root heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.List.Uncons.resultRepresentation $kind).Rel
            (values.head?.map (fun head => (head, values.tail))) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Uncons.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $unconsId:ident (Complexity.Language.List.Uncons.representation $kind)
        (fun _ => True) (fun values => values.head?.map (fun head => (head, values.tail))) :=
      Complexity.Language.List.Uncons.refines $kind)).raw
  return declarations

private def isEmptyDeclarations (registration : IsEmptyRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let isEmptyId := name `isEmptyId
  let isEmpty := name `isEmpty
  let observe := name `isEmpty_observe
  let some equation := operationModel.equation
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
    theorem $(operationModel.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $isEmpty:ident root heap = Part.some (.ok returned, finish) ∧
          Complexity.Language.Representation.bool.Rel values.isEmpty returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.IsEmpty.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $isEmptyId:ident (Complexity.Language.List.IsEmpty.representation $kind)
        (fun _ => True) (fun values => values.isEmpty) :=
      Complexity.Language.List.IsEmpty.refines $kind)).raw
  return declarations

private def rawFunction (fn : Function) : TermElabM (TSyntax `sourceFunction) := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← rawTypeTerm parameter.type.coreTy
    pure ({ name := parameter.name, type } : ParsedParameter)
  let result ← rawTypeTerm fn.result.coreTy
  let declaration : ParsedDeclaration := {
    name := fn.name, params := parameters, result, body := fn.rawBody
    termination := ← `(Lean.Parser.Termination.suffix|) }
  liftMacroM declaration.toSyntax

private def nativeDeclaration (family : TSyntax `ident) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← termOfExpr parameter.type.nativeType
    `(bracketedBinder| ($(parameter.name):ident : $type))
  let result ← termOfExpr fn.result.nativeType
  let name := fieldName family fn.name
  return (← `(command|
    /-- Ordinary mathematical function generated from the same represented source block. -/
    def $name:ident $parameters:bracketedBinder* : $result := Id.run $(model.nativeBody)
      $(model.termination):suffix)).raw

/-- The native model closes over fixed captures, while the source still passes
its full accumulator. The existing fold homomorphism checks that coordinate
change once for each prepared body; no execution or resource fact is changed. -/
private def rangeModelDeclaration (family : TSyntax `ident) (fn : Function)
    (_model : FunctionModel) (range : RangeRegistration) : TermElabM Syntax := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← termOfExpr parameter.type.nativeType
    `(bracketedBinder| ($(parameter.name):ident : $type))
  let some initial := fn.parameters[3]? | throwError "range helper is missing its state parameter"
  let stateType ← termOfExpr fn.result.nativeType
  let callback ← range.callback.requireModel
  let step ← `(fun (state : $stateType) (index : Nat) => $(callback.native) index state)
  let arguments := fn.parameters.map (fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term))
  let native := Lean.Syntax.mkApp ⟨(fieldName family fn.name).raw⟩ arguments
  let equation := fieldName family fn.name "_fold_eq_native"
  let mut proof := #[]
  if range.emptyState then proof := proof.push (← `(tactic| cases $(initial.name):ident))
  proof := proof.push (← `(tactic| exact List.foldl_hom $(range.embedding)
    (g₁ := $(range.mutableStep)) (g₂ := $step)
    (l := $(range.indices)) (init := $(range.initialMutable)) (by intro state index; rfl)))
  return (← `(command|
    /-- Fixed captures disappear from the mathematical accumulator only; the
    full-state source traversal is unchanged. -/
    theorem $equation:ident $parameters:bracketedBinder* :
        ($(range.indices)).foldl $step $(initial.name):ident = $native := by
      $proof:tactic*)).raw

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
  | .unary operation argument =>
      `(congrArg $operation $(← observationProof argument heap relations))
  | .binary operation left right =>
      `(congrArg₂ $operation $(← observationProof left heap relations)
        $(← observationProof right heap relations))
  | .arraySize array =>
      `(Complexity.Language.Buffer.Contents.size_eq $(← observationProof array heap relations))

private def observationAt (argument : Value) (heap : TSyntax `term)
    (relations : Array RetainedObservation) : TermElabM (TSyntax `term) := do
  observationProof (← argument.requireModel).observation heap relations

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
    | [] => do
        let model ← returned.requireModel
        `(pure $(resolveRaw model.rawModel known))
    | .call invocation :: rest => do
        let name := mkIdentFrom invocation.operation.family
          (invocation.operation.actionName.getD
            (invocation.operation.family.getId ++ invocation.operation.sourceName))
        let arguments ← invocation.arguments.mapM Value.requireModel
        let called := Lean.Syntax.mkApp ⟨name.raw⟩
          (arguments.map (fun argument => resolveRaw argument.rawModel known))
        let type ← actualTypeTerm invocation.result.type.coreTy
        let next ← traceAction rest returned known
        `(do
          let $(invocation.result.rawName):ident : $type ← ($called:term)
          $next:term)
    | .conditional condition yes no yesResult noResult result :: rest => do
        let condition ← condition.requireModel
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
        let discriminant ← discriminant.requireModel
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
  let mut scalarEqualities : Array (TSyntax `term) := #[]
  let mut currentHeap := initialHeap
  let mut preserved ← `(Complexity.Language.Heap.ShapeExtends.refl $initialHeap)
  let mut preservedContents ← `((by
    intro kind view values observed
    exact observed : Complexity.Language.Buffer.PreservesContents $initialHeap $initialHeap))
  let mut tactics := #[← normalizeAction]
  for instruction in trace do
    let (result, relationProof) ← match instruction with
      | .call invocation => do
          let models ← invocation.arguments.mapM Value.requireModel
          let operation ← invocation.operation.requireModel
          let mut applied := models.map (·.model)
          let mut hypotheses := #[]
          for argument in invocation.arguments, model in models do
            if argument.type.isPure then
              let observed ← observationAt argument currentHeap relations
              let equality := mkIdent (← mkFreshUserName `argumentEqual)
              let raw := resolveRaw model.rawModel known
              tactics := tactics.push (← `(tactic|
                have $equality:ident : $(model.model) = $raw := $observed))
              scalarEqualities := scalarEqualities.push ⟨equality.raw⟩
              tactics := tactics.push (← `(tactic|
                simp (config := { failIfUnchanged := false }) only [← $equality:ident]))
            else
              applied := applied.push model.rawModel
              hypotheses := hypotheses.push (← observationAt argument currentHeap relations)
          applied := applied.push currentHeap ++ hypotheses
          if let some index := operation.positiveStride then
            let some argument := models[index]?
              | throwError "finite-range operation is missing its stride argument"
            let stride := argument.model
            applied := applied.push (← `(show 0 < $stride from by
              simp (config := { zetaDelta := true, failIfUnchanged := false }) only
                [Nat.add_eq] <;> omega))
          let relation ← if preserveArrays then do
              let some strong := operation.preservingRelation
                | throwError "native array composition requires a proved contents-preserving call"
              pure strong
            else pure operation.relation
          pure (invocation.result, Lean.Syntax.mkApp ⟨relation.raw⟩ applied)
      | .conditional condition yes no yesResult noResult result => do
          let observed ← observationAt condition currentHeap relations
          let condition ← condition.requireModel
          let resultModel ← result.requireModel
          let equality := mkIdent (← mkFreshUserName `conditionEqual)
          let rawCondition := resolveRaw condition.rawModel known
          tactics := tactics.push (← `(tactic|
            have $equality:ident : $(condition.model) = $rawCondition := $observed))
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
          let noneProof ← relationTrace absent noneResult currentHeap relations known preserveArrays
          let mut someRelations := relations
          let mut someKnown := known
          let mut somePrefix := #[]
          if payload.type.isPure then
            somePrefix := somePrefix.push (← `(tactic|
              change $(payloadModel.model) = $(payload.rawName):ident at $payloadObserved:ident))
            somePrefix := somePrefix.push (← `(tactic| subst $(payload.rawName):ident))
            someKnown := someKnown.push (payload.rawName.getId, payloadModel.model)
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
      let model ← result.requireModel
      tactics := tactics.push (← `(tactic| change $(model.model) = $returned:ident at $observed:ident))
      tactics := tactics.push (← `(tactic| subst $returned:ident))
      known := known.push (result.rawName.getId, model.model)
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
  let returnedModel ← returnedValue.requireModel
  let result := resolveRaw returnedModel.rawModel known
  let heapPost ← if preserveArrays then `(And.intro $preserved $preservedContents) else pure preserved
  -- Argument rewrites also affect scalar fields retained in a mixed raw state.
  -- Keep their actual projection equalities, without replacing its heap-backed
  -- representation by equality of the whole native and raw values.
  let scalarFacts ← scalarEqualities.mapM fun equality =>
    `(Lean.Parser.Tactic.simpLemma| $equality:term)
  let executed ← `(by first | rfl | simp only [$scalarFacts,*])
  tactics := tactics.push (← `(tactic|
    exact ⟨$result, $currentHeap, $executed, $observed, $heapPost⟩))
  return tactics

private def equationDeclaration (family : TSyntax `ident) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let header ← correspondenceHeader family fn
  let ⟨nativeName, rawEquation, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let equationName := fieldName family fn.name "_action_eq_native"
  let mut tactics := #[← `(tactic| rw [$rawEquation:ident]),
    ← `(tactic| unfold $nativeName:ident), ← normalizeAction]
  for instruction in model.calls do
    let .call invocation := instruction
      | throwError "a conditional block uses relational correspondence"
    let operation ← invocation.operation.requireModel
    let arguments := invocation.arguments
    let models ← arguments.mapM Value.requireModel
    let mut applied := models.map (·.model)
    let mut relations := #[]
    for argument in arguments, model in models do
      unless argument.type.isPure do
        applied := applied.push model.rawModel
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

private def rangeRelationTactics (family : TSyntax `ident) (fn : Function)
    (range : RangeRegistration) (heap positive : TSyntax `ident) (preserveArrays : Bool) :
    TermElabM (Array (TSyntax `tactic)) := do
  let callbackModel ← range.callback.requireModel
  let source := fieldName (sourceFamily family) (mkIdent `program)
  let bodyId := fieldName (sourceFamily family) (mkIdent range.callback.sourceName) "Id"
  let bodyObserve := fieldName (sourceFamily family) (mkIdent range.callback.sourceName) "_observe"
  let rangeId := fieldName (sourceFamily family) fn.name "Id"
  let rangeObserve := fieldName (sourceFamily family) fn.name "_observe"
  let modelEquation := fieldName family fn.name "_fold_eq_native"
  let type ← termOfExpr fn.result.nativeType
  let core ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let representation ← termOfExpr fn.result.representation
  let representation ← `(($representation : Complexity.Language.Representation $type $core))
  let frame ← if preserveArrays then `(Complexity.Language.Buffer.PreservesContents)
    else `(fun (_ _ : Complexity.Language.Heap) => True)
  let callback := mkIdent (← mkFreshUserName `rangeCallback)
  let index := mkIdent (← mkFreshUserName `index)
  let initial := mkIdent (← mkFreshUserName `initial)
  let actual := mkIdent (← mkFreshUserName `actual)
  let current := mkIdent (← mkFreshUserName `current)
  let observed := mkIdent (← mkFreshUserName `observed)
  let mut arguments : Array (TSyntax `term) := #[⟨index.raw⟩, ⟨initial.raw⟩]
  let mut callbackProof := #[]
  let actualValue : TSyntax `term := if fn.result.isPure then ⟨initial.raw⟩ else ⟨actual.raw⟩
  if fn.result.isPure then
    callbackProof := callbackProof ++ #[
      ← `(tactic| change $initial:ident = $actual:ident at $observed:ident),
      ← `(tactic| subst $actual:ident)]
  else arguments := arguments.push ⟨actual.raw⟩
  arguments := arguments.push ⟨current.raw⟩
  unless fn.result.isPure do arguments := arguments.push ⟨observed.raw⟩
  let relation ← if preserveArrays then
      match callbackModel.preservingRelation with
      | some relation => pure relation
      | none => throwError "range contents preservation requires the actual callback frame"
    else pure callbackModel.relation
  let invocation := Lean.Syntax.mkApp ⟨relation.raw⟩ arguments
  callbackProof := callbackProof ++ (← if preserveArrays then do
      pure #[
        ← `(tactic| obtain ⟨value, finish, executed, related, _, contents⟩ := $invocation),
        ← `(tactic| refine ⟨value, finish, ?_, related, contents⟩)]
    else do
      pure #[
        ← `(tactic| obtain ⟨value, finish, executed, related, _⟩ := $invocation),
        ← `(tactic| refine ⟨value, finish, ?_, related, True.intro⟩)])
  callbackProof := callbackProof ++ #[
    ← `(tactic| change ($source:ident).eval $bodyId:ident
      (Complexity.Language.Env.cons $index:ident
        (Complexity.Language.Env.cons $actualValue Complexity.Language.Env.empty)) $current:ident = _),
    ← `(tactic| rw [$bodyObserve:ident]),
    ← `(tactic| exact executed)]
  let frameRefl ← if preserveArrays then
      `(by intro heap kind view values observed; exact observed)
    else `(by intros; trivial)
  let frameTrans ← if preserveArrays then
      `(by
        intro first second third firstFrame secondFrame kind view values observed
        exact secondFrame view values (firstFrame view values observed))
    else `(by intros; trivial)
  let some startParameter := fn.parameters[0]? | throwError "range helper is missing its start parameter"
  let some stopParameter := fn.parameters[1]? | throwError "range helper is missing its stop parameter"
  let some strideParameter := fn.parameters[2]? | throwError "range helper is missing its stride parameter"
  let some state := fn.parameters[3]? | throwError "range helper is missing its state parameter"
  let start := startParameter.name
  let stop := stopParameter.name
  let stride := strideParameter.name
  let rawState : TSyntax `term := if state.type.isPure then ⟨state.name.raw⟩ else ⟨state.rawName.raw⟩
  let stateObserved ← if state.type.isPure then `(rfl)
    else pure (⟨state.relationName.raw⟩ : TSyntax `term)
  let resultFrame ← if preserveArrays then
      `(tactic| refine ⟨value, finish, ?_, ?_, shape, contents⟩)
    else `(tactic| refine ⟨value, finish, ?_, ?_, shape⟩)
  return #[
    ← `(tactic| have $callback:ident : Complexity.Language.Range.Fold.Contract
        $source:ident $bodyId:ident rfl $representation $(callbackModel.native) $frame := by
      intro $index:ident $initial:ident $actual:ident $current:ident $observed:ident
      $callbackProof:tactic*),
    ← `(tactic| obtain ⟨value, finish, executed, related, contents, shape⟩ :=
      Complexity.Language.Range.Fold.function_eval_exists
        (source := $source:ident) (fn := $bodyId:ident) (same := rfl)
        (R := $representation) (step := $(callbackModel.native)) (frame := $frame)
        $callback:ident $frameRefl $frameTrans $rangeId:ident rfl (by rfl)
        $start:ident $stop:ident $stride:ident $positive:ident
        $(state.name):ident $rawState $heap:ident $stateObserved),
    resultFrame,
    ← `(tactic|
      · change ($source:ident).eval $rangeId:ident
          (Complexity.Language.Env.cons $start:ident
            (Complexity.Language.Env.cons $stop:ident
              (Complexity.Language.Env.cons $stride:ident
                (Complexity.Language.Env.cons $rawState Complexity.Language.Env.empty))))
          $heap:ident = _ at executed
        rw [$rangeObserve:ident] at executed
        exact executed),
    ← `(tactic| · simpa only [$modelEquation:ident] using related)]

private def relationDeclaration (family : TSyntax `ident) (fn : Function)
    (model : FunctionModel) (preserveArrays : Bool := false) : TermElabM Syntax := do
  let header ← correspondenceHeader family fn
  let ⟨nativeName, rawEquation, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let relationName := fieldName family fn.name
    (if preserveArrays then "_action_rel_native_preserving" else "_action_rel_native")
  let resultType ← actualTypeTerm fn.result.coreTy
  let resultCoreType ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeResultType ← termOfExpr fn.result.nativeType
  let resultRepresentation ← termOfExpr fn.result.representation
  let positive := mkIdent (← mkFreshUserName `positiveStride)
  let extra ← if model.range.isSome then do
      let some stride := fn.parameters[2]? | throwError "range helper is missing its stride parameter"
      pure #[← `(bracketedBinder| ($positive:ident : 0 < $(stride.name):ident))]
    else pure #[]
  let heapPost ← if preserveArrays then
      `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
        Complexity.Language.Buffer.PreservesContents $heap:ident finish)
    else `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish)
  let declaration (tactics : Array (TSyntax `tactic)) : TermElabM Syntax := do
    let termination ← if model.recursive && !(fn.preservesArrays && !preserveArrays) then
        pure model.termination
      else `(Lean.Parser.Termination.suffix|)
    return (← `(command|
      /-- Successful execution observes the native result in its actual final heap
      and retains every previously represented immutable list. -/
      theorem $relationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
          ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder*
          $extra:bracketedBinder* :
          ∃ (returned : $resultType) (finish : Complexity.Language.Heap),
            $rawAction $heap:ident = Part.some (.ok returned, finish) ∧
            ($resultRepresentation : Complexity.Language.Representation
              $nativeResultType $resultCoreType).Rel $nativeValue returned finish ∧
            $heapPost finish := by
        $tactics:tactic*
      $termination:suffix)).raw
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
    if model.range.isSome then applied := applied.push ⟨positive.raw⟩
    let correct := Lean.Syntax.mkApp ⟨strong.raw⟩ applied
    return ← declaration #[
      ← `(tactic| obtain ⟨returned, finish, executed, related, shape, _⟩ := $correct),
      ← `(tactic| exact ⟨returned, finish, executed, related, shape⟩)]
  if let some range := model.range then
    return ← declaration (← rangeRelationTactics family fn range heap positive preserveArrays)
  let mut tactics := #[]
  if model.calls.any (fun | .call _ => false | _ => true) then
    let action ← traceAction model.calls.toList model.returned
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
  tactics := tactics ++ (← relationTrace model.calls model.returned ⟨heap.raw⟩ inputRelations #[] preserveArrays)
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

private def interfaceDeclarations (family : TSyntax `ident) (fn : Function) :
    TermElabM (Array Syntax) := do
  let id := fieldName family fn.name "Id"
  let rawId := fieldName (sourceFamily family) fn.name "Id"
  let representation := fieldName family fn.name "_representation"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let result ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeInputType ← inputType fn.parameters.toList
  let nativeResultType ← termOfExpr fn.result.nativeType
  let argumentRepresentation ← inputRepresentation fn.parameters.toList
  let resultRepresentation ← termOfExpr fn.result.representation
  let idDeclaration ← `(command|
    abbrev $id:ident := $rawId:ident)
  let representationDeclaration ← `(command|
    /-- Ordinary arguments and the actual result observed in their real source heaps.
    This interface does not assert the existence of a total mathematical model. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $nativeInputType (fun _ => $nativeResultType) { params := [$params,*], result := $result } :=
      Complexity.Language.FunctionRepresentation.ofResult $argumentRepresentation
        (fun _ => $resultRepresentation))
  return #[idDeclaration.raw, representationDeclaration.raw]

private def refinementDeclaration (family : TSyntax `ident) (fn : Function) :
    TermElabM Syntax := do
  let program := mkIdentFrom family (family.getId ++ `program)
  let id := fieldName family fn.name "Id"
  let native := fieldName family fn.name
  let representation := fieldName family fn.name "_representation"
  let refinement := fieldName family fn.name "_refines"
  let equation := fieldName family fn.name "_action_rel_native"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let nativeInputType ← inputType fn.parameters.toList
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
  let refinementDeclaration ← `(command|
    /-- Automatic correspondence for the same generated source function, without a machine budget. -/
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $id:ident $representation:ident (fun _ => True)
        (fun ($input:ident : $nativeInputType) => $nativeValue) := by
      $tactics:tactic*)
  return refinementDeclaration.raw

private def emitDeclarations (declarations : Array Syntax) : CommandElabM Unit :=
  elabCommand (mkNullNode declarations)

private def readImports (libraries : Array (TSyntax `ident)) : CommandElabM ImportedPrograms :=
  readRepresentedImports libraries

private def registerNativeProgram (family rawFamily : TSyntax `ident) (functions : Array Function) :
    CommandElabM Unit := do
  let sourceProgramName ← resolveGlobalConstNoOverload (mkIdentFrom rawFamily (rawFamily.getId ++ `program))
  let typeInfo (type : NativeType) : FunctionTypeInfo := {
    nativeType := type.nativeType, coreTy := type.coreTy, representation := type.representation }
  let headers ← (functions.filter (·.exposed)).mapM fun fn => do
    let action ← resolveGlobalConstNoOverload (fieldName rawFamily fn.name)
    let model? : Option FunctionModelInfo ← match fn.model? with
      | none => pure none
      | some _ => do
          let name ← resolveGlobalConstNoOverload (fieldName family fn.name)
          let relation ← resolveGlobalConstNoOverload (fieldName family fn.name "_action_rel_native")
          let refinement ← resolveGlobalConstNoOverload (fieldName family fn.name "_refines")
          let equation ← if fn.hasExactEquation then
              some <$> resolveGlobalConstNoOverload (fieldName family fn.name "_action_eq_native")
            else pure none
          let preservingRelation ← if fn.preservesArrays then
              some <$> resolveGlobalConstNoOverload
                (fieldName family fn.name "_action_rel_native_preserving")
            else pure none
          pure (some {
            name, equation, relation := some relation
            refinement := some refinement, preservingRelation })
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

private def elaborate (family : TSyntax `ident) (libraries : Array (TSyntax `ident))
    (functions : Array (TSyntax `sourceFunction)) : CommandElabM Unit := do
  let imports ← readImports libraries
  let prepared ← liftTermElabM do
    let declarations ← functions.mapM fun declaration => liftMacroM (parseDeclaration declaration)
    let mut initial : Preparation := {}
    for declaration in declarations do
      initial := { initial with
        declarationNames := initial.declarationNames.insert declaration.name.getId }
    let (_, state) ← (declarations.forM (prepareFunction family imports)).run initial
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
  Complexity.Language.Syntax.elaborateSourceProgram rawFamily rawFunctions operationFamilies
  let signatures := mkIdentFrom family (family.getId ++ `signatures)
  let program := mkIdentFrom family (family.getId ++ `program)
  let rawSignatures := mkIdentFrom family (rawFamily.getId ++ `signatures)
  let rawProgram := mkIdentFrom family (rawFamily.getId ++ `program)
  emitDeclarations #[
    (← `(command| abbrev $signatures:ident := $rawSignatures:ident)).raw,
    (← `(command| def $program:ident : Complexity.Language.Program $signatures:ident := $rawProgram:ident)).raw]
  for fn in prepared.functions do
    if fn.exposed then emitDeclarations (← liftTermElabM (interfaceDeclarations family fn))
    match fn.model? with
    | none =>
        if fn.exposed then
          let name := fieldName family fn.name
          let action := fieldName rawFamily fn.name
          elabCommand (← `(command|
            /-- The same source action, without an asserted total mathematical model. -/
            noncomputable abbrev $name:ident := $action:ident))
    | some model =>
        elabCommand (← liftTermElabM (nativeDeclaration family fn model))
        if let some range := model.range then
          elabCommand (← liftTermElabM (rangeModelDeclaration family fn model range))
        if fn.hasExactEquation then
          elabCommand (← liftTermElabM (equationDeclaration family fn model))
        if fn.preservesArrays then
          elabCommand (← liftTermElabM (relationDeclaration family fn model true))
        elabCommand (← liftTermElabM (relationDeclaration family fn model))
        if fn.exposed then elabCommand (← liftTermElabM (refinementDeclaration family fn))
  registerNativeProgram family rawFamily prepared.functions

/-- Generate ordinary mathematical functions and checked represented source
implementations from local bindings, branches, calls and normal finite ranges.
Nonlocal loop exits are not supported here; general while uses explicit source contracts. -/
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
