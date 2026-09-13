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
import Complexity.Language.Eval.Locals.Range.Represented
import Lean.Util.SCC

/-!
# Native mathematical views of represented source operations

This frontend retains ordinary mathematical types alongside actual source types.
Heap-backed arrays and lists carry relations, not heap-independent encodings.
Mutable local versions, conditionals and normal finite ranges compose the same
registered operations and their checked heap relations. A finite range retains
the shared source's original named loop and in-place body; its mathematical fold
is proof-side only. General while and source calls without a total model retain
their actual control and heap effects, exposing source contracts instead of a
fabricated pure function. Finite-range exits retain source control without an
automatic total-function view; general loops inside value-producing branches
remain unsupported. Shared typed product
and Option patterns retain one evaluation and ordinary source projections.
Scratch blocks retain their real cleanup and enclosing returns; their contracts
observe the post-cleanup heap rather than a pre-cleanup mathematical view.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

private structure Parameter where
  name : TSyntax `ident
  /-- Hygienic mathematical local; source syntax continues to use `name`. -/
  nativeName : TSyntax `ident := name
  type : NativeType
  rawName : TSyntax `ident
  relationName : TSyntax `ident
  /-- Stable lexical slot; assignment changes its value, not its identity. -/
  slot : Name := rawName.getId

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

/-- Actual source identity and mathematical types do not require a total-function
model. Model names are checked before they enter the public function registry. -/
private structure Operation where
  family : TSyntax `ident
  sourceName : Name
  inputs : Array NativeType
  result : NativeType
  model? : Option OperationModel := none
  /-- A local mathematical candidate, resolved before any model declaration or
  public registration. It promises neither an equation nor a heap frame. -/
  modelDependency? : Option Name := none
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
  /-- A proof of the original named range, not a new source call. -/
  | range (tag : Name) (arguments : Array Value) (result : Binding) (preserving : Bool)

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
          let .app (.app (.const ``Prod _) left) right ← whnf type.nativeType
            | throwError "projection requires a native product"
          pure (← resolveNativeType left, ← resolveNativeType right)
      | _ => throwError "projection requires a product"
    let projection := if first then ``Prod.fst else ``Prod.snd
    let apply (term : TSyntax `term) := Lean.Syntax.mkCApp projection #[term]
    return ({
      type := if first then left else right,
      raw := apply pair.raw
      model? := pair.model?.map fun model => {
        native := apply model.native
        model := apply model.model, rawModel := apply model.rawModel
        observation := .projection pair.type.isIdentity first model.observation } } : Value)
  let projectRecord (expression : TSyntax `term) (fieldName : Name) := do
    let record ← value scope expression
    if let .raw (.buffer _) := record.type then
      unless fieldName == `length || fieldName == ``Buffer.length do
        throwErrorAt expression "a raw buffer exposes its handle length, not an array contents field"
      let type ← termOfExpr record.type.nativeType
      return ({
        type := ← resolveType (← `(Nat))
        raw := ← `(($(record.raw)).$(mkIdent `length):ident)
        model? := ← record.model?.mapM fun model => do
          return {
            native := ← `(($(model.native)).length)
            model := ← `(($(model.model)).length)
            rawModel := ← `(($(model.rawModel)).length)
            observation := .unary (← `(fun (buffer : $type) => buffer.length)) model.observation } } : Value)
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
  | `(source_raw_value% ($expression)) =>
      let type ← liftMacroM <| inferRawValueType
        (scope.map fun binding => (binding.name, binding.type.coreTy))
        expression (expected.map (·.coreTy))
      return { type := ← resolveType (← rawTypeTerm type), raw := expression }
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
  | `(none) | `(Option.none) | `(.none) =>
      let some (.option payload) := expected
        | throwErrorAt stx "none requires an optional result, parameter or binding type"
      return {
        type := .option payload, raw := ← `(none)
        model? := some {
          native := stx, model := stx, rawModel := ← `(none)
          observation := .none payload } }
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
        model? := parameter.model?.map fun model => {
          toBindingModel := model, native := ⟨parameter.nativeName.raw⟩ } }
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
      let payload := expected.bind fun | .option payload => some payload | _ => none
      let result ← value scope expression payload
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
      let fields ← expected.mapM fun type => do
        match type with
        | .prod left right => return some (left, right)
        | .pure type =>
            if let .prod _ _ := type.coreTy then
              let arguments := type.nativeType.getAppArgs
              return some (← resolveNativeType arguments[0]!, ← resolveNativeType arguments[1]!)
            return none
        | _ => return none
      let fields := fields.join
      let left ← value scope left (fields.map (·.1))
      let right ← value scope right (fields.map (·.2))
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
            observation := .pair type.isIdentity left.observation right.observation } }
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
  tag : Name
  captured : Array Binding
  state : Binding
  index : Binding
  body : Array Trace
  returned : Value
  bodyNative : TSyntax `term
  start : Value
  stop : Value
  stride : Value
  result : Binding
  embedding : TSyntax `term
  mutableStep : TSyntax `term
  initialMutable : TSyntax `term
  indices : TSyntax `term
  site? : Option ActualRangeSite := none

private structure FunctionModel where
  nativeBody : TSyntax `term
  calls : Array Trace
  returned : Value
  termination : TSyntax ``Lean.Parser.Termination.suffix
  recursive : Bool := false

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
      match parameter.type with | .pure _ | .raw _ | .list _ => true | _ => false
    match fn.result with
    | .pure _ | .raw _ => !model.recursive && scalarArguments && model.calls.all fun
        | .call invocation => invocation.operation.model?.any (·.equation.isSome)
        | _ => false
    | _ => false

private partial def Trace.preservesArrays : Trace → Bool
  | .call invocation => invocation.operation.model?.any (·.preservingRelation.isSome)
  | .conditional _ yes no _ _ _ => yes.all Trace.preservesArrays && no.all Trace.preservesArrays
  | .optionMatch _ _ absent present _ _ _ =>
      absent.all Trace.preservesArrays && present.all Trace.preservesArrays
  | .range _ _ _ preserving => preserving

private partial def Trace.containsRange : Trace → Bool
  | .range .. => true
  | .conditional _ yes no _ _ _ => yes.any Trace.containsRange || no.any Trace.containsRange
  | .optionMatch _ _ absent present _ _ _ =>
      absent.any Trace.containsRange || present.any Trace.containsRange
  | .call _ => false

private def Function.preservesArrays (fn : Function) : Bool :=
  match fn.model? with
  | none => false
  | some model => fn.hasExactEquation || model.calls.all Trace.preservesArrays

/-- Every local signature is available before any body or model is prepared. -/
private structure LocalHeader where
  name : TSyntax `ident
  parameters : Array (Name × NativeType)
  result : NativeType

private structure Preparation where
  folds : Array FoldRegistration := #[]
  constructors : Array ConsRegistration := #[]
  deconstructors : Array UnconsRegistration := #[]
  emptinessTests : Array IsEmptyRegistration := #[]
  functions : Array Function := #[]
  ranges : Array RangeRegistration := #[]
  localHeaders : Array LocalHeader := #[]
  calledFamilies : Array (TSyntax `ident) := #[]
  current : Option Operation := none
  currentRecursive : Bool := false

private abbrev PrepareM := StateT Preparation TermElabM

private def prepareMacro {α : Type} (action : MacroM α) : PrepareM α :=
  liftM (liftMacroM action : TermElabM α)

private def fieldName (family name : TSyntax `ident) (suffix : String := "") : TSyntax `ident :=
  mkIdentFrom name ((family.getId ++ name.getId).appendAfter suffix)

/-- Names of one source declaration and its optional mathematical proof view.
These names select no alternate evaluator or compilation path. -/
structure DeclarationNames where
  /-- Namespace of the public interfaces and generated correspondence theorems. -/
  publicFamily : TSyntax `ident
  /-- Namespace of the actual source table and actions. -/
  sourceFamily : TSyntax `ident
  /-- Suffix of the optional mathematical function, relative to its source name. -/
  modelSuffix : String

/-- Compatibility layout: source actions live under `Family.Source`, while the
ordinary mathematical function keeps the public name `Family.f`. -/
def DeclarationNames.native (family : TSyntax `ident) : DeclarationNames := {
  publicFamily := family
  sourceFamily := mkIdentFrom family (family.getId ++ `Source)
  modelSuffix := "" }

/-- Direct source layout: `Family.f` remains the actual action and an optional
checked mathematical function is named `Family.f_model`. -/
def DeclarationNames.source (family : TSyntax `ident) : DeclarationNames := {
  publicFamily := family, sourceFamily := family, modelSuffix := "_model" }

private def DeclarationNames.modelName (names : DeclarationNames) (name : TSyntax `ident) :
    TSyntax `ident :=
  fieldName names.publicFamily name names.modelSuffix

private def functionOperation (names : DeclarationNames) (fn : Function) : Operation := {
  family := names.sourceFamily
  sourceName := fn.name.getId
  inputs := fn.parameters.map (·.type)
  result := fn.result
  model? := fn.model?.map fun _ => {
    native := ⟨(names.modelName fn.name).raw⟩
    equation := if fn.hasExactEquation then some (fieldName names.publicFamily fn.name "_action_eq_native") else none
    relation := fieldName names.publicFamily fn.name "_action_rel_native"
    refinement := fieldName names.publicFamily fn.name "_refines"
    preservingRelation := if fn.preservesArrays then
      some (fieldName names.publicFamily fn.name "_action_rel_native_preserving") else none } }

private def localOperation? (names : DeclarationNames) (called : TSyntax `ident)
    (recursive : Bool := false) : PrepareM (Option Operation) := do
  if let some operation := (← get).current.filter
      (fun operation => operation.sourceName == called.getId) then
    if recursive then modify fun state => { state with currentRecursive := true }
    return some operation
  if let some fn := (← get).functions.find? (fun fn => fn.name.getId == called.getId) then
    return some { (functionOperation names fn) with modelDependency? := some fn.name.getId }
  return (← get).localHeaders.find? (fun header => header.name.getId == called.getId) |>.map
    fun header => {
      family := names.sourceFamily, sourceName := header.name.getId
      inputs := header.parameters.map (·.2), result := header.result
      modelDependency? := some header.name.getId
      model? := some {
        native := ⟨(names.modelName header.name).raw⟩
        equation := none
        relation := fieldName names.publicFamily header.name "_action_rel_native"
        refinement := fieldName names.publicFamily header.name "_refines" } }

private def rawHeaders (names : DeclarationNames) : PrepareM (Array RawCallHeader) := do
  return (← get).localHeaders.map fun header => {
    name := header.name
    params := header.parameters.map (fun (name, type) => (name, type.coreTy))
    result := header.result.coreTy
    source := {
      family := names.sourceFamily.getId, name := header.name.getId
      action := names.sourceFamily.getId ++ header.name.getId } }

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
  return imports.native.find? (fun info => info.nativeName == resolved ||
    info.actionName == some resolved || info.sourceFamily ++ info.sourceName == resolved)

/-- A source header can be called without a proved total-function view. A raw
signature supplies only identity observations, never inferred array contents. -/
private def findImportedOperation? (imports : ImportedPrograms) (name : TSyntax `ident) :
    TermElabM (Option Operation) := do
  if let some native ← findImportedNative? imports name then
    return some (importedOperation native)
  let resolved? ← try pure (some (← resolveGlobalConstNoOverload name)) catch _ => pure none
  let some resolved := resolved? | return none
  let sourceAlias := match (← getEnv).find? resolved with
    | some (.defnInfo declaration) => match declaration.value with
      | .const name _ => some name
      | _ => none
    | _ => none
  for (_, functions) in imports.source do
    for information in functions do
      let some source := information.source? | continue
      unless resolved == source.action || sourceAlias == some source.action do continue
      let (inputs, result) ← match information.mathematical? with
        | some mathematical => do
            let inputs ← mathematical.params.mapM fun (_, type) => resolveTypeInfo type
            pure (inputs, ← resolveTypeInfo mathematical.result)
        | none => do
            let inputs ← information.params.mapM fun (_, type) => do
              resolveType (← rawTypeTerm type)
            pure (inputs, ← resolveType (← rawTypeTerm information.result))
      return some {
        family := mkIdent source.family, sourceName := source.name, inputs, result
        actionName := some source.action }
  return none

private def findCallback (imports : ImportedPrograms)
    (name : TSyntax `ident) : TermElabM Callback := do
  let resolved ← resolveGlobalConstNoOverload name
  let pureView (family : Name) (info : FunctionInfo) :=
    info.pure && (family ++ info.name == resolved ||
      info.model?.any (fun model => model.name == resolved) ||
      info.source?.any (fun source => source.action == resolved))
  -- Direct pure calls also have a relational adapter. A fold keeps the stronger
  -- original unchanged-heap contract and its existing compiled equation API.
  let preferPure := imports.source.any fun (family, functions) => functions.any (pureView family)
  if let some info := (← findImportedNative? imports name).filter (fun _ => !preferPure) then
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
      sourceFamily := info.sourceFamily, sourceName := info.sourceName, nativeName := info.nativeName,
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
        let some model := info.model?
          | throwErrorAt name "the registered pure callback is missing its checked mathematical view"
        return {
          sourceFamily := family, sourceName := info.name, nativeName := model.name,
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

private def namedCall? (expression : TSyntax `term) :
    Option (TSyntax `ident × Array (TSyntax `term)) :=
  match expression with
  | `($called:ident) => some (called, #[])
  | `($called:ident $arguments:term*) => some (called, arguments)
  | _ => none

private def rawFieldAccess? (expression : TSyntax `term) :
    Option (TSyntax `term × Name) :=
  match expression with
  | `($receiver:term.$field:ident) => some (receiver, field.getId)
  | `($name:ident) => match name.getId with
      | .str receiver field =>
          if receiver.isAnonymous then none
          else some (⟨(mkIdentFrom name receiver).raw⟩, Name.mkSimple field)
      | _ => none
  | _ => none

private def rawCallSyntax (expression : TSyntax `term) : Bool := Id.run do
  let head := match expression with
    | `($head:term $_arguments:term*) => head
    | _ => expression
  if head.raw.getId == `Buffer.alloc || head.raw.getId == `NodeRef.cons then return true
  let some (_, field) := rawFieldAccess? head | return false
  return field == `get || field == `slice || field == `read || field == `set

private partial def canonicalCall? (imports : ImportedPrograms) (scope : List Binding)
    (expression : TSyntax `term) :
    PrepareM (Option (TSyntax `term)) := do
  if let some (called, _) := namedCall? expression then
    unless scope.any (fun binding => binding.name.getId == called.getId) do
      if (← get).current.any (fun operation => operation.sourceName == called.getId) ||
          (← get).functions.any (fun fn => fn.name.getId == called.getId) ||
          (← get).localHeaders.any (fun header => header.name.getId == called.getId) then
        return some expression
  if rawCallSyntax expression then return some expression
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
    unless scope.any (fun binding => binding.name.getId == called.getId) do
      if (← get).current.any (fun operation => operation.sourceName == called.getId) ||
          (← get).functions.any (fun fn => fn.name.getId == called.getId) ||
          (← findImportedOperation? imports called).isSome then
        return some expression
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
      if (← findImportedOperation? imports called).isSome then return some expression
      return none
  | _ => return none

/-- Checked local models take precedence over their precollected source-only
headers; all local names take precedence over intrinsic spellings. -/
private def operationCall? (names : DeclarationNames) (imports : ImportedPrograms)
    (scope : List Binding) (expression : TSyntax `term) :
    PrepareM (Option (Operation × Array (TSyntax `term))) := do
  if let some (called, arguments) := namedCall? expression then
    if let some operation ← localOperation? names called true then
      return some (operation, arguments)
  match expression with
  | `(Array.append $left:term $right:term) =>
      return some (← arrayOperation true, #[left, right])
  | `(List.foldl $callback:ident $initial:term $values:term) =>
      return some (← foldOperation names.publicFamily imports callback, #[initial, values])
  | `(List.cons $head:term $tail:term) =>
      let tailValue ← value scope tail
      let .list kind := tailValue.type
        | throwErrorAt tail "List.cons requires a represented list tail"
      return some (← consOperation names.publicFamily kind, #[head, tail])
  | `(List.uncons $values:term) =>
      let valuesValue ← value scope values
      let .list kind := valuesValue.type
        | throwErrorAt values "List.uncons requires a represented list"
      return some (← unconsOperation names.publicFamily kind, #[values])
  | `(List.isEmpty $values:term) =>
      let valuesValue ← value scope values
      let .list kind := valuesValue.type
        | throwErrorAt values "List.isEmpty requires a represented list"
      return some (← isEmptyOperation names.publicFamily kind, #[values])
  | _ =>
      let some (called, arguments) := namedCall? expression | return none
      let some operation ← findImportedOperation? imports called | return none
      unless (← get).calledFamilies.any (fun imported => imported.getId == operation.family.getId) do
        modify fun state => { state with calledFamilies := state.calledFamilies.push operation.family }
      return some (operation, arguments)

private def prepareInvocation (names : DeclarationNames) (scope : List Binding)
    (name : TSyntax `ident) (operation : Operation) (arguments : Array (TSyntax `term)) :
    TermElabM (Invocation × TSyntax `term × Option (TSyntax `term)) := do
  unless arguments.size == operation.inputs.size do throwError "wrong number of source call arguments"
  let arguments ← arguments.mapIdxM fun index argument =>
    value scope argument operation.inputs[index]?
  for argument in arguments, expected in operation.inputs do expect name expected argument.type
  let sourceName := mkIdentFrom name
    (if operation.family.getId == names.sourceFamily.getId then operation.sourceName
      else operation.family.getId ++ operation.sourceName)
  let raw := Lean.Syntax.mkApp ⟨sourceName.raw⟩ (arguments.map (·.raw))
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
      observation := if operation.result.isIdentity then .refl else .named relationName.getId } : BindingModel))
  let binding : Binding := {
    name, type := operation.result, rawName, relationName, model? := callModel.map (·.2) }
  return (⟨operation, arguments, binding⟩, raw, callModel.map (·.1))

/-- Convert user operands once, before Core's raw normalizer. A raw operation
requires a handle, not a coincidentally equal Array/List source layout. -/
private def prepareRawOperands (scope : List Binding) (expression : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let (head, operands) := match expression with
    | `($head:term $operands:term*) => (head, operands)
    | _ => (expression, #[])
  if head.raw.getId == `NodeRef.cons then
    unless operands.size == 2 do
      throwErrorAt expression "node construction expects a scalar head and an optional raw tail"
    let first ← value scope operands[0]!
    let kind ← match first.type.coreTy with
      | .nat => pure CellTy.nat
      | .bool => pure CellTy.bool
      | _ => throwErrorAt operands[0]! "node construction requires a Nat or Bool head"
    let tailType ← resolveType (← rawTypeTerm (.option (.node kind)))
    let tail ← value scope operands[1]! (some tailType)
    expect operands[1]! tailType tail.type
    return Lean.Syntax.mkApp head #[first.raw, tail.raw]
  if head.raw.getId == `Buffer.alloc then
    let arguments ← operands.mapM fun operand => return (← value scope operand).raw
    return Lean.Syntax.mkApp head arguments
  let some (receiver, field) := rawFieldAccess? head
    | throwErrorAt expression "expected a declared source call or raw buffer/node operation"
  unless field == `get || field == `slice || field == `set || field == `read do
    throwErrorAt expression "unsupported raw source operation"
  let receiver ← value scope receiver
  match field, receiver.type with
  | `read, .raw (.node _) => pure ()
  | `get, .raw (.buffer _) | `slice, .raw (.buffer _) | `set, .raw (.buffer _) => pure ()
  | _, _ => throwErrorAt expression "raw operations require a Buffer or NodeRef handle; \
      use a registered represented operation for mathematical Array/List values"
  let head ← `($(receiver.raw).$(mkIdent field):ident)
  let arguments ← operands.mapM fun operand => return (← value scope operand).raw
  return if arguments.isEmpty then head else Lean.Syntax.mkApp head arguments

/-- Raw ANF expressions retain their already established source interpretation
when re-entering the same statement preparer. No control or scope is changed. -/
private partial def markRawElements (elements : Array (TSyntax `doElem)) :
    TermElabM (Array (TSyntax `doElem)) :=
  elements.mapM fun element => do
    match element with
    | `(doElem| let $name:ident $[: $type:term]? := $expression:term) =>
        `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($expression))
    | `(doElem| let mut $name:ident $[: $type:term]? := $expression:term) =>
        `(doElem| let mut $name:ident $[: $type:term]? := source_raw_value% ($expression))
    | `(doElem| $name:ident := $expression:term) =>
        `(doElem| $name:ident := source_raw_value% ($expression))
    | `(doElem| if $guard:term then $yes:doSeq else $no:doSeq) =>
        let yes : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((← markRawElements (getDoElems yes)).map (·.raw))⟩
        let no : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq
          ((← markRawElements (getDoElems no)).map (·.raw))⟩
        `(doElem| if source_raw_value% ($guard) then $yes:doSeq else $no:doSeq)
    | _ => throwErrorAt element "unexpected statement produced by raw operand normalization"

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

private def somePattern? (pattern : TSyntax `term) : Option (TSyntax `term) :=
  match pattern with
  | `(some $payload:term) | `(Option.some $payload:term) | `(.some $payload:term) => some payload
  | _ => none

/-- Use the shared checked pattern and nominal projection expander. A simple
name is the payload binder itself; other patterns share that same payload. -/
private def preparePayloadPattern (pattern : TSyntax `term) (type : NativeType) :
    TermElabM (TSyntax `ident × Array (TSyntax `doElem)) := do
  let pattern ← liftMacroM (checkedBindingPattern pattern)
  match pattern with
  | .name name => return (name, #[])
  | _ =>
      let name := mkIdent (← mkFreshUserName `payload)
      return (name, ← patternBindings pattern type ⟨name.raw⟩)

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

private inductive BindingKind where
  | immutable
  | mutable
  | assignment

/-- Actual mutable locals remain source assignments. Mathematical versions are
tracked separately and do not replace a loop-carried source variable. -/
private def rawBinding (kind : BindingKind) (name : TSyntax `ident)
    (type expression : TSyntax `term) (action : Bool := false) :
    TermElabM (TSyntax `doElem) := do
  match kind, action with
  | .immutable, false => `(doElem| let $name:ident : $type := $expression)
  | .immutable, true => `(doElem| let $name:ident : $type ← $expression:term)
  | .mutable, false => `(doElem| let mut $name:ident : $type := $expression)
  | .mutable, true => `(doElem| let mut $name:ident : $type ← $expression:term)
  | .assignment, false => `(doElem| $name:ident := $expression)
  | .assignment, true => `(doElem| $name:ident ← $expression:term)

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
    (elements : Array (TSyntax `doElem)) (kind : BindingKind := .immutable) :
    TermElabM (Array (TSyntax `doElem)) := do
  if slot.guarded then
    let absent : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩
    let payload ← match kind with
      | .immutable => pure name
      | _ => pure (mkIdent (← mkFreshUserName `selectedValue))
    let elements ← match kind with
      | .immutable => pure elements
      | _ => do
          let `(Option $payloadType:term) := slot.type
            | throwError "a guarded result slot must carry an optional source value"
          let binding ← rawBinding kind name payloadType ⟨payload.raw⟩
          pure (#[binding] ++ elements)
    let present : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩
    return #[← `(doElem| match $(slot.name):ident with
      | none => $absent:doSeq
      | some $payload:ident => $present:doSeq)]
  return #[← rawBinding kind name slot.type ⟨slot.name.raw⟩] ++ elements

/-- Shadowed locals are not accessible; distinct visible aliases remain distinct
state fields even when they happen to hold the same heap handle. -/
private def visibleBindings (scope : List Binding) : Array Binding := Id.run do
  let mut visible := #[]
  for binding in scope do
    unless visible.any (fun previous : Binding => previous.name.getId == binding.name.getId) do
      visible := visible.push binding
  return visible

/-- Keep a slot at its declaration position, but observe its latest assignment.
Preparation versions are not extra source locals, and shadowed declarations
remain distinct even when their source spellings coincide. -/
private def lexicalBindings (scope : List Binding) : Array Binding := Id.run do
  let mut declared := #[]
  for binding in scope.reverse do
    unless declared.any (fun previous : Binding => previous.slot == binding.slot) do
      let latest := (scope.find? (fun current => current.slot == binding.slot)).getD binding
      declared := declared.push latest
  return declared.reverse

private partial def stateType (bindings : List Binding) : TermElabM (TSyntax `term) :=
  match bindings with
  | [] => `(Unit)
  | [binding] => termOfExpr binding.type.nativeType
  | binding :: rest => do `($(← termOfExpr binding.type.nativeType) × $(← stateType rest))

private def stateValue (bindings : Array Binding) : TermElabM (TSyntax `term) :=
  fieldsTerm (bindings.map (fun binding => (⟨binding.name.raw⟩ : TSyntax `term))).toList


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

/-- Unspecified effects cannot retain old contents observations. A loop can
also change mutable scalar locals, but immutable raw handles retain their identity. -/
private def invalidateObservations (scope : List Binding) (mutableLocals : Bool := false) :
    List Binding :=
  scope.map fun binding =>
    if !binding.type.isIdentity || (mutableLocals && binding.mutable) then
      { binding with model? := none }
    else binding

private def parameterBinding (name : TSyntax `ident) (type : NativeType) : TermElabM Binding := do
  let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
  let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
  return {
    name, type, rawName, relationName
    model? := some {
      model := ⟨name.raw⟩
      rawModel := if type.isIdentity then ⟨name.raw⟩ else ⟨rawName.raw⟩
      observation := if type.isIdentity then .refl else .named relationName.getId } }


/-- Raw statements and their normal lexical successor are independent of the
optional mathematical body, call trace and returned-value summary. -/
private structure PreparedBlock where
  raw : Array (TSyntax `doElem)
  native? : Option (Array (TSyntax `doElem))
  calls? : Option (Array Trace)
  returned? : Option Value
  normalScope? : Option (List Binding)

/-- Close a branch's local declarations by slot identity. Shadowing introduces
a new slot, while the latest assignment retains the enclosing slot. -/
private def closeScope (entry exit : List Binding) : List Binding :=
  entry.map fun binding =>
    (exit.find? (fun candidate => candidate.slot == binding.slot)).getD binding

/-- A join of observations, not a new source local or instruction. -/
private structure ChoiceModel where
  result : Binding
  native : TSyntax `term
  trace : Trace

private def choiceModel (available : Bool) (type : NativeType)
    (yes no : PreparedBlock)
    (choose : Bool → TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
    (trace : Array Trace → Array Trace → Value → Value → Binding → Trace) :
    TermElabM (Option ChoiceModel) := do
  unless available do return none
  let some yesNative := yes.native? | return none
  let some noNative := no.native? | return none
  let some yesCalls := yes.calls? | return none
  let some noCalls := no.calls? | return none
  let some yesResult := yes.returned? | return none
  let some noResult := no.returned? | return none
  let some yesModel := yesResult.model? | return none
  let some noModel := noResult.model? | return none
  let yesBody ← doTerm yesNative
  let noBody ← doTerm noNative
  let native ← choose false (← `(Id.run $yesBody)) (← `(Id.run $noBody))
  let model ← choose true yesModel.model noModel.model
  let name := mkIdent (← mkFreshUserName `branchView)
  let rawName := mkIdent (← mkFreshUserName `branchSource)
  let relationName := mkIdent (← mkFreshUserName `branchObserved)
  let result : Binding := {
    name, type, rawName, relationName
    model? := some {
      model, rawModel := ⟨rawName.raw⟩
      observation := if type.isIdentity then .refl else .named relationName.getId } }
  return some { result, native, trace := trace yesCalls noCalls yesResult noResult result }

/-- Pack only proof-side normal results. Actual branch bodies keep their
fallthrough and never receive a synthesized source return. -/
private def normalSummary (entry : List Binding) (mutable : Array Binding)
    (type : NativeType) (block : PreparedBlock) : TermElabM PreparedBlock := do
  let some scope := block.normalScope? | return block
  let state ← stateValue mutable
  let returned ← value (closeScope entry scope) state (some type)
  let native ← mapModelsM block.native? returned.model? fun native model => do
    return native.push (← `(doElem| return $(model.native)))
  return { block with native? := native, returned? := some returned }

private partial def sequence (names : DeclarationNames)
    (imports : ImportedPrograms) (resultType : NativeType)
    (scope : List Binding) (elements : List (TSyntax `doElem))
    (bindingKind : BindingKind := .immutable) (allowFallthrough : Bool := false)
    (localReturn : Bool := false) :
    PrepareM PreparedBlock := do
  let bindingMutable := match bindingKind with | .immutable => false | _ => true
  let bindingSlot (name : TSyntax `ident) : TermElabM Name := do
    match bindingKind with
    | .assignment => return (← lookup scope name).slot
    | _ => mkFreshUserName `sourceSlot
  let bindAndContinue (binding : Binding) (raw : TSyntax `doElem)
      (native : Option (TSyntax `doElem)) (calls : Option (Array Trace))
      (rest : List (TSyntax `doElem)) (invalidateHeap : Bool := false) : PrepareM PreparedBlock := do
    let raw ← match raw with
      | `(doElem| let $name:ident : $type:term := $expression:term) =>
          rawBinding bindingKind name type expression
      | `(doElem| let $name:ident : $type:term ← $expression:term) =>
          rawBinding bindingKind name type expression true
      | _ => throwError "a prepared source binding must have its resolved type"
    let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
    let native ← native.mapM fun native => do
      let `(doElem| let $_:ident : $type:term := $expression:term) := native
        | throwError "a prepared mathematical local must be a typed value binding"
      `(doElem| let $nativeName:ident : $type := $expression)
    let binding := { binding with
      nativeName, mutable := bindingMutable, slot := ← bindingSlot binding.name }
    let scope := if invalidateHeap then invalidateObservations scope else scope
    let ⟨rawRest, nativeRest, later, returned, normal⟩ ← sequence names imports resultType
      (binding :: scope) rest .immutable allowFallthrough localReturn
    return ⟨#[raw] ++ rawRest,
      (fun native rest => #[native] ++ rest) <$> native <*> nativeRest,
      (· ++ ·) <$> calls <*> later, returned, normal⟩
  let continueChoice (raw : TSyntax `doElem) (yes no : PreparedBlock)
      (available : Bool)
      (choose : Bool → TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
      (trace : Array Trace → Array Trace → Value → Value → Binding → Trace)
      (rest : List (TSyntax `doElem)) : PrepareM PreparedBlock := do
    if yes.normalScope?.isSome && no.normalScope?.isSome then
      let mutable := (visibleBindings scope).filter (·.mutable)
      let stateType ← resolveType (← stateType mutable.toList)
      let yes ← normalSummary scope mutable stateType yes
      let no ← normalSummary scope mutable stateType no
      let choice ← choiceModel available stateType yes no choose trace
      let mut after := invalidateObservations scope true
      let mut nativePrefix := #[]
      let mut calls : Option (Array Trace) := none
      if let some choice := choice then
        let type ← termOfExpr stateType.nativeType
        nativePrefix := #[← `(doElem| let $(choice.result.name):ident : $type := $(choice.native))]
        after := scope
        for binding in mutable, index in [:mutable.size] do
          let projection ← fieldProjection mutable.size index ⟨choice.result.name.raw⟩
          let projected ← value [choice.result] projection
          let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
          after := after.map fun current =>
            if current.slot == binding.slot then
              { current with nativeName, model? := projected.model?.map (·.toBindingModel) }
            else current
          let type ← termOfExpr binding.type.nativeType
          nativePrefix := nativePrefix.push
            (← `(doElem| let $nativeName:ident : $type := $projection))
        calls := some #[choice.trace]
      let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn
      return { continued with
        raw := #[raw] ++ continued.raw
        native? := (fun _ native => nativePrefix ++ native) <$> choice <*> continued.native?
        calls? := (· ++ ·) <$> calls <*> continued.calls? }
    if yes.normalScope?.isNone && no.normalScope?.isNone then
      -- Unreachable source statements still belong to the typed source body,
      -- but do not contribute to its mathematical result or recursive calls.
      let recursive := (← get).currentRecursive
      let continued ← sequence names imports resultType scope rest .immutable true localReturn
      modify fun state => { state with currentRecursive := recursive }
      let choice ← choiceModel available resultType yes no choose trace
      let native ← choice.mapM fun choice => do
        return #[← `(doElem| return $(choice.native))]
      let returned := choice.map fun choice => ({
        type := resultType, raw := ⟨choice.result.rawName.raw⟩
        model? := choice.result.model?.map fun model => {
          toBindingModel := model, native := choice.native } } : Value)
      return (⟨#[raw] ++ continued.raw, native,
        choice.map (fun choice => #[choice.trace]), returned, none⟩ : PreparedBlock)
    -- Mixed normal/return control is preserved without asserting one pure
    -- output summary. The enclosing continuation runs only on normal paths.
    if localReturn then
      throwError "early return inside a value-producing branch needs a local-return boundary; \
        use a source function for that computation"
    let continued ← sequence names imports resultType (invalidateObservations scope true)
      rest .immutable allowFallthrough localReturn
    return { continued with raw := #[raw] ++ continued.raw, native? := none, calls? := none }
  match elements with
  | [] =>
      if allowFallthrough then return ⟨#[], some #[], some #[], none, some scope⟩
      throwError "a value-producing source block must end with a return"
  | element :: rest => withRef element do
    -- The mathematical view uses local versions; rawBinding retains actual
    -- mutable declarations and assignments for the shared source semantics.
    if let `(doElem| let mut $name:ident $[: $annotation:term]? := $expression:term) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? := $expression)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $expression:term) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn
    if let `(doElem| $name:ident := $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type := $expression)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn
    if let `(doElem| $name:ident ← $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $expression:term)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn
    if let `(doElem| $name:ident ← $rhs:doElem) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $rhs:doElem)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn
    if let `(doElem| with_scratch do $body:doSeq) := element then
      if localReturn then
        throwErrorAt element "a scratch scope inside a value-producing branch needs a local-return boundary; \
          use a source function for that computation"
      let body ← sequence names imports resultType scope (getDoElems body).toList .immutable true
      let bodySyntax : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (body.raw.map (·.raw))⟩
      let raw ← `(doElem| with_scratch do $bodySyntax:doSeq)
      if body.normalScope?.isNone && rest.isEmpty then
        return ⟨#[raw], none, none, none, none⟩
      let after := invalidateObservations
        (body.normalScope?.map (closeScope scope) |>.getD scope) true
      let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn
      return { continued with
        raw := #[raw] ++ continued.raw, native? := none, calls? := none
        returned? := if body.normalScope?.isSome then continued.returned? else none
        normalScope? := if body.normalScope?.isSome then continued.normalScope? else none }
    if let `(doElem| while $condition:term do $body:doSeq) := element then
      if localReturn then
        throwErrorAt element "general while inside a value-producing branch needs a local-return boundary; \
          use a source function for that computation"
      let loopScope := invalidateObservations scope true
      let boolType ← resolveType (← `(Bool))
      let guardElements ← returnElements condition
      let ⟨guardRaw, _, _, _, _⟩ ← sequence names imports boolType loopScope guardElements.toList
      let ⟨bodyRaw, _, _, _, _⟩ ← sequence names imports resultType loopScope
        (getDoElems body).toList .immutable true
      let ⟨rawRest, _, _, returned, normal⟩ ← sequence names imports resultType loopScope rest .immutable true
      let guard ← doTerm guardRaw
      let body : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (bodyRaw.map (·.raw))⟩
      return ⟨#[← `(doElem| while $guard:term do $body:doSeq)] ++ rawRest, none, none, returned, normal⟩
    if let `(doElem| for $pattern:term in $collection:term do $body:doSeq) := element then
      if localReturn then
        throwErrorAt element "a range inside a value-producing branch needs a local-return boundary"
      let index ← match pattern with
        | `($name:ident) => pure name
        | `(_) => pure (mkIdent (← mkFreshUserName `index))
        | _ => throwErrorAt pattern "a finite Nat range binds one index or _"
      let (start, stop, stride) ← match collection with
        | `([ : $stop ]) => pure (← `(0), stop, ← `(1))
        | `([ $start : $stop ]) => pure (start, stop, ← `(1))
        | `([ : $stop : $stride ]) => pure (← `(0), stop, stride)
        | `([ $start : $stop : $stride ]) => pure (start, stop, stride)
        | _ => throwErrorAt collection "represented for currently expects a finite Nat range"
      let captured := lexicalBindings scope
      let stateSyntax ← stateType captured.toList
      let stateNativeType ← resolveType stateSyntax
      let natType ← resolveType (← `(Nat))
      let start ← value scope start (some natType)
      let stop ← value scope stop (some natType)
      let stride ← value scope stride (some natType)
      let tag := mkIdent (← mkFreshUserName `rangeSite)
      let cursor := mkIdent (← mkFreshUserName `rangeIndex)
      let initial := mkIdent (← mkFreshUserName `rangeState)
      let indexBinding := { (← parameterBinding cursor natType) with name := index }
      let stateBinding ← parameterBinding initial stateNativeType
      let mut bodyScope := #[]
      let mut nativePrefix := #[]
      for binding in captured, position in [:captured.size] do
        let field ← fieldProjection captured.size position ⟨initial.raw⟩
        let projected ← value [stateBinding] field
        let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
        bodyScope := bodyScope.push { binding with
          nativeName := nativeName
          model? := projected.model?.map (·.toBindingModel) }
        let type ← termOfExpr binding.type.nativeType
        nativePrefix := nativePrefix.push (← `(doElem| let $nativeName:ident : $type := $field))
      let sourceBodyScope := match pattern with
        | `($_:ident) => indexBinding :: bodyScope.toList
        | _ => bodyScope.toList
      let preparedBody ← sequence names imports resultType sourceBodyScope
        (getDoElems body).toList .immutable true
      let rawBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (preparedBody.raw.map (·.raw))⟩
      let rawCollection ← `([ $(start.raw) : $(stop.raw) : $(stride.raw) ])
      let raw ← `(doElem| source_range_site% $tag:ident ($pattern:term, $rawCollection:term)
        do $rawBody:doSeq)
      let sourceOnly : PrepareM PreparedBlock := do
        let continued ← sequence names imports resultType (invalidateObservations scope true)
          rest .immutable allowFallthrough localReturn
        return { continued with raw := #[raw] ++ continued.raw, native? := none, calls? := none }
      let some normalScope := preparedBody.normalScope? | return ← sourceOnly
      let some native := preparedBody.native? | return ← sourceOnly
      let some calls := preparedBody.calls? | return ← sourceOnly
      let some startModel := start.model? | return ← sourceOnly
      let some stopModel := stop.model? | return ← sourceOnly
      let some strideModel := stride.model? | return ← sourceOnly
      unless captured.all (·.model?.isSome) do return ← sourceOnly
      let closed := closeScope bodyScope.toList normalScope
      -- Resolve the post-state by lexical slot, using hygienic mathematical
      -- names only for this proof-side tuple; no source binding is appended.
      let post := closed.map fun binding => { binding with name := binding.nativeName }
      let bodyReturned ← value post (← stateValue post.toArray) (some stateNativeType)
      let some returnedModel := bodyReturned.model? | return ← sourceOnly
      let bodyTerm ← doTerm (nativePrefix ++ native ++
        #[← `(doElem| return $(returnedModel.native))])
      let bodyNative ← `(fun ($cursor:ident : Nat) ($initial:ident : $stateSyntax) => Id.run $bodyTerm)
      let indices ← `(List.range' $(startModel.native)
        (($(stopModel.native) - $(startModel.native) + $(strideModel.native) - 1) /
          $(strideModel.native)) $(strideModel.native))
      let mutableType ← stateType (captured.filter (·.mutable)).toList
      let mutableName := mkIdent (← mkFreshUserName `mutableState)
      let stepIndex := mkIdent (← mkFreshUserName `index)
      let initialValue ← value (captured.toList.map fun binding => { binding with name := binding.nativeName })
        (← fieldsTerm (captured.map (fun binding => (⟨binding.nativeName.raw⟩ : TSyntax `term))).toList)
        (some stateNativeType)
      let some initialModel := initialValue.model? | return ← sourceOnly
      let packedMutable ← packMutableState captured initialModel.native ⟨mutableName.raw⟩
      let embedding ← `(fun ($mutableName:ident : $mutableType) => $packedMutable)
      let nextState ← `($bodyNative $stepIndex:ident $packedMutable)
      let nextMutable ← mutableState captured nextState
      let mutableStep ← `(fun ($mutableName:ident : $mutableType) ($stepIndex:ident : Nat) => $nextMutable)
      let initialMutable ← mutableState captured initialModel.native
      let nativeFold ← `(($indices).foldl $mutableStep $initialMutable)
      let nativeResult := Lean.Syntax.mkApp embedding #[nativeFold]
      let resultName := mkIdent (← mkFreshUserName `rangeValue)
      let resultRaw := mkIdent (← mkFreshUserName `rangeSource)
      let resultObserved := mkIdent (← mkFreshUserName `rangeObserved)
      -- Replace hygienic local versions by their mathematical expressions for
      -- the theorem view. The emitted ordinary function keeps those versions.
      let nativeSubstitution := captured.filterMap fun binding =>
        binding.model?.map (fun model => (binding.nativeName.getId, model.model.raw))
      let theoremResult : TSyntax `term := ⟨nativeResult.raw.rewriteBottomUp fun node =>
        if node.isIdent then
          ((nativeSubstitution.find? (fun entry => entry.1 == node.getId)).map (·.2)).getD node
        else node⟩
      let result : Binding := {
        name := resultName, type := stateNativeType, rawName := resultRaw, relationName := resultObserved
        model? := some {
          model := theoremResult, rawModel := ⟨resultRaw.raw⟩
          observation := if stateNativeType.isIdentity then .refl else .named resultObserved.getId } }
      modify fun state => { state with ranges := state.ranges.push {
        tag := tag.getId, captured, state := stateBinding, index := indexBinding, body := calls,
        returned := bodyReturned, bodyNative, start, stop, stride, result,
        embedding, mutableStep, initialMutable, indices } }
      let mut after := scope
      let mut nativeAfter := #[← `(doElem| let $resultName:ident : $stateSyntax := $nativeResult)]
      for binding in captured, position in [:captured.size] do
        let projection ← fieldProjection captured.size position ⟨resultName.raw⟩
        let projected ← value [result] projection
        let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
        after := after.map fun current => if current.slot == binding.slot then
          { current with nativeName, model? := projected.model?.map (·.toBindingModel) } else current
        nativeAfter := nativeAfter.push (← `(doElem| let $nativeName:ident := $projection))
      let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn
      return { continued with
        raw := #[raw] ++ continued.raw
        native? := (nativeAfter ++ ·) <$> continued.native?
        calls? := (#[Trace.range tag.getId #[initialValue] result
          (calls.all Trace.preservesArrays)] ++ ·) <$> continued.calls? }
    let statementConditional? ← match element with
      | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
          pure (some (condition, yes, no))
      | `(doElem| if $condition:term then $yes:doSeq) =>
          pure (some (condition, yes, (⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩ : TSyntax ``doSeq)))
      | _ => pure none
    if let some (condition, yes, no) := statementConditional? then
      let condition ← value scope condition
      expect element (← resolveType (← `(Bool))) condition.type
      let yes ← sequence names imports resultType scope (getDoElems yes).toList .immutable true localReturn
      let no ← sequence names imports resultType scope (getDoElems no).toList .immutable true localReturn
      let yesBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (yes.raw.map (·.raw))⟩
      let noBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (no.raw.map (·.raw))⟩
      let raw ← `(doElem| if $(condition.raw) then $yesBody:doSeq else $noBody:doSeq)
      let choose (mathematical : Bool) (yes no : TSyntax `term) := do
        let model ← condition.requireModel
        let condition := if mathematical then model.model else model.native
        `(if $condition then $yes else $no)
      return ← continueChoice raw yes no condition.model?.isSome choose
        (Trace.conditional condition) rest
    if let `(doElem| match $matched:term with
        | $first:term => $firstBody:doSeq
        | $second:term => $secondBody:doSeq) := element then
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
          else throwErrorAt element "a List match needs exactly [] and head :: tail branches"
        let inspected := mkIdent (← mkFreshUserName `listParts)
        let payload := mkIdent (← mkFreshUserName `listFields)
        let someElements := #[
          ← `(doElem| let $head:ident := $payload:ident.1),
          ← `(doElem| let $tail:ident := $payload:ident.2)] ++ getDoElems consBody
        let someBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (someElements.map (·.raw))⟩
        let read ← `(doElem| let $inspected:ident := List.uncons $matched:term)
        let selected ← `(doElem| match $inspected:ident with
          | none => $nilBody:doSeq
          | some $payload:ident => $someBody:doSeq)
        return ← sequence names imports resultType scope (read :: selected :: rest)
          .immutable allowFallthrough localReturn
      let .option payloadType := discriminant.type
        | throwErrorAt matched "source matching currently supports List and Option values"
      let (noneBody, payloadPattern, someBody) ←
        if isNonePattern first then do
          let some payload := somePattern? second
            | throwErrorAt second "expected a some payload option pattern"
          pure (firstBody, payload, secondBody)
        else if isNonePattern second then do
          let some payload := somePattern? first
            | throwErrorAt first "expected a some payload option pattern"
          pure (secondBody, payload, firstBody)
        else throwErrorAt element "an Option match needs exactly none and some payload branches"
      let (payloadName, payloadBindings) ← preparePayloadPattern payloadPattern payloadType
      let payloadRaw := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_source"))
      let payloadRelation := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_represented"))
      let payloadNative := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_native"))
      let payload : Binding := {
        name := payloadName, nativeName := payloadNative
        type := payloadType, rawName := payloadRaw, relationName := payloadRelation
        model? := discriminant.model?.map fun _ => {
          model := ⟨payloadNative.raw⟩, rawModel := ⟨payloadRaw.raw⟩
          observation := if payloadType.isIdentity then .refl else .named payloadRelation.getId } }
      let absent ← sequence names imports resultType scope (getDoElems noneBody).toList .immutable true localReturn
      let present ← sequence names imports resultType (payload :: scope)
        (payloadBindings ++ getDoElems someBody).toList .immutable true localReturn
      let noneBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (absent.raw.map (·.raw))⟩
      let someBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (present.raw.map (·.raw))⟩
      let raw ← `(doElem| match $(discriminant.raw):term with
        | none => $noneBody:doSeq
        | some $payloadName:ident => $someBody:doSeq)
      let choose (mathematical : Bool) (absent present : TSyntax `term) := do
        let model ← discriminant.requireModel
        let discriminant := if mathematical then model.model else model.native
        let type ← termOfExpr payloadType.nativeType
        `(Option.elim $discriminant $absent (fun ($payloadNative:ident : $type) => $present))
      return ← continueChoice raw absent present discriminant.model?.isSome choose
        (Trace.optionMatch discriminant payload) rest
    if rest.isEmpty then
      let terminal? ← match element with
        | `(doElem| return $expression:term) =>
            pure (if (conditionalParts? expression).isSome || (matchParts? expression).isSome then
              some expression else none)
        | _ => pure none
      if let some expression := terminal? then
        let temporary := mkIdent (← mkFreshUserName `branchResult)
        let type ← termOfExpr resultType.nativeType
        return ← sequence names imports resultType scope [
          ← `(doElem| let $temporary:ident : $type ← ($expression:term)),
          ← `(doElem| return $temporary:ident)] .immutable allowFallthrough localReturn
    -- An unparenthesized `if` after `←` is a `doIf`, not a term.
    -- Normalize that parser shape before the shared typed conditional path.
    if let `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      if let `(doElem| if $test:term then $yes:doSeq else $no:doSeq) := rhs then
        let yesTerm ← branchTerm yes
        let noTerm ← branchTerm no
        let expression ← `(if $test:term then $yesTerm:term else $noTerm:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence names imports resultType scope (normalized :: rest) bindingKind allowFallthrough localReturn
      if let `(doElem| match $discriminant:term with
          | $first:term => $firstBody:doSeq
          | $second:term => $secondBody:doSeq) := rhs then
        let firstBody ← branchTerm firstBody
        let secondBody ← branchTerm secondBody
        let expression ← `(match $discriminant:term with
          | $first:term => $firstBody:term
          | $second:term => $secondBody:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence names imports resultType scope (normalized :: rest) bindingKind allowFallthrough localReturn
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
          let select ← match bindingKind with
            | .assignment => `(doElem| $name:ident ← ($optionMatch:term))
            | .mutable => `(doElem| let mut $name:ident : $annotation ← ($optionMatch:term))
            | .immutable => `(doElem| let $name:ident : $annotation ← ($optionMatch:term))
          return ← sequence names imports resultType scope (read :: select :: rest) .immutable allowFallthrough localReturn
        let .option payloadType := discriminant.type
          | throwErrorAt matched "native matching currently supports List and Option values"
        let (noneBody, payloadPattern, someBody) ←
          if isNonePattern first then do
            let some payload := somePattern? second
              | throwErrorAt second "expected a some payload option pattern"
            pure (firstBody, payload, secondBody)
          else if isNonePattern second then do
            let some payload := somePattern? first
              | throwErrorAt first "expected a some payload option pattern"
            pure (secondBody, payload, firstBody)
          else throwErrorAt expression "an Option match needs exactly none and some payload branches"
        let (payloadName, payloadBindings) ← preparePayloadPattern payloadPattern payloadType
        let selectedType ← resolveType annotation
        let noneElements ← returnElements noneBody
        let someElements := payloadBindings ++ (← returnElements someBody)
        let payloadRaw := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_source"))
        let payloadRelation := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_represented"))
        let payloadNative := mkIdent (← mkFreshUserName (payloadName.getId.appendAfter "_native"))
        let payload : Binding := {
          name := payloadName, nativeName := payloadNative, type := payloadType, rawName := payloadRaw,
          relationName := payloadRelation
          model? := discriminant.model?.map fun _ => {
            model := ⟨payloadNative.raw⟩, rawModel := ⟨payloadRaw.raw⟩
            observation := if payloadType.isIdentity then .refl else .named payloadRelation.getId } }
        let ⟨noneRaw, noneNative, noneCalls, noneResult, _⟩ ←
          sequence names imports selectedType scope noneElements.toList .immutable false true
        let ⟨someRaw, someNative, someCalls, someResult, _⟩ ←
          sequence names imports selectedType (payload :: scope) someElements.toList .immutable false true
        let some noneResult := noneResult
          | throwErrorAt noneBody "a value-producing branch must return a value"
        let some someResult := someResult
          | throwErrorAt someBody "a value-producing branch must return a value"
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let joinSlot ← makeJoinSlot slot selectedType.coreTy
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let nativeName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_native"))
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
            (fun ($payloadNative:ident : $payloadNativeType) => Id.run $someNativeBody:term))
          let model ← `(Option.elim $(discriminant.model) $(noneResult.model)
            (fun ($payloadNative:ident : $payloadNativeType) => $(someResult.model)))
          pure (nativeChoice, ({
            model, rawModel := ⟨rawName.raw⟩
            observation := if selectedType.isIdentity then .refl else .named relationName.getId } : BindingModel))
        let binding : Binding := {
          name, nativeName, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          slot := ← bindingSlot name
          mutable := bindingMutable }
        let ⟨rawRest, nativeRest, later, returned, normal⟩ ←
          sequence names imports resultType (binding :: scope) rest .immutable allowFallthrough localReturn
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $(joinSlot.type) := $(joinSlot.initial)),
          ← `(doElem| match $(discriminant.raw):term with
            | none => $noneBlock:doSeq
            | some $payloadName:ident => $someBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $nativeName:ident : $nativeType := $nativeChoice)
        let calls : Option (Array Trace) := do
          let _ ← choice
          let noneCalls ← noneCalls
          let someCalls ← someCalls
          let later ← later
          pure (#[.optionMatch discriminant payload noneCalls someCalls noneResult someResult binding] ++ later)
        return ⟨rawPrefix ++ (← joinSlot.continuation name rawRest bindingKind),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest, calls, returned, normal⟩
      if let some (test, yes, no) := conditionalParts? expression then
        let some annotation := annotation
          | throwErrorAt name "a native conditional binding requires an explicit result type"
        let selectedType ← resolveType annotation
        let condition ← value scope test
        expect test (← resolveType (← `(Bool))) condition.type
        let yesElements ← returnElements yes
        let noElements ← returnElements no
        let ⟨yesRaw, yesNative, yesCalls, yesResult, _⟩ ←
          sequence names imports selectedType scope yesElements.toList .immutable false true
        let ⟨noRaw, noNative, noCalls, noResult, _⟩ ←
          sequence names imports selectedType scope noElements.toList .immutable false true
        let some yesResult := yesResult
          | throwErrorAt yes "a value-producing branch must return a value"
        let some noResult := noResult
          | throwErrorAt no "a value-producing branch must return a value"
        let nativeType ← termOfExpr selectedType.nativeType
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let joinSlot ← makeJoinSlot slot selectedType.coreTy
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let nativeName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_native"))
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
            observation := if selectedType.isIdentity then .refl else .named relationName.getId } : BindingModel))
        let binding : Binding := {
          name, nativeName, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          slot := ← bindingSlot name
          mutable := bindingMutable }
        let ⟨rawRest, nativeRest, later, returned, normal⟩ ←
          sequence names imports resultType (binding :: scope) rest .immutable allowFallthrough localReturn
        let rawPrefix := #[
          ← `(doElem| let mut $slot:ident : $(joinSlot.type) := $(joinSlot.initial)),
          ← `(doElem| if $(condition.raw) then $yesBlock:doSeq else $noBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $nativeName:ident : $nativeType := $nativeChoice)
        let calls : Option (Array Trace) := do
          let _ ← choice
          let yesCalls ← yesCalls
          let noCalls ← noCalls
          let later ← later
          pure (#[.conditional condition yesCalls noCalls yesResult noResult binding] ++ later)
        return ⟨rawPrefix ++ (← joinSlot.continuation name rawRest bindingKind),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest, calls, returned, normal⟩
    if binding?.isNone then
      let destructuring? := match element with
        | `(doElem| let $pattern:term ← $expression:term) => some (pattern, expression, true)
        | `(doElem| let $pattern:term := $expression:term) => some (pattern, expression, false)
        | _ => none
      if let some (pattern, expression, action) := destructuring? then
        let parsed ← prepareMacro (checkedBindingPattern pattern)
        let annotation := match parsed with | .typed _ type => some type | _ => none
        let install (type : NativeType) (expression : TSyntax `term) : PrepareM PreparedBlock := do
          let name := mkIdent (← mkFreshUserName `pattern)
          let bindings ← patternBindings parsed type ⟨name.raw⟩
          let initial ← if action then
              `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term)
            else `(doElem| let $name:ident $[: $annotation:term]? := $expression:term)
          return ← sequence names imports resultType scope
            (initial :: bindings.toList ++ rest) .immutable allowFallthrough localReturn
        let canonical ← canonicalCall? imports scope expression
        if !action then
          if let some call := canonical then
            let rewritten ← `(doElem| let $pattern:term ← $call:term)
            return ← sequence names imports resultType scope (rewritten :: rest)
              .immutable allowFallthrough localReturn
          if let some (called, rebuild) ← hoistValueCall? imports scope expression then
            let name := mkIdent (← mkFreshUserName `sourceValue)
            let called ← `(doElem| let $name:ident ← $called:term)
            let expression ← rebuild ⟨name.raw⟩
            let rewritten ← `(doElem| let $pattern:term := $expression:term)
            return ← sequence names imports resultType scope (called :: rewritten :: rest)
              .immutable allowFallthrough localReturn
          let result ← value scope expression (← annotation.mapM fun stx => return ← resolveType stx)
          return ← install result.type expression
        let expression := canonical.getD expression
        if let some (operation, _) ← operationCall? names imports scope expression then
          return ← install operation.result expression
        if (conditionalParts? expression).isSome || (matchParts? expression).isSome then
          let some annotation := annotation
            | throwErrorAt pattern "a branching destructuring binding requires its result type"
          return ← install (← resolveType annotation) expression
        let raw ← match expression with
          | `(source_raw_value% ($raw)) => pure raw
          | _ => prepareRawOperands scope expression
        let headers ← rawHeaders names
        let rawScope := scope.map fun binding => (binding.name, binding.type.coreTy)
        let (bindings, rewritten) ← prepareMacro (normalizeRawCall headers rawScope raw)
        let expression ← `(source_raw_value% ($rewritten))
        if !bindings.isEmpty then
          let rewritten ← `(doElem| let $pattern:term ← $expression:term)
          return ← sequence names imports resultType scope
            ((← markRawElements bindings).toList ++ rewritten :: rest)
            .immutable allowFallthrough localReturn
        let type ← prepareMacro (inferRawBindingType headers rawScope rewritten)
        return ← install (← resolveType (← rawTypeTerm type)) expression
    match element with
    | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
        if let some call ← canonicalCall? imports scope expression then
          let binding ← `(doElem| let $name:ident $[: $annotation:term]? ← $call:term)
          return ← sequence names imports resultType scope (binding :: rest) bindingKind allowFallthrough localReturn
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceValue)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let binding ← match bindingKind with
            | .assignment => `(doElem| $name:ident := $rewritten:term)
            | .mutable => `(doElem| let mut $name:ident $[: $annotation:term]? := $rewritten:term)
            | .immutable => `(doElem| let $name:ident $[: $annotation:term]? := $rewritten:term)
          return ← sequence names imports resultType scope (call :: binding :: rest) .immutable allowFallthrough localReturn
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
        let operation? ← operationCall? names imports scope expression
        let some (operation, arguments) := operation? | do
          let raw ← match expression with
            | `(source_raw_value% ($raw)) => pure raw
            | _ => prepareRawOperands scope expression
          let headers ← rawHeaders names
          let rawScope := scope.map fun binding => (binding.name, binding.type.coreTy)
          let (bindings, rewritten) ← prepareMacro (normalizeRawCall headers rawScope raw)
          if !bindings.isEmpty then
            let expression ← `(source_raw_value% ($rewritten))
            let call ← match bindingKind with
              | .immutable => `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term)
              | .mutable => `(doElem| let mut $name:ident $[: $annotation:term]? ← $expression:term)
              | .assignment => `(doElem| $name:ident ← $expression:term)
            return ← sequence names imports resultType scope
              ((← markRawElements bindings).toList ++ call :: rest) .immutable allowFallthrough localReturn
          let type ← prepareMacro (inferRawBindingType headers rawScope rewritten)
          let nativeType ← resolveType (← rawTypeTerm type)
          if let some annotation := annotation then
            expect annotation (← resolveType annotation) nativeType
          let type ← rawTypeTerm type
          return ← bindAndContinue {
            name, type := nativeType, rawName := name, relationName := name }
            (← `(doElem| let $name:ident : $type ← $rewritten:term)) none none rest true
        if let some annotation := annotation then expect annotation (← resolveType annotation) operation.result
        let (invocation, raw, native) ← prepareInvocation names scope name operation arguments
        let rawType ← rawTypeTerm operation.result.coreTy
        let nativeType ← termOfExpr operation.result.nativeType
        bindAndContinue invocation.result
          (← `(doElem| let $name:ident : $rawType ← $raw:term))
          (← native.mapM fun native => `(doElem| let $name:ident : $nativeType := $native))
          (native.map fun _ => #[.call invocation]) rest operation.model?.isNone
    | `(doElem| return) =>
        let returned ← `(doElem| return ())
        return ← sequence names imports resultType scope (returned :: rest)
          .immutable allowFallthrough localReturn
    | `(doElem| return $expression:term) =>
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceResult)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let returned ← `(doElem| return $rewritten:term)
          return ← sequence names imports resultType scope (call :: returned :: rest)
            .immutable allowFallthrough localReturn
        let result ← value scope expression (some resultType)
        expect element resultType result.type
        let native ← result.model?.mapM fun model => do
          return #[← `(doElem| return $(model.native))]
        let recursive := (← get).currentRecursive
        let continued ← sequence names imports resultType scope rest .immutable true localReturn
        modify fun state => { state with currentRecursive := recursive }
        return ⟨#[← `(doElem| return $(result.raw))] ++ continued.raw,
          native, some #[], some result, none⟩
    | `(doElem| $expression:term) =>
        let called := (← canonicalCall? imports scope expression).getD expression
        let operation? ← operationCall? names imports scope called
        if let some (operation, arguments) := operation? then
          unless operation.result.coreTy == .unit do
            throwErrorAt expression "a standalone source call must return Unit; bind its result"
          let ignored := mkIdent (← mkFreshUserName `ignoredResult)
          let (invocation, raw, native) ← prepareInvocation names scope ignored operation arguments
          let after := if operation.model?.isNone then invalidateObservations scope else scope
          let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn
          let nativeType ← termOfExpr operation.result.nativeType
          let nativePrefix ← native.mapM fun native =>
            `(doElem| let $ignored:ident : $nativeType := $native)
          return { continued with
            raw := #[← `(doElem| $raw:term)] ++ continued.raw
            native? := (fun binding rest => #[binding] ++ rest) <$> nativePrefix <*> continued.native?
            calls? := (fun _ rest => #[.call invocation] ++ rest) <$> native <*> continued.calls? }
        else
          let raw ← match called with
            | `(source_raw_value% ($raw)) => pure raw
            | _ => prepareRawOperands scope called
          let headers ← rawHeaders names
          let rawScope := scope.map fun binding => (binding.name, binding.type.coreTy)
          let (bindings, rewritten) ← prepareMacro (normalizeRawCall headers rawScope raw)
          if !bindings.isEmpty then
            let action ← `(doElem| source_raw_value% ($rewritten))
            return ← sequence names imports resultType scope
              ((← markRawElements bindings).toList ++ action :: rest) .immutable allowFallthrough localReturn
          prepareMacro (checkRawAction headers rawScope rewritten)
          let ⟨rawRest, _, _, returned, normal⟩ ← sequence names imports resultType
            (invalidateObservations scope) rest .immutable allowFallthrough localReturn
          return ⟨#[← `(doElem| $rewritten:term)] ++ rawRest, none, none, returned, normal⟩
    | _ => throwError "source blocks support typed product/Option patterns, lets, let mut and assignment, \
        source calls and raw operations, conditional/match bindings, with_scratch, \
        finite Nat ranges, general while and return; \
        break/continue and general loops inside value-producing branches are not supported here"

private def prepareFunction (names : DeclarationNames)
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
      native := ⟨(names.modelName name).raw⟩
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
private def completeModels (names : DeclarationNames) (prepared : Preparation) :
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
  let retained := functions.toList.flatMap fun fn =>
    fn.model?.map (fun model => modelRangeTags ranges model.calls) |>.getD []
  ranges := ranges.filter (fun range => retained.contains range.tag)
  return ({ prepared with functions, ranges },
    completed.filterMap fun fn => fn.model?.map (fun _ => fn.name.getId))

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
    | .pure _ | .raw _ => do
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
  unless callback.accumulator.isIdentity do callbackArgs := callbackArgs.push ⟨accObserved.raw⟩
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

private def nativeDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← termOfExpr parameter.type.nativeType
    `(bracketedBinder| ($(parameter.name):ident : $type))
  let result ← termOfExpr fn.result.nativeType
  let name := names.modelName fn.name
  return (← `(command|
    /-- Ordinary mathematical function generated from the same represented source block. -/
    def $name:ident $parameters:bracketedBinder* : $result := Id.run $(model.nativeBody)
      $(model.termination):suffix)).raw

private def normalizeAction : TermElabM (TSyntax `tactic) :=
  `(tactic| simp only [Id.run, Id.instMonad, Bind.bind, Pure.pure, Functor.map,
    MonadLift.monadLift, ExceptT.lift,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
    StateT.bind, StateT.pure, StateT.map, Part.bind_some, Part.map_some])

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

private def correspondenceHeader (names : DeclarationNames) (fn : Function) :
    TermElabM CorrespondenceHeader := do
  let nativeName := names.modelName fn.name
  let rawName := fieldName names.sourceFamily fn.name
  let rawEquation := fieldName names.sourceFamily fn.name "_eq"
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
    | .pure _ | .raw _ => rawArguments := rawArguments.push ⟨parameter.name.raw⟩
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
    | .pure _ | .raw _ => `(by
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

private def RangeRegistration.site (range : RangeRegistration) : TermElabM ActualRangeSite :=
  match range.site? with
  | some site => pure site
  | none => throwError "the prepared range has no checked actual source site"

/-- Align source declarations by lexical occurrence, not by a name lookup.
Anonymous Core coordinates remain in the full source scope. -/
private def RangeRegistration.slots (range : RangeRegistration) : TermElabM (Array Nat) := do
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

private def RangeRegistration.select (range : RangeRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let site ← range.site
  let fields ← sourceFields site.scope.size locals
  let positions ← range.slots
  fieldsTerm (← positions.toList.mapM fun index =>
    match fields[index]? with
    | some field => pure field
    | none => throwError "the selected range coordinate is outside its actual locals")

private structure TraceContext where
  heap : TSyntax `term
  relations : Array RetainedObservation
  known : Array (Name × TSyntax `term)
  scalarEqualities : Array (TSyntax `term)
  shape : TSyntax `term
  contents : TSyntax `term

private abbrev TraceFinish := TraceContext → TermElabM (Array (TSyntax `tactic))

private abbrev RangeBodyProof :=
  Array Trace → Value → TSyntax `term → Array RetainedObservation →
    Array (Name × TSyntax `term) → Bool → TraceFinish →
      TermElabM (Array (TSyntax `tactic))

/-- Prove the original named range in its full source coordinates. The fold is
only a mathematical view; body calls retain their actual control and heap. -/
private def rangeRelationProof (range : RangeRegistration) (initialValue : Value)
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
    | .range _ _ _ _ :: _ =>
        throwError "actual ranges are proved in their enclosing Control/Locals continuation"
  let type ← actualTypeTerm returned.type.coreTy
  `(($action : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $type))

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

private partial def relationTrace (trace : Array Trace) (returnedValue : Value)
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
  let actualBranches := actualBranches || finish?.isSome || trace.any Trace.containsRange
  let mut tactics := #[← normalizeAction]
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
    let mut joinTactics := #[← `(tactic|
      have $armObserved:ident : ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
          $(armModel.model) $actual $(context.heap) := $observed),
      ← `(tactic|
      have $joined:ident : ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
          $(resultModel.model) $actual $(context.heap) := by
        simpa only [$selected,*] using $armObserved:ident)]
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
        shape := preserved, contents := preservedContents }
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
            (some (finishChoice yesResult result yesRules rest)) (some context) true
          let noProof ← relationTrace no noResult currentHeap relations known preserveArrays ranges
            (some (finishChoice noResult result noRules rest)) (some context) true
          return tactics ++ #[
            ← `(tactic| have $equality:ident : $(condition.model) = $raw := $observation),
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
          let impossible := mkIdent (← mkFreshUserName `impossiblePayload)
          let payloadObserved := payload.relationName
          let rules := #[
            ← `(Lean.Parser.Tactic.simpLemma| $rawCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| $nativeCase:ident),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_none),
            ← `(Lean.Parser.Tactic.simpLemma| Option.elim_some)]
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
                    simp (config := { failIfUnchanged := false }) only [$rules,*]
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
                    have $payloadObserved:ident : ($payloadRepresentation :
                        Complexity.Language.Representation $payloadType $payloadCore).Rel
                        $(payload.nativeName):ident $(payload.rawName):ident $currentHeap := by
                      simpa only [Complexity.Language.Representation.option, $rawCase:ident,
                        $nativeCase:ident] using $observed:ident
                    simp (config := { failIfUnchanged := false }) only [$rules,*]
                    $someProof:tactic*)]
      | _ => pure ()
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
          let (setup, proof) ← rangeRelationProof range initial currentHeap relations known preserveArrays
            (fun body returned heap observations known strong finish =>
              relationTrace body returned heap observations known strong ranges (some finish))
          tactics := tactics ++ setup
          pure (result, proof)
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
          if payload.type.isIdentity then
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
    tactics := tactics.push (← `(tactic|
      obtain ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident, $extended:ident⟩ :=
        $relationProof))
    if preserveArrays then
      tactics := tactics.push (← `(tactic|
        obtain ⟨$extended:ident, $contents:ident⟩ := $extended:ident))
    let range? : Option RangeRegistration := match instruction with
      | .range tag _ _ _ => ranges.find? (fun range => range.tag == tag)
      | _ => none
    if let some range := range? then
      let selected ← range.select ⟨returned.raw⟩
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
        StateT.bind, StateT.pure, Part.bind_some] at $executed:ident))
    tactics := tactics.push (← `(tactic| rw [$executed:ident]))
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
  if let some finish := finish? then
    return tactics ++ (← finish {
      heap := currentHeap, relations, known, scalarEqualities,
      shape := preserved, contents := preservedContents })
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

private def equationDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let family := names.publicFamily
  let header ← correspondenceHeader names fn
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
      unless argument.type.isIdentity do
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


private def relationDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) (preserveArrays : Bool := false)
    (ranges : Array RangeRegistration := #[]) : TermElabM Syntax := do
  let family := names.publicFamily
  let header ← correspondenceHeader names fn
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
    let termination ← if model.recursive && !(fn.preservesArrays && !preserveArrays) then
        pure model.termination
      else `(Lean.Parser.Termination.suffix|)
    return (← `(command|
      /-- Successful execution observes the native result in its actual final heap
      and retains every previously represented immutable list. -/
      theorem $relationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
          ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder*
          :
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
      unless parameter.type.isIdentity do applied := applied.push ⟨parameter.rawName.raw⟩
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
      unless parameter.type.isIdentity do applied := applied.push ⟨parameter.rawName.raw⟩
    applied := applied.push ⟨heap.raw⟩ ++ inputRelations.map (·.proof)
    let correct := Lean.Syntax.mkApp ⟨strong.raw⟩ applied
    return ← declaration #[
      ← `(tactic| obtain ⟨returned, finish, executed, related, shape, _⟩ := $correct),
      ← `(tactic| exact ⟨returned, finish, executed, related, shape⟩)]
  let mut tactics := #[]
  if !model.calls.any Trace.containsRange && model.calls.any (fun | .call _ => false | _ => true) then
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
  tactics := tactics ++ (← relationTrace model.calls model.returned ⟨heap.raw⟩ inputRelations #[] preserveArrays ranges)
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

private def interfaceDeclarations (names : DeclarationNames) (fn : Function) :
    TermElabM (Array Syntax) := do
  let family := names.publicFamily
  let id := fieldName family fn.name "Id"
  let rawId := fieldName names.sourceFamily fn.name "Id"
  let representation := fieldName family fn.name "_representation"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let result ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeInputType ← inputType fn.parameters.toList
  let nativeResultType ← termOfExpr fn.result.nativeType
  let argumentRepresentation ← inputRepresentation fn.parameters.toList
  let resultRepresentation ← termOfExpr fn.result.representation
  let mut declarations := #[]
  if id.getId != rawId.getId then
    declarations := declarations.push (← `(command|
      abbrev $id:ident := $rawId:ident)).raw
  let representationDeclaration ← `(command|
    /-- Ordinary arguments and the actual result observed in their real source heaps.
    This interface does not assert the existence of a total mathematical model. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $nativeInputType (fun _ => $nativeResultType) { params := [$params,*], result := $result } :=
      Complexity.Language.FunctionRepresentation.ofResult $argumentRepresentation
        (fun _ => $resultRepresentation))
  return declarations.push representationDeclaration.raw

private def refinementDeclaration (names : DeclarationNames) (fn : Function) :
    TermElabM Syntax := do
  let family := names.publicFamily
  let program := mkIdentFrom family (family.getId ++ `program)
  let id := fieldName family fn.name "Id"
  let native := names.modelName fn.name
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
    | .pure _ | .raw _ =>
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

private def registerNativeProgram (names : DeclarationNames) (functions : Array Function) :
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
          let name ← resolveGlobalConstNoOverload (names.modelName fn.name)
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
  let actualRanges ← Complexity.Language.Syntax.elaborateSourceProgramWithSites
    rawFamily rawFunctions libraries false operationFamilies
  let ranges ← prepared.ranges.mapM fun range => do
    let some site := actualRanges.find? (fun site => site.tag == range.tag)
      | throwError "the source emitter did not return the prepared range site"
    pure { range with site? := some site }
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
  for name in modelOrder do
    let some fn := prepared.functions.find? (fun fn => fn.name.getId == name)
      | throwError "the completed mathematical function has no actual source declaration"
    let some model := fn.model?
      | throwError "a source-only function entered mathematical declaration emission"
    elabCommand (← liftTermElabM (nativeDeclaration names fn model))
    if fn.hasExactEquation then
      elabCommand (← liftTermElabM (equationDeclaration names fn model))
    if fn.preservesArrays then
      elabCommand (← liftTermElabM (relationDeclaration names fn model true ranges))
    elabCommand (← liftTermElabM (relationDeclaration names fn model false ranges))
    if fn.exposed then elabCommand (← liftTermElabM (refinementDeclaration names fn))
  registerNativeProgram names prepared.functions

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
