/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Basic

/-!
# Represented value expressions

Prepare typed source values and, when available, their ordinary mathematical
observations. Record construction and projection use the registered field
representations; heap-backed values are never decoded by an invented inverse.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def lookup (scope : List Binding) (name : TSyntax `ident) : TermElabM Binding := do
  let some parameter := scope.find? (fun parameter => parameter.name.getId == name.getId)
    | throwErrorAt name "unknown native source variable '{name.getId}'"
  return parameter

partial def fieldsTerm : List (TSyntax `term) → TermElabM (TSyntax `term)
  | [] => `(())
  | [field] => pure field
  | field :: rest => do `(($field, $(← fieldsTerm rest)))

private def fieldsObservation : List Observation → Observation
  | [] => .refl
  | [field] => field
  | field :: rest => .pair false field (fieldsObservation rest)

def fieldProjection (count index : Nat) (receiver : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut result := receiver
  for _ in [:index] do result ← `(Prod.snd $result)
  if index + 1 < count then `(Prod.fst $result) else pure result

private def projectObservation (purePair first : Bool) (pair : Observation) : Observation :=
  match pair with
  | .pair _ left right => if first then left else right
  | _ => .projection purePair first pair

private def fieldObservation (count index : Nat) (receiver : Observation) : Observation := Id.run do
  let mut result := receiver
  for _ in [:index] do result := projectObservation false false result
  if index + 1 < count then return projectObservation false true result else return result

partial def value (scope : List Binding) (stx : TSyntax `term)
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
          rawModel := ← nativeBuild (← `(($(left.rawModel) : $inputSyntax)))
            (← `(($(right.rawModel) : $inputSyntax)))
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
    let nativeType ← termOfExpr pair.type.nativeType
    let rawType ← actualTypeTerm pair.type.coreTy
    return ({
      type := if first then left else right,
      raw := apply pair.raw
      model? := ← pair.model?.mapM fun model => do
        return {
          native := apply (← `(($(model.native) : $nativeType)))
          model := apply (← `(($(model.model) : $nativeType)))
          rawModel := apply (← `(($(model.rawModel) : $rawType)))
          observation := projectObservation pair.type.isIdentity first model.observation } } : Value)
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

end Internal

end Complexity.Language.Syntax.Represented
