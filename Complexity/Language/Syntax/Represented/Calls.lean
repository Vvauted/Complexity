/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Expression
import Complexity.Language.Buffer.Copy.Native
import Complexity.Language.Buffer.RepresentedCopy
import Complexity.Language.List.Fold.Native
import Complexity.Language.List.Cons.Native
import Complexity.Language.List.Uncons.Native
import Complexity.Language.List.IsEmpty.Native

/-!
# Represented calls and operation selection

Resolve local and imported calls, register concrete container operations, and
normalize raw operands. Source identities remain independent of whether a total
mathematical model is available.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def functionOperation (names : DeclarationNames) (fn : Function) : Operation := {
  family := names.sourceFamily
  sourceName := fn.name.getId
  inputs := fn.parameters.map (·.type)
  result := fn.result
  model? := fn.model?.map fun _ => {
    native := ⟨(modelName names fn.name).raw⟩
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
        native := ⟨(modelName names header.name).raw⟩
        equation := none
        relation := fieldName names.publicFamily header.name "_action_rel_native"
        refinement := fieldName names.publicFamily header.name "_refines" } }

def rawHeaders (names : DeclarationNames) : PrepareM (Array RawCallHeader) := do
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

def doTerm (elements : Array (TSyntax `doElem)) : TermElabM (TSyntax `term) := do
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

partial def canonicalCall? (imports : ImportedPrograms) (scope : List Binding)
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
def operationCall? (names : DeclarationNames) (imports : ImportedPrograms)
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

def prepareInvocation (names : DeclarationNames) (scope : List Binding)
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
def prepareRawOperands (scope : List Binding) (expression : TSyntax `term) :
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
partial def markRawElements (elements : Array (TSyntax `doElem)) :
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
/-- Extract one actual call from transparent value constructors. Branches and
callbacks are deliberately not traversed: hoisting must not execute unselected code. -/
partial def hoistValueCall? (imports : ImportedPrograms) (scope : List Binding)
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

end Internal

end Complexity.Language.Syntax.Represented
