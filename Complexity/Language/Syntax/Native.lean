/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Types
import Lean.Elab.Do
import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Typed native-structure preprocessing

The markers retain a native expression and its nominal type while exposing an
ordinary raw expression to the existing source lowering. This pass checks names
and types, and expands registered structure operations to products. Arithmetic
and boolean operators remain source syntax: their semantics and normalization
are supplied by the existing lowering, not by another evaluator here.

The supported native structures have scalar or scalar-product fields. Finite
ranges retain the existing source loop lowering; general loops, matches,
recursive calls, buffers, and unknown native callbacks are rejected.
-/

namespace Complexity.Language.Syntax

open Lean Meta Elab Term Parser.Term

/-- Raw lowering with a checked native reconstruction for the pure frontend. -/
syntax (name := sourceNativeValue) "source_native%" "(" term ")" "(" term ")"
  "(" term ")" : term
/-- Native value metadata with a checked equivalence to the exact raw layout. -/
syntax (name := sourceNativeValueEquiv) "source_native%" "(" term ")" "(" term ")"
  "(" term ")" " via " "(" term ")" : term
/-- Distinct raw and native types of a lexical binding. -/
syntax (name := sourceNativeType) "source_native_type%" "(" term ")" "(" term ")" : term
/-- A lexical binding's native type and its checked raw-layout equivalence. -/
syntax (name := sourceNativeTypeEquiv) "source_native_type%" "(" term ")" "(" term ")"
  " via " "(" term ")" : term

macro_rules
  | `(source_native% ($raw) ($_native) ($_type) via ($_equiv)) => pure raw
  | `(source_native% ($raw) ($_native) ($_type)) => pure raw
  | `(source_native_type% ($raw) ($_native) via ($_equiv)) => pure raw
  | `(source_native_type% ($raw) ($_native)) => pure raw

/-- A source parameter keeps its original name and nominal native type. -/
structure NativeParameter where
  name : TSyntax `ident
  type : PureType

/-- Native signatures used to check calls before the ordinary raw lowering. -/
structure NativeHeader where
  name : TSyntax `ident
  params : Array NativeParameter
  result : PureType
  native : TSyntax `ident

private structure NativeLocal extends NativeParameter where
  mutable : Bool := false

private structure NativeValue where
  bindings : Array (TSyntax `doElem) := #[]
  term : TSyntax `term
  type : PureType
  atomic : Bool := false

private def nativeTypeSyntax (type : PureType) : TermElabM (TSyntax `term) := do
  if type.nativeType.hasFVar || type.nativeType.hasMVar then
    throwError "native source types must be closed before generating declarations"
  withOptions (fun opts => opts.setBool `pp.fullNames true) do
    PrettyPrinter.delab type.nativeType

private partial def rawTypeSyntax : Ty → TermElabM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .prod left right => do `($(← rawTypeSyntax left) × $(← rawTypeSyntax right))
  | _ => throwError "this native frontend supports only scalars and scalar-product structures"

private def scalar (name : Name) : MetaM PureType := resolvePureType (mkConst name)

private def expect (ref : Syntax) (actual expected : PureType) : MetaM Unit := do
  unless ← actual.isDefEq expected do
    throwErrorAt ref "expected native type {expected.nativeType}, found {actual.nativeType}"

private partial def simpleType (type : Expr) : MetaM Bool := do
  for name in [``Nat, ``Bool, ``Unit] do
    if ← Meta.isDefEq type (mkConst name) then return true
  match ← whnf type with
  | .app (.app (.const ``Prod _) left) right =>
      return (← simpleType left) && (← simpleType right)
  | _ => return false

private def structureInfo? (type : PureType) : MetaM (Option StructureTypeInfo) := do
  let .const name _ ← whnf type.nativeType | return none
  return getStructureTypeInfo? (← getEnv) name

private def supported (type : PureType) : MetaM Unit := do
  if ← simpleType type.nativeType then return
  let some info ← structureInfo? type
    | throwError "unsupported native source type {type.nativeType}"
  for field in info.fields do
    unless ← simpleType field.type.nativeType do
      throwError "native source field '{field.name}' must be a scalar or scalar product"
    unless field.binderInfo == .default do
      throwError "native source constructors currently require explicit fields"

/-- Rebuild a supported native value from its exact core layout for proof-side
transport. The encoding of the generated reconstruction must be definitionally
equal to every raw input; no runtime conversion or general decoder is added. -/
def nativeReconstruction (type : PureType) : MetaM Expr := do
  if type.nativeType.hasFVar || type.nativeType.hasMVar ||
      type.encoding.hasFVar || type.encoding.hasMVar then
    throwError "native reconstruction requires a closed, fully inferred source type"
  supported type
  let rawType := mkApp (mkConst ``Value) (coreTypeExpr type.coreTy)
  let encodingType ← mkArrow type.nativeType rawType
  unless ← isDefEq (← inferType type.encoding) encodingType do
    throwError "native reconstruction has an incompatible source encoding"
  let reconstruction ← withLocalDeclD `raw rawType fun raw => do
    let value ← if ← simpleType type.nativeType then pure raw else do
      let some info ← structureInfo? type
        | throwError "native reconstruction requires a registered structure"
      let fields ← info.fields.mapM fun field => do
        let value ← tupleProjection info.fields.size field.index raw
        unless ← isDefEq (← inferType value) field.type.nativeType do
          throwError "native reconstruction has an incompatible layout for field '{field.name}'"
        return value
      mkAppM info.constructor fields
    unless ← isDefEq (← inferType value) type.nativeType do
      throwError "native reconstruction does not have the registered native type"
    unless ← isDefEq (mkApp type.encoding value) raw do
      throwError "native reconstruction does not encode back to every raw input"
    mkLambdaFVars #[raw] (← instantiateMVars value)
  let reconstruction ← instantiateMVars reconstruction
  let reconstructionType ← mkArrow rawType type.nativeType
  if reconstructionType.hasFVar || reconstructionType.hasMVar ||
      reconstruction.hasFVar || reconstruction.hasMVar then
    throwError "native reconstruction must be closed and fully inferred"
  unless ← isDefEq (← inferType reconstruction) reconstructionType do
    throwError "native reconstruction does not have its expected function type"
  return reconstruction

private def nativeEquivalenceProjection (name : Name) (input left right : Expr)
    (doc : String) : TermElabM Unit := do
  let left := left.withApp fun fn args =>
    if fn.isConstOf ``Equiv.symm then
      mkAppN fn (args.mapIdx fun index arg =>
        if index < 2 then DiscrTree.mkNoindexAnnotation arg else arg)
    else left
  let some left ← coerceToFunction? left
    | throwError "source equivalence projection '{name}' is not callable"
  -- `Value τ` and its native type can have different simplifier index keys.
  -- Ignore the type parameters of DFunLike and Equiv.symm; the particular
  -- equivalence still selects this rule, and unification checks the types.
  let left := left.withApp fun fn args =>
    mkAppN fn (args.mapIdx fun index arg =>
      if index < 3 then DiscrTree.mkNoindexAnnotation arg else arg)
  let (type, proof) ← withLocalDeclD `value input fun value => do
    let lhs := mkApp left value
    let rhs := mkApp right value
    unless ← isDefEq lhs rhs do
      throwError "source equivalence projection '{name}' does not match its checked encoding"
    return (← mkForallFVars #[value] (← mkEq lhs rhs),
      ← mkLambdaFVars #[value] (← mkEqRefl lhs))
  if let some existing := (← getEnv).find? name then
    unless existing.levelParams.isEmpty do
      throwError "existing source equivalence projection '{name}' has unexpected universe parameters"
    unless ← isDefEq existing.type type do
      throwError "existing source equivalence projection '{name}' has an incompatible type"
  else
    let shared : Array Expr := _root_.ShareCommon.shareCommon' #[type, proof]
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl {
        name := name, levelParams := [], type := shared[0]!, value := shared[1]!
      })
      enableRealizationsForConst name
    addDocStringCore name doc

/-- Reuse a checked computable equivalence to a supported native type's exact
raw layout. Scalars and scalar products use a verified `Equiv.refl`; registered
structures share one ordinary `sourceEquiv` definition with explicit inverse
proofs, rather than repeating an inline record in generated declarations. -/
def nativeEquivalence (type : PureType) : TermElabM (TSyntax `term) := do
  let reconstructionExpr ← nativeReconstruction type
  let nativeType ← nativeTypeSyntax type
  let rawTypeExpr := mkApp (mkConst ``Value) (coreTypeExpr type.coreTy)
  let expected ← mkAppM ``Equiv #[type.nativeType, rawTypeExpr]
  if ← simpleType type.nativeType then
    let identity ← mkAppM ``Equiv.refl #[type.nativeType]
    unless ← isDefEq (← inferType identity) expected do
      throwError "native identity equivalence has an incompatible raw layout"
    unless ← isDefEq (← mkAppM ``Equiv.toFun #[identity]) type.encoding do
      throwError "native identity equivalence does not preserve the registered encoding"
    return ← `(Equiv.refl $nativeType)
  let some info ← structureInfo? type
    | throwError "native equivalence requires a registered structure"
  let name := info.name ++ `sourceEquiv
  let (rawType, encoding, reconstruction, embedding) ←
    withOptions (fun opts => opts.setBool `pp.fullNames true) do
      return (← PrettyPrinter.delab rawTypeExpr, ← PrettyPrinter.delab type.encoding,
        ← PrettyPrinter.delab reconstructionExpr, ← PrettyPrinter.delab type.embedding)
  let equivalence ← `(({
    toFun := ($encoding : $nativeType → $rawType)
    invFun := ($reconstruction : $rawType → $nativeType)
    left_inv := by
      intro value
      apply (Function.Embedding.injective $embedding)
      rfl
    right_inv := by
      intro raw
      rfl
  } : $nativeType ≃ $rawType))
  let checked ← withoutErrToSorry <| elabTermAndSynthesize equivalence none
  let checked ← instantiateMVars checked
  if checked.hasFVar || checked.hasMVar || checked.hasSorry then
    throwError "native equivalence must be closed and fully checked"
  unless ← isDefEq (← inferType checked) expected do
    throwError "native equivalence does not have its expected source and raw types"
  if let some existing := (← getEnv).find? name then
    unless existing.levelParams.isEmpty do
      throwError "existing source equivalence '{name}' has unexpected universe parameters"
    unless ← isDefEq existing.type expected do
      throwError "existing source equivalence '{name}' has an incompatible type"
    unless ← isDefEq (mkConst name) checked do
      throwError "existing source equivalence '{name}' does not preserve the checked encoding and reconstruction"
  else
    let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) checked + 1)
    withOptions (Elab.async.set · false) do
      addAndCompile (.defnDecl {
        name := name, levelParams := [], type := expected, value := checked
        hints := hints, safety := .safe
      })
      enableRealizationsForConst name
    addDocStringCore name
      "Checked computable equivalence between the native structure and its exact pure source layout."
  let equivalence := Lean.mkConst name
  nativeEquivalenceProjection (info.name ++ `sourceEquiv_apply) type.nativeType
    equivalence type.encoding
    "Apply the checked native equivalence using the registered source encoding."
  nativeEquivalenceProjection (info.name ++ `sourceEquiv_symm_apply) rawTypeExpr
    (← mkAppM ``Equiv.symm #[equivalence]) reconstructionExpr
    "Reconstruct a native structure through its checked equivalence without unfolding proof fields."
  return ⟨(mkIdent name).raw⟩

private def annotation (type : PureType) : TermElabM (TSyntax `term) := do
  `(source_native_type% ($(← rawTypeSyntax type.coreTy)) ($(← nativeTypeSyntax type))
    via ($(← nativeEquivalence type)))

private def mark (raw native : TSyntax `term) (type : PureType) : TermElabM (TSyntax `term) := do
  `(source_native% ($raw) ($native) ($(← nativeTypeSyntax type))
    via ($(← nativeEquivalence type)))

private def nativeAtom (term : TSyntax `term) : TSyntax `term :=
  match term with
  | `(source_native% ($_raw) ($native) ($_type) via ($_equiv)) => native
  | `(source_native% ($_raw) ($native) ($_type)) => native
  | _ => term

private def lookup (scope : List NativeLocal) (name : TSyntax `ident) : TermElabM NativeLocal := do
  let some binding := scope.find? (fun binding => binding.name.getId == name.getId)
    | throwErrorAt name "unknown native source variable '{name.getId}'"
  return binding

private def atomize (value : NativeValue) : TermElabM NativeValue := do
  if value.atomic then return value
  let name := mkIdent (← mkFreshUserName `nativeOperand)
  let binding ← `(doElem| let $name:ident : $(← annotation value.type) := $(value.term))
  let term : TSyntax `term := ⟨name.raw⟩
  return { value with
    bindings := value.bindings.push binding
    term := ← mark term term value.type
    atomic := true }

private def fieldAccess? (term : TSyntax `term) : Option (TSyntax `term × Name) :=
  match term with
  | `($(receiver).$field:fieldIdx) =>
      match field.raw.isFieldIdx? with
      | some 1 => some (receiver, `fst)
      | some 2 => some (receiver, `snd)
      | _ => none
  | `($receiver.$field:ident) => some (receiver, field.getId)
  | `($name:ident) => match name.getId with
      | .str receiver field =>
          if receiver.isAnonymous then none
          else some (⟨(mkIdentFrom name receiver).raw⟩, Name.mkSimple field)
      | _ => none
  | _ => none

private partial def fieldsTerm : List (TSyntax `term) → TermElabM (TSyntax `term)
  | [] => `(())
  | [field] => pure field
  | field :: rest => do `(($field, $(← fieldsTerm rest)))

private def projectionTerm (count index : Nat) (receiver : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut result := receiver
  for _ in [:index] do result ← `(Prod.snd $result)
  if index + 1 < count then `(Prod.fst $result) else pure result

private partial def lowerValue (scope : List NativeLocal) (term : TSyntax `term) :
    TermElabM NativeValue := withRef term do
  let binary (left right : TSyntax `term) (input output : Name)
      (rebuild : TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
      (shortCircuit := false) : TermElabM NativeValue := do
    let lhs ← lowerValue scope left
    let rhs ← lowerValue scope right
    expect left lhs.type (← scalar input)
    expect right rhs.type (← scalar input)
    if shortCircuit && !rhs.bindings.isEmpty then
      throwErrorAt right "name compound native operands before a short-circuit boolean expression"
    return {
      bindings := lhs.bindings ++ rhs.bindings
      term := ← rebuild lhs.term rhs.term
      type := ← scalar output }
  let project (receiver : TSyntax `term) (fieldName : Name) : TermElabM NativeValue := do
    let value ← atomize (← lowerValue scope receiver)
    if let some info ← structureInfo? value.type then
      let some field := getStructureSourceField? (← getEnv) info.name fieldName
        | throwError "unknown field '{fieldName}' of native structure '{info.name}'"
      let raw ← projectionTerm info.fields.size field.index value.term
      let native := Lean.Syntax.mkCApp field.projection #[nativeAtom value.term]
      return { bindings := value.bindings, term := ← mark raw native field.type, type := field.type }
    let .app (.app (.const ``Prod _) left) right ← whnf value.type.nativeType
      | throwError "a projection requires a registered native structure or native product"
    unless fieldName == `fst || fieldName == `snd do throwError "unknown native product field"
    let raw ← if fieldName == `fst then `(Prod.fst $(value.term)) else `(Prod.snd $(value.term))
    return {
      bindings := value.bindings
      term := raw
      type := ← resolvePureType (if fieldName == `fst then left else right) }
  match term with
  | `(($value:term : $type:term)) =>
      let value ← lowerValue scope value
      expect type value.type (← elabPureType type)
      return value
  | `(($value:term)) => lowerValue scope value
  | `(true) | `(false) => return { term, type := ← scalar ``Bool, atomic := true }
  | `(()) => return { term, type := ← scalar ``Unit, atomic := true }
  | `($_:num) => return { term, type := ← scalar ``Nat, atomic := true }
  | `(($left, $right)) | `(Prod.mk $left $right) =>
      let lhs ← lowerValue scope left
      let rhs ← lowerValue scope right
      let type ← resolvePureType (← mkAppM ``Prod #[lhs.type.nativeType, rhs.type.nativeType])
      supported type
      return {
        bindings := lhs.bindings ++ rhs.bindings
        term := ← `(($(lhs.term), $(rhs.term)))
        type }
  | `(Prod.fst $value) => project value `fst
  | `(Prod.snd $value) => project value `snd
  | `($left + $right) => binary left right ``Nat ``Nat fun a b => `($a + $b)
  | `($left * $right) => binary left right ``Nat ``Nat fun a b => `($a * $b)
  | `($left - $right) => binary left right ``Nat ``Nat fun a b => `($a - $b)
  | `($left / $right) => binary left right ``Nat ``Nat fun a b => `($a / $b)
  | `($left % $right) => binary left right ``Nat ``Nat fun a b => `($a % $b)
  | `($left < $right) => binary left right ``Nat ``Bool fun a b => `($a < $b)
  | `($left ≤ $right) => binary left right ``Nat ``Bool fun a b => `($a ≤ $b)
  | `($left <= $right) => binary left right ``Nat ``Bool fun a b => `($a <= $b)
  | `($left > $right) => binary left right ``Nat ``Bool fun a b => `($a > $b)
  | `($left ≥ $right) => binary left right ``Nat ``Bool fun a b => `($a ≥ $b)
  | `($left >= $right) => binary left right ``Nat ``Bool fun a b => `($a >= $b)
  | `($left == $right) | `($left = $right) | `($left != $right) | `($left ≠ $right) =>
      let lhs ← lowerValue scope left
      let input ← if ← Meta.isDefEq lhs.type.nativeType (mkConst ``Bool) then pure ``Bool else pure ``Nat
      match term with
      | `($_ == $_) => binary left right input ``Bool fun a b => `($a == $b)
      | `($_ = $_) => binary left right input ``Bool fun a b => `($a = $b)
      | `($_ != $_) => binary left right input ``Bool fun a b => `($a != $b)
      | _ => binary left right input ``Bool fun a b => `($a ≠ $b)
  | `($left && $right) => binary left right ``Bool ``Bool (fun a b => `($a && $b)) true
  | `($left || $right) => binary left right ``Bool ``Bool (fun a b => `($a || $b)) true
  | `(!$value) =>
      let value ← lowerValue scope value
      expect term value.type (← scalar ``Bool)
      return { value with term := ← `(!$(value.term)), atomic := false }
  | _ =>
      if let `($name:ident) := term then
        if let some binding := scope.find? (fun binding => binding.name.getId == name.getId) then
          return { term := ← mark term term binding.type, type := binding.type, atomic := true }
      if let some (receiver, field) := fieldAccess? term then
        if !term.raw.isIdent || scope.any (fun binding =>
            binding.name.getId.isPrefixOf receiver.raw.getId) then
          return ← project receiver field
      let (head, arguments) := match term with
        | `($head:ident $arguments:term*) => (head, arguments)
        | `($head:ident) => (head, #[])
        | _ => (mkIdent Name.anonymous, #[])
      if head.getId.isAnonymous then throwError "unsupported native source expression"
      let name ← resolveGlobalConstNoOverload head
      if let some info := getStructureConstructorInfo? (← getEnv) name then
        supported info.type
        unless arguments.size == info.fields.size do throwError "wrong number of native constructor fields"
        let mut bindings := #[]
        let mut values := #[]
        for argument in arguments, field in info.fields do
          let value ← atomize (← lowerValue scope argument)
          expect argument value.type field.type
          bindings := bindings ++ value.bindings
          values := values.push value.term
        let native := Lean.Syntax.mkCApp info.constructor (values.map nativeAtom)
        return { bindings, term := ← mark (← fieldsTerm values.toList) native info.type, type := info.type }
      if arguments.size == 1 then
        if let some projection := (← getEnv).getProjectionFnInfo? name then
          if let some info := getStructureConstructorInfo? (← getEnv) projection.ctorName then
            let value ← lowerValue scope arguments[0]!
            expect arguments[0]! value.type info.type
            return ← project arguments[0]! name
      throwError "unknown native callback '{name}'; use a registered constructor/projection or a named source call"

private def doSequence (elements : Array (TSyntax `doElem)) : TSyntax ``doSeq :=
  ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩

private def lowerCall (callees : Array NativeHeader) (header : NativeHeader)
    (scope : List NativeLocal) (term : TSyntax `term) : TermElabM NativeValue := do
  let (name, arguments) ← match term with
    | `($name:ident $arguments:term*) => pure (name, arguments)
    | `($name:ident) => pure (name, #[])
    | _ => throwErrorAt term "expected a named source call"
  let some callee := callees.find? (fun callee => callee.name.getId == name.getId)
    | throwErrorAt name "unknown named native source call '{name.getId}'"
  if callee.name.getId == header.name.getId || callee.native.getId == header.native.getId then
    throwErrorAt name "recursive native structure calls are not supported in this frontend"
  unless arguments.size == callee.params.size do throwErrorAt term "wrong number of native call arguments"
  let mut bindings := #[]
  let mut values := #[]
  for argument in arguments, parameter in callee.params do
    let value ← atomize (← lowerValue scope argument)
    expect argument value.type parameter.type
    bindings := bindings ++ value.bindings
    values := values.push value.term
  return { bindings, term := Lean.Syntax.mkApp ⟨name.raw⟩ values, type := callee.result }

private partial def lowerSequence (callees : Array NativeHeader) (header : NativeHeader)
    (scope : List NativeLocal) (elements : List (TSyntax `doElem)) :
    TermElabM (Array (TSyntax `doElem)) := do
  match elements with
  | [] => return #[]
  | element :: rest => withRef element do
      let bind (name : TSyntax `ident) (ann : Option (TSyntax `term)) (term : TSyntax `term)
          (mutable call : Bool) := do
        let value ← if call then lowerCall callees header scope term else lowerValue scope term
        if let some ann := ann then expect ann value.type (← elabPureType ann)
        let type ← annotation value.type
        let binding ← if call then
            if mutable then `(doElem| let mut $name:ident : $type ← $(value.term):term)
            else `(doElem| let $name:ident : $type ← $(value.term):term)
          else if mutable then `(doElem| let mut $name:ident : $type := $(value.term))
            else `(doElem| let $name:ident : $type := $(value.term))
        let entry : NativeLocal := { name, type := value.type, mutable }
        return value.bindings ++ #[binding] ++ (← lowerSequence callees header (entry :: scope) rest)
      let branch (condition : TSyntax `term) (yes no : TSyntax ``doSeq) := do
        let condition ← lowerValue scope condition
        expect element condition.type (← scalar ``Bool)
        let yes := doSequence (← lowerSequence callees header scope (getDoElems yes).toList)
        let no := doSequence (← lowerSequence callees header scope (getDoElems no).toList)
        let branch ← `(doElem| if $(condition.term) then $yes:doSeq else $no:doSeq)
        return condition.bindings ++ #[branch] ++ (← lowerSequence callees header scope rest)
      match element with
      | `(doElem| let mut $name:ident $[: $ann:term]? := $value:term) => bind name ann value true false
      | `(doElem| let $name:ident $[: $ann:term]? := $value:term) => bind name ann value false false
      | `(doElem| let mut $name:ident $[: $ann:term]? ← $value:term) => bind name ann value true true
      | `(doElem| let $name:ident $[: $ann:term]? ← $value:term) => bind name ann value false true
      | `(doElem| $name:ident := $value:term) =>
          let binding ← lookup scope name
          unless binding.mutable do throwErrorAt name "assignment requires a mutable native binding"
          let value ← lowerValue scope value
          expect element value.type binding.type
          return value.bindings ++ #[← `(doElem| $name:ident := $(value.term))] ++
            (← lowerSequence callees header scope rest)
      | `(doElem| return $value:term) =>
          let value ← lowerValue scope value
          expect element value.type header.result
          return value.bindings ++ #[← `(doElem| return $(value.term))] ++
            (← lowerSequence callees header scope rest)
      | `(doElem| return) =>
          expect element (← scalar ``Unit) header.result
          return #[← `(doElem| return ())] ++ (← lowerSequence callees header scope rest)
      | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) => branch condition yes no
      | `(doElem| if $condition:term then $yes:doSeq) => branch condition yes (doSequence #[])
      | `(doElem| for $pattern:term in $collection:term do $body:doSeq) =>
          let `($name:ident) := pattern
            | throwErrorAt pattern "a native source range requires an identifier as its loop variable"
          let nat ← scalar ``Nat
          let range (start stop stride : TSyntax `term)
              (rebuild : TSyntax `term → TSyntax `term → TSyntax `term →
                TermElabM (TSyntax `term)) := do
            let startValue ← lowerValue scope start
            expect start startValue.type nat
            let stopValue ← lowerValue scope stop
            expect stop stopValue.type nat
            let strideValue ← lowerValue scope stride
            expect stride strideValue.type nat
            return (startValue.bindings ++ stopValue.bindings ++ strideValue.bindings,
              ← rebuild startValue.term stopValue.term strideValue.term)
          let (bindings, collection) ← match collection with
            | `([ : $stop]) =>
                range (← `(0)) stop (← `(1)) (fun _ stop _ => `([ : $stop]))
            | `([ $start : $stop ]) =>
                range start stop (← `(1)) (fun start stop _ => `([ $start : $stop ]))
            | `([ : $stop : $stride ]) =>
                range (← `(0)) stop stride (fun _ stop stride => `([ : $stop : $stride ]))
            | `([ $start : $stop : $stride ]) =>
                range start stop stride (fun start stop stride => `([ $start : $stop : $stride ]))
            | _ => throwErrorAt collection "native source iteration requires a finite Nat range"
          let entry : NativeLocal := { name, type := nat }
          let body := doSequence (← lowerSequence callees header (entry :: scope)
            (getDoElems body).toList)
          let loop ← `(doElem| for $name:ident in $collection:term do $body:doSeq)
          return bindings ++ #[loop] ++ (← lowerSequence callees header scope rest)
      | _ => throwError "unsupported native source statement; general loops, match, and callbacks are not supported"

/-- Type-check and preprocess one nonrecursive native-structure source body.
All emitted bindings retain their raw and native types for the existing lowering. -/
def lowerNativeBody (callees : Array NativeHeader) (header : NativeHeader)
    (body : TSyntax `term) : TermElabM (TSyntax `term) := do
  supported header.result
  let mut scope := []
  for parameter in header.params do
    supported parameter.type
    if scope.any (fun binding : NativeLocal => binding.name.getId == parameter.name.getId) then
      throwErrorAt parameter.name "duplicate native source parameter"
    scope := { name := parameter.name, type := parameter.type } :: scope
  let `(do $sequence:doSeq) := body | throwErrorAt body "a native source body must be a do block"
  let sequence := doSequence (← lowerSequence callees header scope (getDoElems sequence).toList)
  `(do $sequence:doSeq)

end Complexity.Language.Syntax
