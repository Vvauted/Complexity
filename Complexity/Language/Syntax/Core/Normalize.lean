/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.LocalReturn

/-!
# Source operand normalization and binding patterns

Normalizes supported expressions left to right and prepares actual binding patterns. Public raw
preparation functions keep their names in `Complexity.Language.Syntax`; they reuse the same
internal operation checker as final lowering. No mathematical model is required here.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

partial def guardElements (condition : TSyntax `term) : MacroM (List (TSyntax `doElem)) :=
  match condition with
  | `(($inner:term)) => guardElements inner
  | `(do $body:doSeq) => pure (getDoElems body).toList
  | _ => do return [← `(doElem| return $condition)]

-- Normalize only the supported expression vocabulary. Fresh lexical names are
-- consumed by the ordinary typed translator and cannot capture user bindings.
private def normalizeBooleanBranch (stx : TSyntax `term)
    (condition yes no : NormalizedValue) : MacroM NormalizedValue := do
  let name ← freshProofName stx `boolean
  let initial ← `(doElem| let mut $name:ident : Bool := false)
  let yesBody := doSequence (yes.bindings.push (← `(doElem| $name:ident := $(yes.value))))
  let noBody := doSequence (no.bindings.push (← `(doElem| $name:ident := $(no.value))))
  let branch ← `(doElem| if $(condition.value) then $yesBody:doSeq else $noBody:doSeq)
  return ⟨condition.bindings ++ #[initial, branch], ⟨name.raw⟩, true⟩

private partial def normalizeValue (stx : TSyntax `term) (atomize : Bool)
    (expected : Option Ty := none) :
    MacroM NormalizedValue := withRef stx do
  let binary (left right : TSyntax `term)
      (rebuild : TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
      (leftType rightType : Option Ty := none) := do
    let lhs ← normalizeValue left true leftType
    let rhs ← normalizeValue right true rightType
    return (⟨lhs.bindings ++ rhs.bindings, ← rebuild lhs.value rhs.value, false⟩ : NormalizedValue)
  let unary (value : TSyntax `term)
      (rebuild : TSyntax `term → MacroM (TSyntax `term))
      (valueType : Option Ty := none) := do
    let value ← normalizeValue value true valueType
    return (⟨value.bindings, ← rebuild value.value, false⟩ : NormalizedValue)
  let normalized ← (match stx with
    | `(source_native% ($raw) ($native) ($nativeType) via ($equiv)) => do
        let raw ← normalizeValue raw false expected
        let bindings ← raw.bindings.mapM fun binding => do
          match binding with
          | `(doElem| let $name:ident $[: $type:term]? := $value:term) =>
              `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($value))
          | _ => Macro.throwErrorAt binding "a native layout expansion must contain only primitive bindings"
        return { raw with
          bindings := bindings
          value := ← `(source_native% ($(raw.value)) ($native) ($nativeType) via ($equiv))
          atomic := false }
    | `(source_native% ($raw) ($native) ($nativeType)) => do
        let raw ← normalizeValue raw false expected
        let bindings ← raw.bindings.mapM fun binding => do
          match binding with
          | `(doElem| let $name:ident $[: $type:term]? := $value:term) =>
              `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($value))
          | _ => Macro.throwErrorAt binding "a native layout expansion must contain only primitive bindings"
        return { raw with
          bindings := bindings
          value := ← `(source_native% ($(raw.value)) ($native) ($nativeType))
          atomic := false }
    | `(source_raw_value% ($raw)) => do
        let raw ← normalizeValue raw false expected
        return { raw with value := ← `(source_raw_value% ($(raw.value))), atomic := false }
    | `(($value:term : $type:term)) => do
        let value ← normalizeValue value false (some (← parseType type))
        return { value with value := ← `(($(value.value) : $type)) }
    | `(($value:term)) => normalizeValue value false expected
    | `(($left, $right)) | `(Prod.mk $left $right) =>
        let (leftType, rightType) := match expected with
          | some (.prod left right) => (some left, some right)
          | _ => (none, none)
        binary left right (fun a b => `(($a, $b))) leftType rightType
    | `(some $value) | `(Option.some $value) | `(.some $value) =>
        let valueType := match expected with
          | some (.option payload) => some payload
          | _ => none
        unary value (fun value => `(some $value)) valueType
    | `(none) | `(Option.none) | `(.none) => pure ⟨#[], stx, false⟩
    | `(Prod.fst $value) => unary value fun value => `(Prod.fst $value)
    | `(Prod.snd $value) => unary value fun value => `(Prod.snd $value)
    | `($left + $right) => binary left right fun a b => `($a + $b)
    | `($left * $right) => binary left right fun a b => `($a * $b)
    | `($left - $right) => binary left right fun a b => `($a - $b)
    | `($left / $right) => binary left right fun a b => `($a / $b)
    | `($left % $right) => binary left right fun a b => `($a % $b)
    | `($left == $right) => binary left right fun a b => `($a == $b)
    | `($left = $right) => binary left right fun a b => `($a = $b)
    | `($left < $right) => binary left right fun a b => `($a < $b)
    | `($left ≤ $right) => binary left right fun a b => `($a ≤ $b)
    | `($left <= $right) => binary left right fun a b => `($a <= $b)
    | `($left > $right) => binary left right fun a b => `($a > $b)
    | `($left ≥ $right) => binary left right fun a b => `($a ≥ $b)
    | `($left >= $right) => binary left right fun a b => `($a >= $b)
    | `(!$value) => do
        let condition ← normalizeValue value true (some .bool)
        normalizeBooleanBranch stx condition ⟨#[], ← `(false), true⟩ ⟨#[], ← `(true), true⟩
    | `($left && $right) => do
        let condition ← normalizeValue left true (some .bool)
        let yes ← normalizeValue right false (some .bool)
        normalizeBooleanBranch stx condition yes ⟨#[], ← `(false), true⟩
    | `($left || $right) => do
        let condition ← normalizeValue left true (some .bool)
        let no ← normalizeValue right false (some .bool)
        normalizeBooleanBranch stx condition ⟨#[], ← `(true), true⟩ no
    | `($left != $right) | `($left ≠ $right) => do
        normalizeValue (← `(!($left == $right))) false expected
    | _ => do
        if let some (receiver, field) := fieldAccess? stx then
          if field == `length || field == `fst || field == `snd then
            return ← unary receiver fun value => `($value.$(mkIdent field):ident)
        return ⟨#[], stx, true⟩)
  if atomize && !normalized.atomic then
    let name ← freshProofName stx `operand
    let annotation ← expected.mapM valueTypeTerm
    let binding ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value))
    return ⟨normalized.bindings.push binding, ⟨name.raw⟩, true⟩
  else
    return normalized

-- Operand bindings must enter the lexical scope before overloaded equality is
-- resolved. Boolean equality uses the existing typed branch/assignment core.
private partial def normalizeTypedValue (scope : Scope) (stx : TSyntax `term)
    (atomize : Bool) (expected : Option Ty := none) : MacroM NormalizedValue := do
  let normalized ← normalizeValue stx atomize expected
  if !normalized.bindings.isEmpty then
    return normalized
  match normalized.value with
  | `(($value:term : $type:term)) =>
      let value ← normalizeTypedValue scope value false (some (← parseType type))
      return { value with value := ← `(($(value.value) : $type)) }
  | `($left == $right) | `($left = $right) =>
      let lhs ← parseAtom scope left
      let rhs ← parseAtom scope right
      if lhs.type == .bool || rhs.type == .bool then
        expectType left lhs.type .bool
        expectType right rhs.type .bool
        let no ← normalizeValue (← `(!$right)) false (some .bool)
        normalizeBooleanBranch stx ⟨#[], left, true⟩ ⟨#[], right, true⟩ no
      else
        return normalized
  | _ => return normalized

private def normalizeCall (functions : Array Callee) (scope : Scope) (stx : TSyntax `term) :
    MacroM (Array (TSyntax `doElem) × TSyntax `term) := withRef stx do
  if let `($head:term $operands:term*) := stx then
    if head.raw.getId == `NodeRef.cons &&
        !functions.any (fun fn => fn.hasName head.raw.getId) then
      unless operands.size == 2 do
        Macro.throwErrorAt stx "node construction expects a scalar head and an optional tail"
      let value ← normalizeValue operands[0]! true
      -- Install the head's real primitive bindings before inferring its kind.
      -- The tail is normalized only afterwards, with its precise option type.
      if !value.bindings.isEmpty then
        return (value.bindings, Lean.Syntax.mkApp head #[value.value, operands[1]!])
      let valueAtom ← parseAtom scope value.value
      let kind : CellTy ← match valueAtom.type with
        | .nat => pure CellTy.nat
        | .bool => pure CellTy.bool
        | _ => Macro.throwErrorAt operands[0]! "node construction requires a Nat or Bool head"
      let tail ← normalizeValue operands[1]! true (some (.option (.node kind)))
      return (tail.bindings, Lean.Syntax.mkApp head #[value.value, tail.value])
  match stx with
  | `($head:term $operands:term*) =>
      let mut bindings := #[]
      let mut arguments := #[]
      let callee := functions.find? (fun fn => fn.hasName head.raw.getId)
      let mut head := head
      if callee.isNone then
        if let some (receiver, field) := fieldAccess? head then
          if field == `get || field == `set || field == `slice || field == `read then
            let normalized ← normalizeValue receiver true
            bindings := normalized.bindings
            head ← `($(normalized.value).$(mkIdent field):ident)
      for operand in operands, index in [:operands.size] do
        let expected := callee.bind fun fn => fn.params[index]?.map (·.type)
        let normalized ← normalizeValue operand true expected
        bindings := bindings ++ normalized.bindings
        arguments := arguments.push normalized.value
      return (bindings, Lean.Syntax.mkApp head arguments)
  | _ =>
      if let some (receiver, field) := fieldAccess? stx then
        if field == `read && !functions.any (fun fn => fn.hasName stx.raw.getId) then
          let normalized ← normalizeValue receiver true
          return (normalized.bindings,
            ← `($(normalized.value).$(mkIdent field):ident))
      return (#[], stx)

end Core

open Core

/-- A source call's checked signature before its body is prepared. The surface
name may be qualified; the source identity is the actual local or imported
entry, independently of any optional mathematical model. -/
structure RawCallHeader where
  name : TSyntax `ident
  params : Array (Name × Ty)
  result : Ty
  source : SourceFunctionInfo

/-- Actual source locals, innermost first. Mathematical contents observations
are deliberately absent from this type-and-syntax preparation interface. -/
abbrev RawScope := List (TSyntax `ident × Ty)

private def RawCallHeader.toCallee (header : RawCallHeader) : Callee := {
  name := header.name
  params := header.params.map fun (name, type) => ⟨mkIdent name, type⟩
  result := header.result
  id := mkIdent ((header.source.family ++ header.source.name).appendAfter "Id")
  observation := mkIdent header.source.action
  fold := mkIdent ((header.source.family ++ header.source.name).appendAfter "_observe") }

private def rawScope (scope : RawScope) : Scope :=
  scope.map fun (name, type) => {
    name := some name.getId, proofName := name, type, isMutable := false }

/-- Reuse the source call normalizer, preserving left-to-right operands and
temporary scopes. Install returned bindings before preparing the rewritten
call again; node construction can need more than one such step. -/
def normalizeRawCall (headers : Array RawCallHeader) (scope : RawScope)
    (call : TSyntax `term) : MacroM (Array (TSyntax `doElem) × TSyntax `term) :=
  normalizeCall (headers.map (·.toCallee)) (rawScope scope) call

/-- Infer a normalized call's actual result using the existing source operation
checker. No generated statement escapes: final lowering must still use the
combined program's relocated function IDs. -/
def inferRawBindingType (headers : Array RawCallHeader) (scope : RawScope)
    (call : TSyntax `term) : MacroM Ty := do
  return (← parseBinding (headers.map (·.toCallee)) (rawScope scope) call).1

/-- Infer an already normalized source value, for example a temporary created
when a mathematical record projection is expanded to its actual field layout.
This reuses primitive typing rather than assigning a new contents observation
to the temporary. -/
def inferRawValueType (scope : RawScope) (value : TSyntax `term)
    (expected : Option Ty := none) : MacroM Ty := do
  return (← parsePrimitive (rawScope scope) value expected).type

/-- Check a normalized standalone action using the same buffer-write and Unit
call rules as final source lowering. This does not assert successful execution
or preservation of any mathematical contents observation. -/
def checkRawAction (headers : Array RawCallHeader) (scope : RawScope)
    (call : TSyntax `term) : MacroM Unit := do
  discard <| actionCode (headers.map (·.toCallee)) (rawScope scope) call

namespace Core

def optionMatch? (element : TSyntax `doElem) :
    Option (TSyntax `term × TSyntax `term × TSyntax ``doSeq × TSyntax `term × TSyntax ``doSeq) :=
  match element with
  | `(doElem| match $value:term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq) =>
      some (value, first, firstBody, second, secondBody)
  | _ => none

def nonePattern (pattern : TSyntax `term) : Bool :=
  match pattern with
  | `(none) | `(Option.none) | `(.none) => true
  | _ => false

def somePattern? (pattern : TSyntax `term) : Option (TSyntax `term) :=
  match pattern with
  | `(some $payload) | `(Option.some $payload) | `(.some $payload) => some payload
  | _ => none

end Core

/-- Shared source binding-pattern syntax. Type annotations remain syntax so
each type preparer can check them against its actual types before projection. -/
inductive BindingPattern where
  | wildcard
  | name (value : TSyntax `ident)
  | pair (left right : BindingPattern)
  | typed (pattern : BindingPattern) (type : TSyntax `term)

private instance : Nonempty BindingPattern := ⟨.wildcard⟩

private partial def parseBindingPattern (pattern : TSyntax `term) : MacroM BindingPattern := do
  match pattern with
  | `(_) => return .wildcard
  | `(($pattern:term : $type:term)) =>
      return .typed (← parseBindingPattern pattern) type
  | `(($pattern:term)) => parseBindingPattern pattern
  | `(($left, $right)) | `(Prod.mk $left $right) =>
      return .pair (← parseBindingPattern left) (← parseBindingPattern right)
  | `($name:ident) => return .name name
  | _ => Macro.throwErrorAt pattern "expected a name, _, or a nested product pattern"

private def BindingPattern.names : BindingPattern → List Name
  | .wildcard => []
  | .name binder => [binder.getId]
  | .pair left right => left.names ++ right.names
  | .typed pattern _ => pattern.names

/-- Parse a shared binding pattern and reject repeated names. Consumers check
the retained type annotations against their own resolved parameter types. -/
def checkedBindingPattern (pattern : TSyntax `term) : MacroM BindingPattern := do
  let parsed ← parseBindingPattern pattern
  unless parsed.names.Nodup do
    Macro.throwErrorAt pattern "a source pattern cannot bind the same name twice"
  return parsed

namespace Core

-- The value supplied here has already been evaluated once. Project only used
-- fields, sharing each nested product projection; even ignored patterns are
-- checked against their actual source type.
def patternBindings (pattern : BindingPattern) (type : Ty)
    (value : TSyntax `term) : MacroM (Array (TSyntax `doElem)) := do
  match pattern with
  | .wildcard => return #[]
  | .name name =>
      return #[← `(doElem| let $name:ident : $(← valueTypeTerm type) := $value)]
  | .typed pattern expected =>
      let expected ← parseType expected
      expectType value type expected
      patternBindings pattern type value
  | .pair left right =>
      let .prod leftType rightType := type
        | Macro.throwErrorAt value "a product pattern requires a source product"
      let (bindings, base) ← if value.raw.isIdent then pure (#[], value) else do
        let name ← freshProofName value `pattern
        pure (#[← `(doElem| let $name:ident : $(← valueTypeTerm type) := $value)],
          (⟨name.raw⟩ : TSyntax `term))
      let leftBindings ← patternBindings left leftType (← `(Prod.fst $base))
      let rightBindings ← patternBindings right rightType (← `(Prod.snd $base))
      let fields := leftBindings ++ rightBindings
      return if fields.isEmpty then #[] else bindings ++ fields

def normalizeElement (functions : Array Callee) (scope : Scope) (result : Ty)
    (element : TSyntax `doElem) :
    MacroM (Array (TSyntax `doElem) × TSyntax `doElem) := withRef element do
  if let some (value, first, firstBody, second, secondBody) := optionMatch? element then
    let normalized ← normalizeTypedValue scope value true
    return (normalized.bindings, ← `(doElem| match $(normalized.value):term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq))
  match element with
  | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeTypedValue scope value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let mut $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeTypedValue scope value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| let $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $pattern:term := $value:term) =>
      let normalized ← normalizeTypedValue scope value false
      if !normalized.bindings.isEmpty then
        return (normalized.bindings,
          ← `(doElem| let $pattern:term := $(normalized.value)))
      let pattern ← checkedBindingPattern pattern
      let parsed ← parsePrimitive scope normalized.value
      let name ← freshProofName value `pattern
      let initial ← `(doElem| let $name:ident : $(← valueTypeTerm parsed.type) := $(normalized.value))
      let expanded := #[initial] ++ (← patternBindings pattern parsed.type ⟨name.raw⟩)
      return (expanded.pop, expanded.back!)
  | `(doElem| let $pattern:term ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      if !bindings.isEmpty then
        return (bindings, ← `(doElem| let $pattern:term ← $action:term))
      let pattern ← checkedBindingPattern pattern
      let (type, _, _) ← parseBinding functions scope action
      let name ← freshProofName action `pattern
      let initial ← `(doElem| let $name:ident ← $action:term)
      let expanded := #[initial] ++ (← patternBindings pattern type ⟨name.raw⟩)
      return (expanded.pop, expanded.back!)
  | `(doElem| $name:ident := $value:term) =>
      let (binding, _) ← lookupBinding scope name
      let normalized ← normalizeTypedValue scope value false (some binding.type)
      return (normalized.bindings, ← `(doElem| $name:ident := $(normalized.value)))
  | `(doElem| $name:ident ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| $name:ident ← $action:term))
  | `(doElem| return $value:term) =>
      let normalized ← normalizeTypedValue scope value false (some result)
      return (normalized.bindings, ← `(doElem| return $(normalized.value)))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let normalized ← normalizeTypedValue scope condition false
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| if $condition:term then $yes:doSeq) =>
      let normalized ← normalizeTypedValue scope condition false
      let no := doSequence #[]
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| while $_condition do $_body) => return (#[], element)
  | `(doElem| with_scratch do $_body:doSeq) => return (#[], element)
  | `(doElem| $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| $action:term))
  | _ => return (#[], element)

end Core

end Complexity.Language.Syntax
