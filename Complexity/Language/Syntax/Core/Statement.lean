/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Normalize

/-!
# Source statement and block lowering

Lowers structured source blocks, lexical bindings, calls, branches, ranges and scratch scopes to
the typed statement language. It also records the actual block sites used by later proof emission;
no second control-flow lowering is used for those observations.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

private partial def rangeReceiverName? (value : TSyntax `term) : Option (TSyntax `ident) :=
  match value with
  | `(($inner:term)) => rangeReceiverName? inner
  | `($name:ident) => some name
  | _ => none

private partial def stableRangeBound (scope : Scope) (value : TSyntax `term)
    (allowLength : Bool := true) : MacroM Bool := do
  match value with
  | `(source_native% ($raw) ($_native) ($_type) via ($_equiv)) =>
      stableRangeBound scope raw allowLength
  | `(source_native% ($raw) ($_native) ($_type)) =>
      stableRangeBound scope raw allowLength
  | `(($value:term)) => stableRangeBound scope value allowLength
  | `($_:num) => return true
  | _ =>
      if let some (receiver, field) := fieldAccess? value then
        if allowLength && field == `length then
          if let some name := rangeReceiverName? receiver then
            let (binding, _) ← lookupBinding scope name
            return !binding.isMutable && match binding.type with
              | .buffer _ => true
              | _ => false
        return false
      if let `($name:ident) := value then
        let (binding, _) ← lookupBinding scope name
        return !binding.isMutable && binding.type == .nat
      return false

private def statementCode (family : TSyntax `ident) (functions : Array Callee)
    (owner : TSyntax `ident)
    (recurse : Scope → Ty → List (TSyntax `doElem) → Nat → Option LocalReturnTarget →
      MacroM LoweredBlock)
    (scope : Scope) (result : Ty) (element : TSyntax `doElem) (nextIndex : Nat)
    (localReturn : Option LocalReturnTarget) :
    MacroM LoweredBlock := withRef element do
  if let `(doElem| source_local_return% ($pending:ident) do $body:doSeq) := element then
    let target ← localReturnTarget scope pending
    let scope := scope.map fun binding =>
      if binding.proofName.getId == target.pending then
        { binding with privatePending := true }
      else binding
    return ← recurse scope result (getDoElems body).toList nextIndex (some target)
  if let `(doElem| source_range_site% $tag:ident ($pattern:term, $collection:term) do $body:doSeq) := element then
    let source ← `(doElem| for $pattern:term in $collection:term do $body:doSeq)
    let lowered ← recurse scope result [source] nextIndex localReturn
    -- Ordinary for lowering appends its own loop after its nested sites.
    -- Reuse that returned site, without predicting its generated name/index.
    let some site := lowered.sites.back?
      | Macro.throwErrorAt tag "the tagged range did not emit its source loop"
    return { lowered with
      sites := lowered.sites.pop.push { site with rangeRequest := some {
        tag := tag.getId, entryScope := scope, proofBody := lowered.proofBody } } }
  if let `(doElem| source_while_site% $tag:ident ($condition:term) do $body:doSeq) := element then
    let source ← `(doElem| while $condition:term do $body:doSeq)
    let lowered ← recurse scope result [source] nextIndex localReturn
    -- Ordinary while lowering appends its own loop after its nested sites.
    -- The marker selects that same loop and leaves its term and order intact.
    let some site := lowered.sites.back?
      | Macro.throwErrorAt tag "the tagged while did not emit its source loop"
    return { lowered with
      sites := lowered.sites.pop.push { site with whileRequest := some tag.getId } }
  if let some (value, first, firstBody, second, secondBody) := optionMatch? element then
    let (noneBody, payload, someBody) ←
      if nonePattern first then
        match somePattern? second with
        | some payload => pure (firstBody, payload, secondBody)
        | none => Macro.throwErrorAt second "expected a 'some pattern' option branch"
      else if nonePattern second then
        match somePattern? first with
        | some payload => pure (secondBody, payload, firstBody)
        | none => Macro.throwErrorAt first "expected a 'some pattern' option branch"
      else Macro.throwErrorAt element "an option match needs exactly none and some branches"
    let option ← parseAtom scope value
    let .option payloadType := option.type
      | Macro.throwErrorAt value "source matching currently supports Option values"
    let pattern ← checkedBindingPattern payload
    let payloadName ← freshProofName payload `payload
    let (sourceName, bindings) ← match pattern with
      | .name name => pure (name.getId, #[])
      | _ => do
          pure (payloadName.getId, ← patternBindings pattern payloadType ⟨payloadName.raw⟩)
    let noneCode ← recurse scope result (getDoElems noneBody).toList nextIndex localReturn
    let someCode ← recurse (⟨some sourceName, payloadName, payloadType, false, none, false⟩ :: scope)
      result (bindings.toList ++ (getDoElems someBody).toList) (nextIndex + noneCode.sites.size) localReturn
    let normal ← `(doElem| pure ())
    let noneBody := noneCode.proofSequence normal
    let someBody := someCode.proofSequence normal
    let branch ← `(doElem| match $(option.value):term with
      | none => $noneBody:doSeq
      | some $payloadName:ident => $someBody:doSeq)
    return ⟨← `(Complexity.Language.Stmt.matchOption $(option.term)
        $(noneCode.term) $(someCode.term)),
      #[branch], noneCode.fallsThrough || someCode.fallsThrough, noneCode.sites ++ someCode.sites⟩
  match element with
  | `(doElem| $name:ident := $value:term) => assignCode scope name value
  | `(doElem| $name:ident ← $action:term) => assignBindingCode functions scope name action
  | `(doElem| return $value:term) =>
      match localReturn with
      | some target => localReturnCode scope target value
      | none => returnCode scope result value
  | `(doElem| return) =>
      match localReturn with
      | some target => localReturnCode scope target (← `(()))
      | none => returnCode scope result (← `(()))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let parsed ← parsePrimitive scope condition
      expectType condition parsed.type .bool
      let saved ← freshProofName condition `condition
      let inner := if parsed.atom.isSome then scope
        else ⟨none, saved, Ty.bool, false, none, false⟩ :: scope
      let yesCode ← recurse inner result (getDoElems yes).toList nextIndex localReturn
      let noCode ← recurse inner result (getDoElems no).toList (nextIndex + yesCode.sites.size) localReturn
      let term ← match parsed.atom with
        | some atom =>
            `(Complexity.Language.Stmt.ite $atom $(yesCode.term) $(noCode.term))
        | none =>
            `(Complexity.Language.Stmt.letPrim $(parsed.term)
              (Complexity.Language.Stmt.ite
                (Complexity.Language.Atom.var Complexity.Language.Var.here)
                $(yesCode.term) $(noCode.term)))
      let normal ← `(doElem| pure ())
      let yesBody := yesCode.proofSequence normal
      let noBody := noCode.proofSequence normal
      let conditionValue ← if parsed.atom.isSome then pure parsed.value else `($saved:ident)
      let branch ← `(doElem| if $conditionValue then $yesBody:doSeq else $noBody:doSeq)
      let proofBody ← if parsed.atom.isSome then pure #[branch] else do
        let capture ← `(doElem| let $saved:ident : Bool := $(parsed.value))
        pure #[capture, branch]
      return ⟨term, proofBody, yesCode.fallsThrough || noCode.fallsThrough,
        yesCode.sites ++ noCode.sites⟩
  | `(doElem| while $condition do $body) =>
      let name := generatedName family owner s!"_loop{nextIndex}"
      let guardCode ← recurse scope .bool (← guardElements condition) (nextIndex + 1) none
      let bodyCode ← recurse scope result (getDoElems body).toList
        (nextIndex + 1 + guardCode.sites.size) localReturn
      let site : BlockSite := {
        name, scope, result, guard := some (← localGuard scope localReturn guardCode.term), body := bodyCode.term,
        finiteRange := none, localReturn }
      let code := loopMember site "Code"
      return ⟨⟨code.raw⟩, ← loopProofBody site, true,
        guardCode.sites ++ bodyCode.sites |>.push site⟩
  | `(doElem| source_range% ($cursor:ident, $stop:term, $stride:term) do $body:doSeq) =>
      let name := generatedName family owner s!"_loop{nextIndex}"
      let condition ← `($cursor:ident < $stop)
      let guardCode ← recurse scope .bool (← guardElements condition) (nextIndex + 1) none
      let bodyCode ← recurse scope result (getDoElems body).toList
        (nextIndex + 1 + guardCode.sites.size) localReturn
      let (cursorBinding, _) ← lookupBinding scope cursor
      let stopValue ← parsePrimitive scope stop (some .nat)
      let strideValue ← parsePrimitive scope stride (some .nat)
      let metadata : FiniteRange :=
        ⟨cursorBinding.proofName, stopValue.value, strideValue.value,
          bodyCode.proofBody, bodyCode.fallsThrough, localReturn.isSome⟩
      let site : BlockSite := {
        name, scope, result, guard := some (← localGuard scope localReturn guardCode.term), body := bodyCode.term,
        finiteRange := some metadata, localReturn }
      let code := loopMember site "Code"
      let positive ← freshProofName element `positiveStep
      let checked ← `(doElem| have $positive:ident : 0 < $(strideValue.value) := by
        simp (config := { zetaDelta := true, failIfUnchanged := false }) only
          [Nat.add_eq] <;> omega)
      return ⟨⟨code.raw⟩, #[checked] ++ (← loopProofBody site), true,
        guardCode.sites ++ bodyCode.sites |>.push site⟩
  | `(doElem| for $pattern:term in $collection:term do $body:doSeq) =>
      let isRange := match collection with
        | `([ : $_stop]) | `([ $_start : $_stop ]) |
          `([ : $_stop : $_stride ]) | `([ $_start : $_stop : $_stride ]) => true
        | _ => false
      let cursorName := if isRange then match pattern with
          | `($name:ident) => name.getId.eraseMacroScopes
          | _ => `index
        else `index
      let cursor ← freshProofName element cursorName
      let limit ← freshProofName element `stop
      let stepName ← freshProofName element `step
      let rangeInitial (start stop stride : TSyntax `term) := do
        let cursorBinding ← `(doElem| let mut $cursor:ident : Nat := $start)
        let (initial, stop) ← if ← stableRangeBound scope stop then
            pure (#[cursorBinding], stop)
          else
            pure (#[cursorBinding, ← `(doElem| let $limit:ident : Nat := $stop)],
              (⟨limit.raw⟩ : TSyntax `term))
        if ← stableRangeBound scope stride false then
          pure (initial, stop, stride)
        else
          pure (initial.push (← `(doElem| let $stepName:ident : Nat := $stride)), stop,
            (⟨stepName.raw⟩ : TSyntax `term))
      let (initial, stop, stride, elementBinding) ← match collection with
        | `([ : $stop]) => do
            let (initial, stop, stride) ← rangeInitial (← `(0)) stop (← `(1))
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ $start : $stop ]) => do
            let (initial, stop, stride) ← rangeInitial start stop (← `(1))
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ : $stop : $stride ]) => do
            let (initial, stop, stride) ← rangeInitial (← `(0)) stop stride
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ $start : $stop : $stride ]) => do
            let (initial, stop, stride) ← rangeInitial start stop stride
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | _ => do
            let buffer ← freshProofName collection `buffer
            pure (#[← `(doElem| let $buffer:ident := $collection),
              ← `(doElem| let $limit:ident : Nat := ($buffer:ident).length),
              ← `(doElem| let mut $cursor:ident : Nat := 0)],
              (⟨limit.raw⟩ : TSyntax `term), ← `(1),
              ← `(doElem| let $pattern:term ← ($buffer:ident).get $cursor:ident))
      let advance ← `(doElem| $cursor:ident := $cursor:ident + $stride)
      let iteration := doSequence (#[elementBinding] ++ getDoElems body ++ #[advance])
      let loop ← `(doElem| source_range% ($cursor:ident, $stop, $stride) do $iteration:doSeq)
      recurse scope result (initial.toList ++ [loop]) nextIndex localReturn
  | `(doElem| with_scratch do $body:doSeq) =>
      let name := generatedName family owner s!"_scope{nextIndex}"
      match localReturn with
      | none =>
          let bodyCode ← recurse scope result (getDoElems body).toList (nextIndex + 1) none
          let site : BlockSite := {
            name, scope, result, guard := none, body := bodyCode.term, finiteRange := none }
          let code := loopMember site "Code"
          -- The observation exposes Control rather than a syntactically terminal
          -- return. Retain its normal continuation just as for a named loop.
          return ⟨⟨code.raw⟩, ← loopProofBody site, true,
            bodyCode.sites.push site⟩
      | some parent =>
          -- This slot belongs to the parent lexical scope, but lies outside
          -- this scratch body. A failing cleanup cannot commit an escaping root.
          let pendingName ← freshProofName element `scratchPending
          let pending : Binding :=
            ⟨some pendingName.getId, pendingName, .option parent.type, true, none, true⟩
          let inner := pending :: scope
          let target : LocalReturnTarget := ⟨parent.type, pendingName.getId⟩
          let bodyCode ← recurse inner result (getDoElems body).toList (nextIndex + 1) (some target)
          let site : BlockSite := {
            name, scope := inner, result, guard := none, body := bodyCode.term,
            finiteRange := none, localReturn := some target }
          let code := loopMember site "Code"
          let commit ← commitLocalReturnCode inner parent pending
          let pendingType ← valueTypeTerm (.option parent.type)
          let term ← `(Complexity.Language.Stmt.letPrim
            (Complexity.Language.Prim.none $(← typeTerm parent.type))
            (Complexity.Language.Stmt.seq $code:ident $(commit.term)))
          let declarations := #[
            ← `(doElem| let mut $pendingName:ident : $pendingType := none)]
          return ⟨term, declarations ++ (← loopProofBody site) ++ commit.proofBody,
            true, bodyCode.sites.push site⟩
  | `(doElem| $action:term) => actionCode functions scope action
  | _ =>
      Macro.throwErrorAt element
        "unsupported source statement; use let, let mut, assignment, a named call, buffer access or allocation, node read or construction, with_scratch, if/then/else, Option match, while, bounded for, or return"

private partial def blockCode (family : TSyntax `ident) (functions : Array Callee)
    (owner : TSyntax `ident) (scope : Scope) (result : Ty)
    (elements : List (TSyntax `doElem)) (nextIndex : Nat)
    (localReturn : Option LocalReturnTarget := none) : MacroM LoweredBlock := do
  match elements with
  | [] => return ⟨← `(Complexity.Language.Stmt.skip), #[], true, #[]⟩
  | element :: rest => withRef element do
      let returnType := localReturn.map (·.type) |>.getD result
      let (bindings, element) ← normalizeElement functions scope returnType element
      if !bindings.isEmpty then
        return ← blockCode family functions owner scope result
          (bindings.toList ++ element :: rest) nextIndex localReturn
      match element with
      | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value (← annotation.mapM parseType)
          checkAnnotation annotation parsed.type
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType parsed.type annotation (some parsed.value)
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, true, bindingNativeCoordinate type, false⟩ :: scope)
            result rest nextIndex localReturn
          let binding ← `(doElem| let mut $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value (← annotation.mapM parseType)
          checkAnnotation annotation parsed.type
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType parsed.type annotation (some parsed.value)
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, false, bindingNativeCoordinate type, false⟩ :: scope)
            result rest nextIndex localReturn
          let binding ← `(doElem| let $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType bindingType annotation
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, true, bindingNativeCoordinate type, false⟩ :: scope)
            result rest nextIndex localReturn
          let binding ← `(doElem| let mut $proofName:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType bindingType annotation
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, false, bindingNativeCoordinate type, false⟩ :: scope)
            result rest nextIndex localReturn
          let binding ← `(doElem| let $proofName:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | _ =>
          let statement ← statementCode family functions owner
            (fun scope result elements nextIndex target =>
              blockCode family functions owner scope result elements nextIndex target)
            scope result element nextIndex localReturn
          if rest.isEmpty then
            return statement
          else
            let continuation ← blockCode family functions owner scope result rest
              (nextIndex + statement.sites.size) localReturn
            let continuation ← match localReturn with
              | some target => resumeLocalCode scope target continuation
              | none => pure continuation
            return ⟨← `(Complexity.Language.Stmt.seq $(statement.term) $(continuation.term)),
              if statement.fallsThrough then statement.proofBody ++ continuation.proofBody
                else statement.proofBody,
              statement.fallsThrough && continuation.fallsThrough,
              statement.sites ++ continuation.sites⟩

def functionCode (family : TSyntax `ident) (functions : Array Callee)
    (fn : Function) : MacroM LoweredBlock := do
  match fn.body with
  | `(do $body:doSeq) =>
      let scope : Scope := fn.params.toList.zipIdx.map fun (param, index) =>
        ⟨some param.name.getId, param.name, param.type, false,
          fn.nativeView.map (fun view => ⟨view.parameterTypes[index]!, view.parameterEquivs[index]!⟩), false⟩
      let result ← blockCode family functions fn.name scope fn.result (getDoElems body).toList 1
      return { result with sites := result.sites.map fun site =>
        { site with nativeResult := fn.nativeView.map fun view => ⟨view.resultType, view.resultEquiv⟩ } }
  | _ => Macro.throwErrorAt fn.body "source function bodies must be supported 'do' blocks"

end Core

end Complexity.Language.Syntax
