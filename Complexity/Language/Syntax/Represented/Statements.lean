/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Control

/-!
# Represented source statement preparation

The recursive statement pass prepares one actual source block together with
optional mathematical observations. Calls, finite ranges, while loops, branches
and scratch scopes retain their shared Core lowering and actual control flow.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

/-- A direct value choice keeps its local-return boundary inside each arm.
The selector is outside that boundary, as in the original source lowering. -/
private def closeValueChoice (slot : JoinSlot) (elements : Array (TSyntax `doElem)) :
    TermElabM (Array (TSyntax `doElem)) := do
  let [element] := elements.toList
    | throwError "a prepared value choice must retain its branch structure"
  match element with
  | `(doElem| if $test:term then $yes:doSeq else $no:doSeq) =>
      let yes ← slot.branch (getDoElems yes)
      let no ← slot.branch (getDoElems no)
      return #[← `(doElem| if $test:term then $yes:doSeq else $no:doSeq)]
  | `(doElem| match $value:term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq) =>
      let firstBody ← slot.branch (getDoElems firstBody)
      let secondBody ← slot.branch (getDoElems secondBody)
      return #[← `(doElem| match $value:term with
        | $first:term => $firstBody:doSeq
        | $second:term => $secondBody:doSeq)]
  | _ => throwError "a prepared value choice must retain its branch structure"

private def completionRangeModel (captured : Array Binding)
    (stateSyntax returnedType bodyNative : TSyntax `term)
    (initialModel startModel stopModel strideModel : ValueModel) :
    TermElabM (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) := do
  let mutableType ← stateType (captured.filter (·.mutable)).toList
  let mutableName := mkIdent (← mkFreshUserName `mutableState)
  let stepIndex := mkIdent (← mkFreshUserName `index)
  let nextState := mkIdent (← mkFreshUserName `nextState)
  let packedMutable ← packMutableState captured initialModel.native ⟨mutableName.raw⟩
  let embedding ← `(fun ($mutableName:ident : $mutableType) => $packedMutable)
  let nextMutable ← mutableState captured ⟨nextState.raw⟩
  let mutableStep ← `(fun ($stepIndex:ident : Nat) ($mutableName:ident : $mutableType) =>
    Prod.map (id : Option $returnedType → Option $returnedType)
      (fun ($nextState:ident : $stateSyntax) => $nextMutable)
      ($bodyNative $stepIndex:ident $packedMutable))
  let initialMutable ← mutableState captured initialModel.native
  let nativeRange ← `(({
    start := $(startModel.native), stop := $(stopModel.native)
    step := $(strideModel.native), step_pos := by
      simp (config := { zetaDelta := true, failIfUnchanged := false }) only [Nat.add_eq] <;>
        omega } : Std.Legacy.Range))
  let nativeResult ← `(let outcome := Id.run (forIn (m := Id) $nativeRange
      ((none, $initialMutable) : Option $returnedType × $mutableType)
      (fun index running =>
        let iteration : Option $returnedType × $mutableType := $mutableStep index running.2
        Option.elim iteration.1
          (pure (ForInStep.yield (none, iteration.2)))
          (fun returned => pure (ForInStep.done (some returned, iteration.2)))))
    (outcome.1, $embedding outcome.2))
  return (nativeResult, embedding, mutableStep, initialMutable)

partial def sequence (names : DeclarationNames)
    (imports : ImportedPrograms) (resultType : NativeType)
    (scope : List Binding) (elements : List (TSyntax `doElem))
    (bindingKind : BindingKind := .immutable) (allowFallthrough : Bool := false)
    (localReturn : Bool := false) (completion : Option CompletionContext := none)
    (returnState : Option CompletionContext := none) :
    PrepareM PreparedBlock := do
  let modelResultType := returnState.map (fun context =>
    NativeType.prod resultType context.stateType) |>.getD resultType
  let completedValue (scope : List Binding) (result : Value) :=
    match returnState with
    | none => pure (some result)
    | some context => context.returnedValue? scope result
  let completedBlock (scope : List Binding) (result : Value) : TermElabM PreparedBlock := do
    let returned ← completedValue scope result
    let native ← returned.bind (·.model?) |>.mapM fun model => do
      pure #[← `(doElem| return $(model.native))]
    return {
      raw := #[], native? := native, calls? := some #[]
      returned? := returned, normalScope? := none }
  let bindingMutable := match bindingKind with | .immutable => false | _ => true
  let bindingSlot (name : TSyntax `ident) : PrepareM Name := do
    match bindingKind with
    | .assignment =>
        let slot := (← lookup scope name).slot
        modify fun state => { state with assignedSlots := state.assignedSlots.push slot }
        return slot
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
    let continued ← sequence names imports resultType
      (binding :: scope) rest .immutable allowFallthrough localReturn completion returnState
    return { continued with
      raw := #[raw] ++ continued.raw
      native? := (fun native rest => #[native] ++ rest) <$> native <*> continued.native?
      calls? := (· ++ ·) <$> calls <*> continued.calls?
      completion? := CompletionSummary.prepend? (Array.singleton <$> native) calls
        continued.completion? }
  let continueChoice (raw : TSyntax `doElem) (yes no : PreparedBlock)
      (available : Bool)
      (choose : Bool → TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
      (trace : Array Trace → Array Trace → Value → Value → Binding → Trace)
      (branchCompletion : Option CompletionContext)
      (assigned : Array Name)
      (rest : List (TSyntax `doElem)) : PrepareM PreparedBlock := do
    let mixedNormal (block : PreparedBlock) :=
      block.normalScope?.isSome && !(block.native?.isSome && block.calls?.isSome)
    if mixedNormal yes || mixedNormal no then
      let joined ← match branchCompletion with
        | none => pure none
        | some context =>
            completionChoice available context yes.completion? no.completion? choose trace
      if let some summary := joined then
        let some context := branchCompletion
          | throwError "a completion summary must retain its lexical coordinates"
        let (snapshot, after, nativePrefix) ← CompletionSummary.openView context scope assigned summary
        let pending ← value [snapshot] (← `($(snapshot.name):ident.1))
        let payloadName := mkIdent (← mkFreshUserName `completedValue)
        let payload ← parameterBinding payloadName resultType
        let payload := { payload with model? := payload.model?.map fun model =>
          { model with rawModel := ⟨payload.rawName.raw⟩ } }
        let payloadValue ← value [payload] ⟨payloadName.raw⟩ (some resultType)
        let payloadType ← termOfExpr resultType.nativeType
        let choosePending (mathematical : Bool) (absent present : TSyntax `term) := do
          let pending ← pending.requireModel
          let discriminant := if mathematical then pending.model else pending.native
          let selected ← `(Option.elim $discriminant $absent
            (fun ($payloadName:ident : $payloadType) => $present))
          if mathematical then shareCompletionModel summary selected else pure selected
        -- A nested mixed arm contributes its current state, not a fictitious
        -- normal trace. The common suffix is prepared once and only the empty
        -- completion branch consumes its calls.
        let continued ← sequence names imports resultType after rest
          .immutable allowFallthrough localReturn completion returnState
        let returnedBlock ← completedBlock after payloadValue
        let choice ← if continued.normalScope?.isNone then
            choiceModel true modelResultType continued returnedBlock choosePending
              (Trace.optionMatch pending payload)
          else pure none
        let native ← choice.mapM fun choice => do
          return nativePrefix ++ #[← `(doElem| return $(choice.native))]
        let returned := choice.map fun choice => ({
          type := modelResultType, raw := ⟨choice.result.rawName.raw⟩
          model? := choice.result.model?.map fun model => {
            toBindingModel := model, native := choice.native } } : Value)
        let completionSummary ← match completion with
          | none => pure none
          | some target => do
              let completed ← target.capture after (some payloadValue)
              let selected ← completionChoice true target continued.completion? completed
                choosePending (Trace.optionMatch pending payload)
              pure (CompletionSummary.prepend? (some nativePrefix) (some summary.calls) selected)
        return {
          raw := #[raw] ++ continued.raw, native? := native
          calls? := choice.map fun choice => summary.calls ++ #[choice.trace]
          returned? := returned, normalScope? := continued.normalScope?
          completion? := completionSummary }
    -- Simple choices keep their existing mathematical shape. Their local
    -- completion snapshots are projected to the caller's lexical coordinates.
    let project (block : PreparedBlock) : TermElabM PreparedBlock := do
      let summary ← match branchCompletion, completion with
        | some source, some target => CompletionSummary.project? source target scope block.completion?
        | _, _ => pure none
      return { block with completion? := summary }
    let yes ← project yes
    let no ← project no
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
      let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn completion returnState
      return { continued with
        raw := #[raw] ++ continued.raw
        native? := (fun _ native => nativePrefix ++ native) <$> choice <*> continued.native?
        calls? := (· ++ ·) <$> calls <*> continued.calls?
        completion? := CompletionSummary.prepend? ((fun _ => nativePrefix) <$> choice)
          calls continued.completion? }
    if yes.normalScope?.isNone && no.normalScope?.isNone then
      -- Unreachable source statements still belong to the typed source body,
      -- but do not contribute to its mathematical result or recursive calls.
      let recursive := (← get).currentRecursive
      let continued ← sequence names imports resultType scope rest .immutable true localReturn completion returnState
      modify fun state => { state with currentRecursive := recursive }
      let choice ← choiceModel available modelResultType yes no choose trace
      let completionSummary ← match completion with
        | none => pure none
        | some context =>
            completionChoice available context yes.completion? no.completion? choose trace
      let native ← choice.mapM fun choice => do
        return #[← `(doElem| return $(choice.native))]
      let returned := choice.map fun choice => ({
        type := modelResultType, raw := ⟨choice.result.rawName.raw⟩
        model? := choice.result.model?.map fun model => {
          toBindingModel := model, native := choice.native } } : Value)
      return (⟨#[raw] ++ continued.raw, native,
        choice.map (fun choice => #[choice.trace]), returned, none, completionSummary⟩ : PreparedBlock)
    -- Only the normally continuing arm reaches the enclosing continuation.
    -- Prepare that suffix once in its actual outgoing lexical scope; branch
    -- locals are closed while assignments keep their original slot identity.
    let yesContinues := yes.normalScope?.isSome
    let normal := if yesContinues then yes else no
    let some normalScope := normal.normalScope?
      | throwError "a mixed source choice must have a normally continuing arm"
    let after := closeScope scope normalScope
    let after := if available && normal.native?.isSome && normal.calls?.isSome then after
      else invalidateObservations after true
    let continued ← sequence names imports resultType after rest
      .immutable allowFallthrough localReturn completion returnState
    let completionSummary ← match completion with
      | none => pure none
      | some context =>
          let normalSummary := CompletionSummary.prepend? normal.native? normal.calls?
            continued.completion?
          completionChoice available context
            (if yesContinues then normalSummary else yes.completion?)
            (if yesContinues then no.completion? else normalSummary) choose trace
    if continued.normalScope?.isNone then
      -- This is proof-side continuation distribution, not another source
      -- branch or execution. Both arms now return the same result type.
      let completed := { continued with
        native? := (· ++ ·) <$> normal.native? <*> continued.native?
        calls? := (· ++ ·) <$> normal.calls? <*> continued.calls? }
      let choice ← choiceModel available modelResultType
        (if yesContinues then completed else yes)
        (if yesContinues then no else completed) choose trace
      let native ← choice.mapM fun choice => do
        return #[← `(doElem| return $(choice.native))]
      let returned := choice.map fun choice => ({
        type := modelResultType, raw := ⟨choice.result.rawName.raw⟩
        model? := choice.result.model?.map fun model => {
          toBindingModel := model, native := choice.native } } : Value)
      return ⟨#[raw] ++ continued.raw, native,
        choice.map (fun choice => #[choice.trace]), returned, none, completionSummary⟩
    -- A genuinely mixed block still has no single normal range-body model.
    return { continued with
      raw := #[raw] ++ continued.raw, native? := none, calls? := none
      completion? := completionSummary }
  match elements with
  | [] =>
      if allowFallthrough then
        let summary ← match completion with
          | none => pure none
          | some context => context.capture scope none
        return ⟨#[], some #[], some #[], none, some scope, summary⟩
      throwError "a value-producing source block must end with a return"
  | element :: rest => withRef element do
    -- The mathematical view uses local versions; rawBinding retains actual
    -- mutable declarations and assignments for the shared source semantics.
    if let `(doElem| let mut $name:ident $[: $annotation:term]? := $expression:term) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? := $expression)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn completion returnState
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $expression:term) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn completion returnState
    if let `(doElem| let mut $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem)
      return ← sequence names imports resultType scope (normalized :: rest) .mutable allowFallthrough localReturn completion returnState
    if let `(doElem| $name:ident := $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type := $expression)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn completion returnState
    if let `(doElem| $name:ident ← $expression:term) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $expression:term)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn completion returnState
    if let `(doElem| $name:ident ← $rhs:doElem) := element then
      let previous ← lookup scope name
      unless previous.mutable do throwErrorAt name "assignment requires a local declared with let mut"
      let type ← termOfExpr previous.type.nativeType
      let normalized ← `(doElem| let $name:ident : $type ← $rhs:doElem)
      return ← sequence names imports resultType scope (normalized :: rest) .assignment allowFallthrough localReturn completion returnState
    if let `(doElem| with_scratch do $body:doSeq) := element then
      let body ← sequence names imports resultType scope (getDoElems body).toList .immutable true localReturn completion returnState
      let bodySyntax : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (body.raw.map (·.raw))⟩
      let raw ← `(doElem| with_scratch do $bodySyntax:doSeq)
      if body.normalScope?.isNone && rest.isEmpty then
        return ⟨#[raw], none, none, none, none, none⟩
      let after := invalidateObservations
        (body.normalScope?.map (closeScope scope) |>.getD scope) true
      let continued ← sequence names imports resultType after rest .immutable
        (allowFallthrough || body.normalScope?.isNone) localReturn completion returnState
      return { continued with
        raw := #[raw] ++ continued.raw, native? := none, calls? := none
        returned? := if body.normalScope?.isSome then continued.returned? else none
        normalScope? := if body.normalScope?.isSome then continued.normalScope? else none
        completion? := none }
    if let `(doElem| while $condition:term do $body:doSeq) := element then
      -- Each round receives fresh mathematical observations at its actual heap;
      -- the optional whole-function model remains unavailable for general while.
      let captured := lexicalBindings scope
      let stateSyntax ← stateType captured.toList
      let stateNativeType ← resolveType stateSyntax
      let initial := mkIdent (← mkFreshUserName `whileState)
      let stateBinding ← parameterBinding initial stateNativeType
      let mut loopScope := #[]
      let mut nativePrefix := #[]
      for binding in captured, position in [:captured.size] do
        let field ← fieldProjection captured.size position ⟨initial.raw⟩
        let projected ← value [stateBinding] field
        let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
        loopScope := loopScope.push { binding with
          nativeName, model? := projected.model?.map (·.toBindingModel) }
        let type ← termOfExpr binding.type.nativeType
        nativePrefix := nativePrefix.push (← `(doElem| let $nativeName:ident : $type := $field))
      let boolType ← resolveType (← `(Bool))
      let guardElements ← returnElements condition
      let firstGuardAssignment := (← get).assignedSlots.size
      let guardBlock ← sequence names imports boolType loopScope.toList guardElements.toList
      let guardAssigned := (← get).assignedSlots.extract firstGuardAssignment (← get).assignedSlots.size
      let bodyBlock ← sequence names imports resultType loopScope.toList
        (getDoElems body).toList .immutable true localReturn completion returnState
      let ⟨rawRest, _, _, returned, normal, _⟩ ← sequence names imports resultType
        (invalidateObservations scope true)
        rest .immutable allowFallthrough localReturn completion returnState
      let tag := mkIdent (← mkFreshUserName `whileSite)
      let guard ← doTerm guardBlock.raw
      let body : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (bodyBlock.raw.map (·.raw))⟩
      let raw ← `(doElem| source_while_site% $tag:ident ($guard:term) do $body:doSeq)
      let fallback : PreparedBlock := ⟨#[raw] ++ rawRest, none, none, returned, normal, none⟩
      if localReturn then
        modify fun preparation => { preparation with
          completionWhiles := preparation.completionWhiles.push {
            tag := tag.getId, captured, state := stateBinding } }
        return fallback
      if guardAssigned.any (fun slot => captured.any (·.slot == slot)) then
        return fallback
      let some guardNative := guardBlock.native? | return fallback
      let some guardCalls := guardBlock.calls? | return fallback
      let some guardResult := guardBlock.returned? | return fallback
      let some normalScope := bodyBlock.normalScope? | return fallback
      let some bodyNative := bodyBlock.native? | return fallback
      let some bodyCalls := bodyBlock.calls? | return fallback
      let closed := closeScope loopScope.toList normalScope
      let post := closed.map fun binding => { binding with name := binding.nativeName }
      let bodyReturned ← value post (← stateValue post.toArray) (some stateNativeType)
      let some returnedModel := bodyReturned.model? | return fallback
      let guardTerm ← doTerm (nativePrefix ++ guardNative)
      let bodyTerm ← doTerm (nativePrefix ++ bodyNative ++
        #[← `(doElem| return $(returnedModel.native))])
      let guardNative ← `(fun ($initial:ident : $stateSyntax) => Id.run $guardTerm)
      let bodyNative ← `(fun ($initial:ident : $stateSyntax) => Id.run $bodyTerm)
      modify fun state => { state with whiles := state.whiles.push {
        tag := tag.getId, captured, state := stateBinding
        guard := guardCalls, guardResult, guardNative
        body := bodyCalls, returned := bodyReturned, bodyNative } }
      return fallback
    if let `(doElem| for $pattern:term in $collection:term do $body:doSeq) := element then
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
      -- The optional mathematical result also describes a real function return.
      -- Keep the source boundary unchanged: Core still receives localReturn.
      let bodyCompletion := some ({
        carried := bodyScope, stateType := stateNativeType, resultType } : CompletionContext)
      let preparedBody ← sequence names imports resultType sourceBodyScope
        (getDoElems body).toList .immutable true localReturn bodyCompletion
      let rawBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (preparedBody.raw.map (·.raw))⟩
      let rawCollection ← `([ $(start.raw) : $(stop.raw) : $(stride.raw) ])
      let raw ← `(doElem| source_range_site% $tag:ident ($pattern:term, $rawCollection:term)
        do $rawBody:doSeq)
      let sourceOnly : PrepareM PreparedBlock := do
        let continued ← sequence names imports resultType (invalidateObservations scope true)
          rest .immutable allowFallthrough localReturn completion returnState
        return { continued with
          raw := #[raw] ++ continued.raw, native? := none, calls? := none
          completion? := none }
      let completing : PrepareM PreparedBlock := do
        let some summary := preparedBody.completion? | return ← sourceOnly
        let some startModel := start.model? | return ← sourceOnly
        let some stopModel := stop.model? | return ← sourceOnly
        let some strideModel := stride.model? | return ← sourceOnly
        unless captured.all (·.model?.isSome) do return ← sourceOnly
        let initialValue ← value
          (captured.toList.map fun binding => { binding with name := binding.nativeName })
          (← fieldsTerm
            (captured.map (fun binding => (⟨binding.nativeName.raw⟩ : TSyntax `term))).toList)
          (some stateNativeType)
        let some initialModel := initialValue.model? | return ← sourceOnly
        let bodyTerm ← doTerm (nativePrefix ++ summary.native)
        let bodyNative ← `(fun ($cursor:ident : Nat) ($initial:ident : $stateSyntax) =>
          Id.run $bodyTerm)
        let returnedType ← termOfExpr resultType.nativeType
        let (nativeResult, embedding, mutableStep, initialMutable) ←
          completionRangeModel captured stateSyntax returnedType bodyNative
            initialModel startModel stopModel strideModel
        let resultName := mkIdent (← mkFreshUserName `rangeValue)
        let resultRaw := mkIdent (← mkFreshUserName `rangeSource)
        let resultObserved := mkIdent (← mkFreshUserName `rangeObserved)
        let nativeSubstitution := captured.filterMap fun binding =>
          binding.model?.map (fun model => (binding.nativeName.getId, model.model.raw))
        let theoremResult : TSyntax `term := ⟨nativeResult.raw.rewriteBottomUp fun node =>
          if node.isIdent then
            ((nativeSubstitution.find? (fun entry => entry.1 == node.getId)).map (·.2)).getD node
          else node⟩
        let rangeType := NativeType.prod (.option resultType) stateNativeType
        let result : Binding := {
          name := resultName, type := rangeType, rawName := resultRaw, relationName := resultObserved
          model? := some {
            model := theoremResult, rawModel := ⟨resultRaw.raw⟩
            observation := if rangeType.isIdentity then .refl else .named resultObserved.getId } }
        modify fun state => { state with ranges := state.ranges.push {
          tag := tag.getId, captured, state := stateBinding, index := indexBinding
          body := summary.calls, returned := summary.returned, bodyNative
          start, stop, stride, result,
          model := .completion resultType embedding mutableStep initialMutable } }
        let rangeTrace := Trace.range tag.getId #[initialValue] result
          (summary.calls.all Trace.preservesArrays)
        let nativeType ← termOfExpr rangeType.nativeType
        let mut nativeAfter := #[← `(doElem| let $resultName:ident : $nativeType := $nativeResult)]
        let mut after := scope
        for binding in captured, position in [:captured.size] do
          let projection ← fieldProjection captured.size position (← `($resultName:ident.2))
          let projected ← value [result] projection
          let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
          after := after.map fun current => if current.slot == binding.slot then
            { current with nativeName, model? := projected.model?.map (·.toBindingModel) } else current
          nativeAfter := nativeAfter.push (← `(doElem| let $nativeName:ident := $projection))
        let pending ← value [result] (← `($resultName:ident.1))
        let payloadName := mkIdent (← mkFreshUserName `completedValue)
        let payload ← parameterBinding payloadName resultType
        let payloadValue ← value [payload] ⟨payloadName.raw⟩ (some resultType)
        let choose (mathematical : Bool) (absent present : TSyntax `term) := do
          let model ← pending.requireModel
          let discriminant := if mathematical then model.model else model.native
          `(Option.elim $discriminant $absent
            (fun ($payloadName:ident : $returnedType) => $present))
        -- Prepare the actual source continuation only once. Its mathematical
        -- branch runs only on none, whether some records a local completion
        -- or a real function return propagated by Core.
        let continued ← sequence names imports resultType after rest
          .immutable allowFallthrough localReturn completion returnState
        let returnedBlock ← completedBlock after payloadValue
        let choice ← if continued.normalScope?.isNone then
            choiceModel true modelResultType continued returnedBlock choose (Trace.optionMatch pending payload)
          else pure none
        let native ← choice.mapM fun choice => do
          return nativeAfter ++ #[← `(doElem| return $(choice.native))]
        let returned := choice.map fun choice => ({
          type := modelResultType, raw := ⟨choice.result.rawName.raw⟩
          model? := choice.result.model?.map fun model => {
            toBindingModel := model, native := choice.native } } : Value)
        let completionSummary ← match completion with
          | none => pure none
          | some context => do
              let completed ← context.capture after (some payloadValue)
              let joined ← completionChoice true context continued.completion? completed
                choose (Trace.optionMatch pending payload)
              pure (CompletionSummary.prepend? (some nativeAfter) (some #[rangeTrace]) joined)
        return {
          raw := #[raw] ++ continued.raw, native? := native
          calls? := choice.map fun choice => #[rangeTrace, choice.trace]
          returned? := returned, normalScope? := continued.normalScope?
          completion? := completionSummary }
      -- These three checks require a fully modeled, normally continuing body.
      -- Within a local-return boundary the correspondence also proves that the
      -- actual pending-controlled guard and increment remain active.
      let some normalScope := preparedBody.normalScope? | return ← completing
      let some native := preparedBody.native? | return ← completing
      let some calls := preparedBody.calls? | return ← completing
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
        model := .fold embedding mutableStep initialMutable indices } }
      let mut after := scope
      let mut nativeAfter := #[← `(doElem| let $resultName:ident : $stateSyntax := $nativeResult)]
      for binding in captured, position in [:captured.size] do
        let projection ← fieldProjection captured.size position ⟨resultName.raw⟩
        let projected ← value [result] projection
        let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
        after := after.map fun current => if current.slot == binding.slot then
          { current with nativeName, model? := projected.model?.map (·.toBindingModel) } else current
        nativeAfter := nativeAfter.push (← `(doElem| let $nativeName:ident := $projection))
      let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn completion returnState
      let rangeTrace := Trace.range tag.getId #[initialValue] result (calls.all Trace.preservesArrays)
      return { continued with
        raw := #[raw] ++ continued.raw
        native? := (nativeAfter ++ ·) <$> continued.native?
        calls? := (#[rangeTrace] ++ ·) <$> continued.calls?
        completion? := CompletionSummary.prepend? (some nativeAfter) (some #[rangeTrace])
          continued.completion? }
    let statementConditional? ← match element with
      | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
          pure (some (condition, yes, no))
      | `(doElem| if $condition:term then $yes:doSeq) =>
          pure (some (condition, yes, (⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩ : TSyntax ``doSeq)))
      | _ => pure none
    if let some (condition, yes, no) := statementConditional? then
      let condition ← value scope condition
      expect element (← resolveType (← `(Bool))) condition.type
      let branchCompletion ← if localReturn || completion.isSome then
          some <$> CompletionContext.ofScope scope resultType
        else pure completion
      let firstAssignment := (← get).assignedSlots.size
      let yes ← sequence names imports resultType scope (getDoElems yes).toList
        .immutable true localReturn branchCompletion returnState
      let no ← sequence names imports resultType scope (getDoElems no).toList
        .immutable true localReturn branchCompletion returnState
      let assigned := (← get).assignedSlots.extract firstAssignment (← get).assignedSlots.size
      let yesBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (yes.raw.map (·.raw))⟩
      let noBody : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (no.raw.map (·.raw))⟩
      let raw ← `(doElem| if $(condition.raw) then $yesBody:doSeq else $noBody:doSeq)
      let choose (mathematical : Bool) (yes no : TSyntax `term) := do
        let model ← condition.requireModel
        let condition := if mathematical then model.model else model.native
        `(if $condition then $yes else $no)
      return ← continueChoice raw yes no condition.model?.isSome choose
        (Trace.conditional condition) branchCompletion assigned rest
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
          .immutable allowFallthrough localReturn completion returnState
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
      let branchCompletion ← if localReturn || completion.isSome then
          some <$> CompletionContext.ofScope scope resultType
        else pure completion
      let firstAssignment := (← get).assignedSlots.size
      let absent ← sequence names imports resultType scope (getDoElems noneBody).toList
        .immutable true localReturn branchCompletion returnState
      let present ← sequence names imports resultType (payload :: scope)
        (payloadBindings ++ getDoElems someBody).toList .immutable true localReturn branchCompletion returnState
      let assigned := (← get).assignedSlots.extract firstAssignment (← get).assignedSlots.size
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
        (Trace.optionMatch discriminant payload) branchCompletion assigned rest
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
          ← `(doElem| return $temporary:ident)] .immutable allowFallthrough localReturn completion returnState
    -- An unparenthesized `if` after `←` is a `doIf`, not a term.
    -- Normalize that parser shape before the shared typed conditional path.
    if let `(doElem| let $name:ident $[: $annotation:term]? ← $rhs:doElem) := element then
      if let `(doElem| do $body:doSeq) := rhs then
        let expression ← `(do $body:doSeq)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence names imports resultType scope (normalized :: rest) bindingKind allowFallthrough localReturn completion returnState
      if let `(doElem| if $test:term then $yes:doSeq else $no:doSeq) := rhs then
        let yesTerm ← branchTerm yes
        let noTerm ← branchTerm no
        let expression ← `(if $test:term then $yesTerm:term else $noTerm:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence names imports resultType scope (normalized :: rest) bindingKind allowFallthrough localReturn completion returnState
      if let `(doElem| match $discriminant:term with
          | $first:term => $firstBody:doSeq
          | $second:term => $secondBody:doSeq) := rhs then
        let firstBody ← branchTerm firstBody
        let secondBody ← branchTerm secondBody
        let expression ← `(match $discriminant:term with
          | $first:term => $firstBody:term
          | $second:term => $secondBody:term)
        let normalized ← `(doElem| let $name:ident $[: $annotation:term]? ← ($expression:term))
        return ← sequence names imports resultType scope (normalized :: rest) bindingKind allowFallthrough localReturn completion returnState
    let binding? := match element with
      | `(doElem| let $name:ident $[: $annotation:term]? ← $expression:term) =>
          some (name, annotation, expression)
      | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
          some (name, annotation, expression)
      | _ => none
    if let some (name, annotation, expression) := binding? then
      let prepareValueBlock (body : TSyntax ``doSeq)
          (closeBoundary : JoinSlot → Array (TSyntax `doElem) →
            TermElabM (Array (TSyntax `doElem))) : PrepareM PreparedBlock := do
        let some annotation := annotation
          | throwErrorAt name "a source value block requires an explicit result type"
        let selectedType ← resolveType annotation
        let firstAssignment := (← get).assignedSlots.size
        let returnedState ← CompletionContext.ofScope scope selectedType
        let returnedState? := if returnedState.carried.isEmpty then none else some returnedState
        let prepared ← sequence names imports selectedType scope (getDoElems body).toList
          .immutable false true none returnedState?
        if prepared.normalScope?.isSome then
          throwErrorAt expression "a value-producing block cannot finish without returning a value"
        let slot := mkIdent (← mkFreshUserName (name.getId.appendAfter "_join"))
        let joinSlot ← makeJoinSlot slot selectedType.coreTy
        let boundary ← closeBoundary joinSlot prepared.raw
        let rawPrefix := (← joinSlot.initialization) ++ boundary
        let stateInputs := do
          let context ← returnedState?
          let native ← prepared.native?
          let calls ← prepared.calls?
          let returned ← prepared.returned?
          let model ← returned.model?
          pure (context, native, calls, returned, model)
        if let some (context, native, calls, returned, model) := stateInputs then
          let snapshotName := mkIdent (← mkFreshUserName `valueBlockResult)
          let snapshotRaw := mkIdent (← mkFreshUserName `valueBlockSource)
          let observed := mkIdent (← mkFreshUserName `valueBlockObserved)
          let snapshot : Binding := {
            name := snapshotName, type := returned.type, rawName := snapshotRaw,
            relationName := observed
            model? := some {
              model := model.model, rawModel := ⟨snapshotRaw.raw⟩
              observation := if returned.type.isIdentity then .refl else .named observed.getId } }
          let nativeType ← termOfExpr returned.type.nativeType
          let nativeBody ← doTerm native
          let mut nativePrefix := #[← `(doElem|
            let $snapshotName:ident : $nativeType := Id.run $nativeBody)]
          let assigned := (← get).assignedSlots.extract firstAssignment (← get).assignedSlots.size
          let mut after := scope
          for binding in context.carried, index in [:context.carried.size] do
            unless assigned.contains binding.slot do continue
            let projection ← fieldProjection context.carried.size index
              (← `($snapshotName:ident.2))
            let projected ← value [snapshot] projection (some binding.type)
            let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
            after := after.map fun current =>
              if current.slot == binding.slot then
                { current with nativeName, model? := projected.model?.map (·.toBindingModel) }
              else current
            nativePrefix := nativePrefix.push (← `(doElem| let $nativeName:ident := $projection))
          let payload ← value [snapshot] (← `($snapshotName:ident.1)) (some selectedType)
          let nativeName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_native"))
          let binding : Binding := {
            name, nativeName, type := selectedType, rawName := name, relationName := observed
            model? := payload.model?.map (·.toBindingModel)
            slot := ← bindingSlot name, mutable := bindingMutable }
          nativePrefix := nativePrefix.push
            (← `(doElem| let $nativeName:ident := $snapshotName:ident.1))
          let continued ← sequence names imports resultType (binding :: after) rest
            .immutable allowFallthrough localReturn completion returnState
          let traces := #[Trace.valueBlock calls returned snapshot]
          return { continued with
            raw := rawPrefix ++ (← joinSlot.continuation name continued.raw bindingKind)
            native? := (nativePrefix ++ ·) <$> continued.native?
            calls? := (traces ++ ·) <$> continued.calls?
            completion? := CompletionSummary.prepend? (some nativePrefix) (some traces)
              continued.completion? }
        let modelInputs := do
          let native ← prepared.native?
          let _ ← prepared.calls?
          let returned ← prepared.returned?
          let model ← returned.model?
          pure (native, model)
        let after ← valueBlockScope scope firstAssignment modelInputs.isSome
        let nativeName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_native"))
        let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
        let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
        let binding : Binding := {
          name, nativeName, type := selectedType, rawName, relationName
          -- The proof trace already supplies this value and its observation.
          -- A new source join name is not a new mathematical call result.
          model? := modelInputs.map (fun (_, model) => model.toBindingModel)
          slot := ← bindingSlot name
          mutable := bindingMutable }
        let continued ← sequence names imports resultType (binding :: after) rest
          .immutable allowFallthrough localReturn completion returnState
        let nativeType ← termOfExpr selectedType.nativeType
        let nativeBinding ← modelInputs.mapM fun (native, _) => do
          let body ← doTerm native
          `(doElem| let $nativeName:ident : $nativeType := Id.run $body:term)
        return { continued with
          raw := rawPrefix ++ (← joinSlot.continuation name continued.raw bindingKind)
          native? := (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> continued.native?
          calls? := (· ++ ·) <$> prepared.calls? <*> continued.calls?
          completion? := CompletionSummary.prepend? ((fun binding => #[binding]) <$> nativeBinding)
            prepared.calls? continued.completion? }
      let continueValueBlock (choice : TSyntax `doElem) : PrepareM PreparedBlock :=
        prepareValueBlock ⟨Lean.Elab.Term.Do.mkDoSeq #[choice.raw]⟩ closeValueChoice
      if let some body := doParts? expression then
        return ← prepareValueBlock body fun slot elements =>
          getDoElems <$> slot.branch elements
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
          return ← sequence names imports resultType scope (read :: select :: rest) .immutable allowFallthrough localReturn completion returnState
        let .option payloadType := discriminant.type
          | throwErrorAt matched "native matching currently supports List and Option values"
        if scope.any (·.mutable) then
          -- Keep the List inspection above outside the join, and share the
          -- value-block observer for the selected arm's final mutable state.
          let firstElements ← returnElements firstBody
          let secondElements ← returnElements secondBody
          let firstSeq : TSyntax ``doSeq :=
            ⟨Lean.Elab.Term.Do.mkDoSeq (firstElements.map (·.raw))⟩
          let secondSeq : TSyntax ``doSeq :=
            ⟨Lean.Elab.Term.Do.mkDoSeq (secondElements.map (·.raw))⟩
          return ← continueValueBlock (← `(doElem| match $matched:term with
            | $first:term => $firstSeq:doSeq
            | $second:term => $secondSeq:doSeq))
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
        let firstAssignment := (← get).assignedSlots.size
        let ⟨noneRaw, noneNative, noneCalls, noneResult, noneNormal, _⟩ ←
          sequence names imports selectedType scope noneElements.toList .immutable false true
        let ⟨someRaw, someNative, someCalls, someResult, someNormal, _⟩ ←
          sequence names imports selectedType (payload :: scope) someElements.toList .immutable false true
        if noneNormal.isSome then
          throwErrorAt noneBody "a value-producing branch cannot finish without returning a value"
        if someNormal.isSome then
          throwErrorAt someBody "a value-producing branch cannot finish without returning a value"
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
          let noneValue ← noneResult
          let someValue ← someResult
          let noneResult ← noneValue.model?
          let someResult ← someValue.model?
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
        let after ← valueBlockScope scope firstAssignment choice.isSome
        let binding : Binding := {
          name, nativeName, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          slot := ← bindingSlot name
          mutable := bindingMutable }
        let ⟨rawRest, nativeRest, later, returned, normal, laterCompletion⟩ ←
          sequence names imports resultType (binding :: after) rest .immutable allowFallthrough localReturn completion returnState
        let rawPrefix := (← joinSlot.initialization) ++ #[
          ← `(doElem| match $(discriminant.raw):term with
            | none => $noneBlock:doSeq
            | some $payloadName:ident => $someBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $nativeName:ident : $nativeType := $nativeChoice)
        let choiceCalls : Option (Array Trace) := do
          let _ ← choice
          let noneCalls ← noneCalls
          let someCalls ← someCalls
          let noneResult ← noneResult
          let someResult ← someResult
          pure #[.optionMatch discriminant payload noneCalls someCalls noneResult someResult binding]
        let calls := (· ++ ·) <$> choiceCalls <*> later
        let completionSummary := CompletionSummary.prepend? (Array.singleton <$> nativeBinding)
          choiceCalls laterCompletion
        return ⟨rawPrefix ++ (← joinSlot.continuation name rawRest bindingKind),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest,
          calls, returned, normal, completionSummary⟩
      if let some (test, yes, no) := conditionalParts? expression then
        let some annotation := annotation
          | throwErrorAt name "a native conditional binding requires an explicit result type"
        if scope.any (·.mutable) then
          let yesElements ← returnElements yes
          let noElements ← returnElements no
          let yesSeq : TSyntax ``doSeq :=
            ⟨Lean.Elab.Term.Do.mkDoSeq (yesElements.map (·.raw))⟩
          let noSeq : TSyntax ``doSeq :=
            ⟨Lean.Elab.Term.Do.mkDoSeq (noElements.map (·.raw))⟩
          return ← continueValueBlock (← `(doElem|
            if $test:term then $yesSeq:doSeq else $noSeq:doSeq))
        let selectedType ← resolveType annotation
        let condition ← value scope test
        expect test (← resolveType (← `(Bool))) condition.type
        let yesElements ← returnElements yes
        let noElements ← returnElements no
        let firstAssignment := (← get).assignedSlots.size
        let ⟨yesRaw, yesNative, yesCalls, yesResult, yesNormal, _⟩ ←
          sequence names imports selectedType scope yesElements.toList .immutable false true
        let ⟨noRaw, noNative, noCalls, noResult, noNormal, _⟩ ←
          sequence names imports selectedType scope noElements.toList .immutable false true
        if yesNormal.isSome then
          throwErrorAt yes "a value-producing branch cannot finish without returning a value"
        if noNormal.isSome then
          throwErrorAt no "a value-producing branch cannot finish without returning a value"
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
          let yesValue ← yesResult
          let noValue ← noResult
          let yesResult ← yesValue.model?
          let noResult ← noValue.model?
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
        let after ← valueBlockScope scope firstAssignment choice.isSome
        let binding : Binding := {
          name, nativeName, type := selectedType, rawName, relationName,
          model? := choice.map (·.2)
          slot := ← bindingSlot name
          mutable := bindingMutable }
        let ⟨rawRest, nativeRest, later, returned, normal, laterCompletion⟩ ←
          sequence names imports resultType (binding :: after) rest .immutable allowFallthrough localReturn completion returnState
        let rawPrefix := (← joinSlot.initialization) ++ #[
          ← `(doElem| if $(condition.raw) then $yesBlock:doSeq else $noBlock:doSeq)]
        let nativeBinding ← choice.mapM fun (nativeChoice, _) =>
          `(doElem| let $nativeName:ident : $nativeType := $nativeChoice)
        let choiceCalls : Option (Array Trace) := do
          let _ ← choice
          let yesCalls ← yesCalls
          let noCalls ← noCalls
          let yesResult ← yesResult
          let noResult ← noResult
          pure #[.conditional condition yesCalls noCalls yesResult noResult binding]
        let calls := (· ++ ·) <$> choiceCalls <*> later
        let completionSummary := CompletionSummary.prepend? (Array.singleton <$> nativeBinding)
          choiceCalls laterCompletion
        return ⟨rawPrefix ++ (← joinSlot.continuation name rawRest bindingKind),
          (fun binding rest => #[binding] ++ rest) <$> nativeBinding <*> nativeRest,
          calls, returned, normal, completionSummary⟩
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
            (initial :: bindings.toList ++ rest) .immutable allowFallthrough localReturn completion returnState
        let canonical ← canonicalCall? imports scope expression
        if !action then
          if let some call := canonical then
            let rewritten ← `(doElem| let $pattern:term ← $call:term)
            return ← sequence names imports resultType scope (rewritten :: rest)
              .immutable allowFallthrough localReturn completion returnState
          if let some (called, rebuild) ← hoistValueCall? imports scope expression then
            let name := mkIdent (← mkFreshUserName `sourceValue)
            let called ← `(doElem| let $name:ident ← $called:term)
            let expression ← rebuild ⟨name.raw⟩
            let rewritten ← `(doElem| let $pattern:term := $expression:term)
            return ← sequence names imports resultType scope (called :: rewritten :: rest)
              .immutable allowFallthrough localReturn completion returnState
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
            .immutable allowFallthrough localReturn completion returnState
        let type ← prepareMacro (inferRawBindingType headers rawScope rewritten)
        return ← install (← resolveType (← rawTypeTerm type)) expression
    match element with
    | `(doElem| let $name:ident $[: $annotation:term]? := $expression:term) =>
        if let some call ← canonicalCall? imports scope expression then
          let binding ← `(doElem| let $name:ident $[: $annotation:term]? ← $call:term)
          return ← sequence names imports resultType scope (binding :: rest) bindingKind allowFallthrough localReturn completion returnState
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceValue)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let binding ← match bindingKind with
            | .assignment => `(doElem| $name:ident := $rewritten:term)
            | .mutable => `(doElem| let mut $name:ident $[: $annotation:term]? := $rewritten:term)
            | .immutable => `(doElem| let $name:ident $[: $annotation:term]? := $rewritten:term)
          return ← sequence names imports resultType scope (call :: binding :: rest) .immutable allowFallthrough localReturn completion returnState
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
              ((← markRawElements bindings).toList ++ call :: rest) .immutable allowFallthrough localReturn completion returnState
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
          .immutable allowFallthrough localReturn completion returnState
    | `(doElem| return $expression:term) =>
        if let some (called, rebuild) ← hoistValueCall? imports scope expression then
          let temporary := mkIdent (← mkFreshUserName `sourceResult)
          let call ← `(doElem| let $temporary:ident ← $called:term)
          let rewritten ← rebuild ⟨temporary.raw⟩
          let returned ← `(doElem| return $rewritten:term)
          return ← sequence names imports resultType scope (call :: returned :: rest)
            .immutable allowFallthrough localReturn completion returnState
        let result ← value scope expression (some resultType)
        expect element resultType result.type
        let returned ← completedValue scope result
        let native ← returned.bind (·.model?) |>.mapM fun model => do
          return #[← `(doElem| return $(model.native))]
        let recursive := (← get).currentRecursive
        let continued ← sequence names imports resultType scope rest .immutable true localReturn completion returnState
        modify fun state => { state with currentRecursive := recursive }
        let summary ← match completion with
          | none => pure none
          | some context => context.capture scope (some result)
        return ⟨#[← `(doElem| return $(result.raw))] ++ continued.raw,
          native, some #[], returned, none, summary⟩
    | `(doElem| $expression:term) =>
        let called := (← canonicalCall? imports scope expression).getD expression
        let operation? ← operationCall? names imports scope called
        if let some (operation, arguments) := operation? then
          unless operation.result.coreTy == .unit do
            throwErrorAt expression "a standalone source call must return Unit; bind its result"
          let ignored := mkIdent (← mkFreshUserName `ignoredResult)
          let (invocation, raw, native) ← prepareInvocation names scope ignored operation arguments
          let after := if operation.model?.isNone then invalidateObservations scope else scope
          let continued ← sequence names imports resultType after rest .immutable allowFallthrough localReturn completion returnState
          let nativeType ← termOfExpr operation.result.nativeType
          let nativePrefix ← native.mapM fun native =>
            `(doElem| let $ignored:ident : $nativeType := $native)
          return { continued with
            raw := #[← `(doElem| $raw:term)] ++ continued.raw
            native? := (fun binding rest => #[binding] ++ rest) <$> nativePrefix <*> continued.native?
            calls? := (fun _ rest => #[.call invocation] ++ rest) <$> native <*> continued.calls?
            completion? := CompletionSummary.prepend? (Array.singleton <$> nativePrefix)
              (native.map fun _ => #[.call invocation]) continued.completion? }
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
              ((← markRawElements bindings).toList ++ action :: rest) .immutable allowFallthrough localReturn completion returnState
          prepareMacro (checkRawAction headers rawScope rewritten)
          let ⟨rawRest, _, _, returned, normal, _⟩ ← sequence names imports resultType
            (invalidateObservations scope) rest .immutable allowFallthrough localReturn completion returnState
          return ⟨#[← `(doElem| $rewritten:term)] ++ rawRest, none, none, returned, normal, none⟩
    | _ => throwError "source blocks support typed product/Option patterns, lets, let mut and assignment, \
        source calls and raw operations, conditional/match bindings, with_scratch, \
        finite Nat ranges, general while and return; \
        break and continue are not supported here"

end Internal

end Complexity.Language.Syntax.Represented
