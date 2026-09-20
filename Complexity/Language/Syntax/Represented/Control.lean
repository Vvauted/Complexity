/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Calls

/-!
# Lexical state and control preparation for represented blocks

Prepare branch patterns, local-return result slots and mutable lexical state.
The source slot identity is retained across assignments; mathematical versions
and branch summaries do not introduce extra runtime variables.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

partial def conditionalParts? (expression : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term × TSyntax `term) :=
  match expression with
  | `(($inner:term)) => conditionalParts? inner
  | `(if $condition:term then $yes:term else $no:term) => some (condition, yes, no)
  | _ => none

partial def doParts? (expression : TSyntax `term) : Option (TSyntax ``doSeq) :=
  match expression with
  | `(($inner:term)) => doParts? inner
  | `(do $body:doSeq) => some body
  | _ => none
partial def matchParts? (expression : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) :=
  match expression with
  | `(($inner:term)) => matchParts? inner
  | `(match $discriminant:term with
      | $first:term => $firstBody:term
      | $second:term => $secondBody:term) =>
      some (discriminant, first, firstBody, second, secondBody)
  | _ => none

def branchTerm (elements : TSyntax ``doSeq) : TermElabM (TSyntax `term) := do
  if let [element] := (getDoElems elements).toList then
    if let `(doElem| do $nested:doSeq) := element then
      return ← `(do $nested:doSeq)
  `(do $elements:doSeq)

/-- A value branch and a block with a final return share the same lowering. -/
def returnElements (body : TSyntax `term) : TermElabM (Array (TSyntax `doElem)) :=
  match body with
  | `(do $elements:doSeq) => pure (getDoElems elements)
  | _ => return #[← `(doElem| return $body:term)]

def isNonePattern (pattern : TSyntax `term) : Bool :=
  match pattern with | `(none) | `(Option.none) | `(.none) => true | _ => false

def somePattern? (pattern : TSyntax `term) : Option (TSyntax `term) :=
  match pattern with
  | `(some $payload:term) | `(Option.some $payload:term) | `(.some $payload:term) => some payload
  | _ => none

/-- Use the shared checked pattern and nominal projection expander. A simple
name is the payload binder itself; other patterns share that same payload. -/
def preparePayloadPattern (pattern : TSyntax `term) (type : NativeType) :
    TermElabM (TSyntax `ident × Array (TSyntax `doElem)) := do
  let pattern ← liftMacroM (checkedBindingPattern pattern)
  match pattern with
  | .name name => return (name, #[])
  | _ =>
      let name := mkIdent (← mkFreshUserName `payload)
      return (name, ← patternBindings pattern type ⟨name.raw⟩)

def isNilPattern (pattern : TSyntax `term) : Bool :=
  match pattern with | `([]) | `(List.nil) => true | _ => false

def consNames? (pattern : TSyntax `term) :
    Option (TSyntax `ident × TSyntax `ident) :=
  match pattern with
  | `($head:ident :: $tail:ident) => some (head, tail)
  | _ => none

/-- A result slot never invents a heap handle. Its outer Option records whether
the block has returned, including when the returned value is itself `none`. -/
structure JoinSlot where
  name : TSyntax `ident
  type : TSyntax `term

inductive BindingKind where
  | immutable
  | mutable
  | assignment

/-- Actual mutable locals remain source assignments. Mathematical versions are
tracked separately and do not replace a loop-carried source variable. -/
def rawBinding (kind : BindingKind) (name : TSyntax `ident)
    (type expression : TSyntax `term) (action : Bool := false) :
    TermElabM (TSyntax `doElem) := do
  match kind, action with
  | .immutable, false => `(doElem| let $name:ident : $type := $expression)
  | .immutable, true => `(doElem| let $name:ident : $type ← $expression:term)
  | .mutable, false => `(doElem| let mut $name:ident : $type := $expression)
  | .mutable, true => `(doElem| let mut $name:ident : $type ← $expression:term)
  | .assignment, false => `(doElem| $name:ident := $expression)
  | .assignment, true => `(doElem| $name:ident ← $expression:term)

def makeJoinSlot (name : TSyntax `ident) (type : Ty) : TermElabM JoinSlot := do
  let rawType ← rawTypeTerm type
  return { name, type := ← `(Option $rawType) }

def JoinSlot.initialization (slot : JoinSlot) :
    TermElabM (Array (TSyntax `doElem)) := do
  return #[← `(doElem| let mut $(slot.name):ident : $(slot.type) := none)]

def JoinSlot.branch (slot : JoinSlot) (elements : Array (TSyntax `doElem)) :
    TermElabM (TSyntax ``doSeq) := do
  let body : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩
  let boundary ← `(doElem| source_local_return% ($(slot.name):ident)
    do $body:doSeq)
  return ⟨Lean.Elab.Term.Do.mkDoSeq #[boundary.raw]⟩

def JoinSlot.continuation (slot : JoinSlot) (name : TSyntax `ident)
    (elements : Array (TSyntax `doElem)) (kind : BindingKind := .immutable) :
    TermElabM (Array (TSyntax `doElem)) := do
  -- Value-block typing excludes normal fallthrough, so a successful boundary
  -- always supplies some payload. Faults never execute this continuation.
  let absent : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq #[]⟩
  let payload ← match kind with
    | .immutable => pure name
    | _ => pure (mkIdent (← mkFreshUserName `selectedValue))
  let elements ← match kind with
    | .immutable => pure elements
    | _ => do
        let `(Option $payloadType:term) := slot.type
          | throwError "a result slot must carry an optional source value"
        let binding ← rawBinding kind name payloadType ⟨payload.raw⟩
        pure (#[binding] ++ elements)
  let present : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩
  return #[← `(doElem| match $(slot.name):ident with
    | none => $absent:doSeq
    | some $payload:ident => $present:doSeq)]

/-- Shadowed locals are not accessible; distinct visible aliases remain distinct
state fields even when they happen to hold the same heap handle. -/
def visibleBindings (scope : List Binding) : Array Binding := Id.run do
  let mut visible := #[]
  for binding in scope do
    unless visible.any (fun previous : Binding => previous.name.getId == binding.name.getId) do
      visible := visible.push binding
  return visible

/-- Keep a slot at its declaration position, but observe its latest assignment.
Preparation versions are not extra source locals, and shadowed declarations
remain distinct even when their source spellings coincide. -/
def lexicalBindings (scope : List Binding) : Array Binding := Id.run do
  let mut declared := #[]
  for binding in scope.reverse do
    unless declared.any (fun previous : Binding => previous.slot == binding.slot) do
      let latest := (scope.find? (fun current => current.slot == binding.slot)).getD binding
      declared := declared.push latest
  return declared.reverse

partial def stateType (bindings : List Binding) : TermElabM (TSyntax `term) :=
  match bindings with
  | [] => `(Unit)
  | [binding] => termOfExpr binding.type.nativeType
  | binding :: rest => do `($(← termOfExpr binding.type.nativeType) × $(← stateType rest))

def stateValue (bindings : Array Binding) : TermElabM (TSyntax `term) :=
  fieldsTerm (bindings.map (fun binding => (⟨binding.name.raw⟩ : TSyntax `term))).toList


/-- Mathematical loop coordinates contain only locals that the body can update. -/
def mutableState (bindings : Array Binding) (state : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut fields := #[]
  for binding in bindings, index in [:bindings.size] do
    if binding.mutable then fields := fields.push (← fieldProjection bindings.size index state)
  fieldsTerm fields.toList

/-- Captures are closed over at loop entry, not selected again from each step's
mathematical result. The actual source accumulator still contains every field. -/
def packMutableState (bindings : Array Binding) (captured mutable : TSyntax `term) :
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
def invalidateObservations (scope : List Binding) (mutableLocals : Bool := false) :
    List Binding :=
  scope.map fun binding =>
    if !binding.type.isIdentity || (mutableLocals && binding.mutable) then
      { binding with model? := none }
    else binding

def parameterBinding (name : TSyntax `ident) (type : NativeType) : TermElabM Binding := do
  let rawName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_source"))
  let relationName := mkIdent (← mkFreshUserName (name.getId.appendAfter "_represented"))
  return {
    name, type, rawName, relationName
    model? := some {
      model := ⟨name.raw⟩
      rawModel := if type.isIdentity then ⟨name.raw⟩ else ⟨rawName.raw⟩
      observation := if type.isIdentity then .refl else .named relationName.getId } }

/-- Proof-side coordinates at a block's completion boundary. Source slot
identity selects the latest carried values, including shadowed declarations. -/
structure CompletionContext where
  carried : Array Binding
  stateType : NativeType
  resultType : NativeType

/-- Retain mutable lexical slots, including declarations hidden by a newer name.
Assignments contribute their latest observation without changing slot order;
immutable bindings remain available in the surrounding scope. -/
def CompletionContext.ofScope (scope : List Binding) (resultType : NativeType) :
    TermElabM CompletionContext := do
  let carried := (lexicalBindings scope).filter (·.mutable)
  let stateType ← resolveType (← Internal.stateType carried.toList)
  return { carried, stateType, resultType }

/-- A mathematical result records both local completion and the current state.
Its statements and call trace are proof-side summaries, not new source code. -/
structure CompletionSummary where
  native : Array (TSyntax `doElem)
  calls : Array Trace
  returned : Value

/-- Capture continuing or locally returning completion using the existing
field, option and product representations. Missing observations leave the
source block available without claiming a mathematical summary. -/
def CompletionContext.capture (context : CompletionContext) (scope : List Binding)
    (returned : Option Value) : TermElabM (Option CompletionSummary) := do
  let mut carried := #[]
  for binding in context.carried do
    let some latest := scope.find? (fun current => current.slot == binding.slot)
      | return none
    unless latest.model?.isSome do return none
    carried := carried.push { latest with name := latest.nativeName }
  let state ← value carried.toList (← stateValue carried) (some context.stateType)
  let some stateModel := state.model? | return none
  let pending : Value ← match returned with
    | none => do
        let absent ← `(none)
        pure ({
          type := .option context.resultType, raw := absent
          model? := some {
            native := absent, model := absent, rawModel := absent
            observation := .none context.resultType } } : Value)
    | some result => do
        pure ({
          type := .option context.resultType, raw := ← `(some $(result.raw))
          model? := ← result.model?.mapM fun model => do
            return ({
              native := ← `(some $(model.native)), model := ← `(some $(model.model))
              rawModel := ← `(some $(model.rawModel))
              observation := .some model.observation } : ValueModel) } : Value)
  let some pendingModel := pending.model? | return none
  let native ← `(($(pendingModel.native), $(stateModel.native)))
  let returned : Value := {
    type := .prod (.option context.resultType) context.stateType
    raw := ← `(($(pending.raw), $(state.raw)))
    model? := some {
      native
      model := ← `(($(pendingModel.model), $(stateModel.model)))
      rawModel := ← `(($(pendingModel.rawModel), $(stateModel.rawModel)))
      observation := .pair false pendingModel.observation stateModel.observation } }
  return some { native := #[← `(doElem| return $native)], calls := #[], returned }

/-- Prefix a completion summary only when both mathematical preparation and
its checked call trace are available. The final represented value is unchanged. -/
def CompletionSummary.prepend? (native : Option (Array (TSyntax `doElem)))
    (calls : Option (Array Trace)) (summary : Option CompletionSummary) :
    Option CompletionSummary := do
  let native ← native
  let calls ← calls
  let summary ← summary
  return { summary with native := native ++ summary.native, calls := calls ++ summary.calls }

private def completionSnapshot (summary : CompletionSummary) :
    TermElabM (Binding × TSyntax `doElem) := do
  let name := mkIdent (← mkFreshUserName `completionView)
  let rawName := mkIdent (← mkFreshUserName `completionSource)
  let relationName := mkIdent (← mkFreshUserName `completionObserved)
  let snapshot : Binding := {
    name, type := summary.returned.type, rawName, relationName
    model? := summary.returned.model?.map (·.toBindingModel) }
  let body ← doTerm summary.native
  let type ← termOfExpr snapshot.type.nativeType
  return (snapshot, ← `(doElem| let $name:ident : $type := Id.run $body:term))

/-- Share a completed mathematical state inside one closed proof-side term.
Only exact occurrences of this summary are replaced, and the fresh binder stays
outside any payload binders. Unfolding the let recovers the original term. -/
def shareCompletionModel (summary : CompletionSummary) (term : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let model ← summary.returned.requireModel
  let name := mkIdent (← mkFreshUserName `completionModel)
  let body : TSyntax `term := ⟨term.raw.rewriteBottomUp fun stx =>
    if stx == model.model.raw then name.raw else stx⟩
  let type ← termOfExpr summary.returned.type.nativeType
  `(let $name:ident : $type := $(model.model); $body)

/-- Name a mathematical completion and expose its carried state in the current
lexical scope. The snapshot reuses the original heap-indexed observation; its
fresh names do not introduce another source value or an observation premise.
Unassigned locals retain an existing observation, whose current-heap validity
is still checked by the call trace's preservation rules. -/
def CompletionSummary.openView (context : CompletionContext) (scope : List Binding)
    (assigned : Array Name) (summary : CompletionSummary) :
    TermElabM (Binding × List Binding × Array (TSyntax `doElem)) := do
  let (snapshot, native) ← completionSnapshot summary
  let state ← `(Prod.snd $(snapshot.name):ident)
  let mut after := scope
  let mut nativePrefix := #[native]
  for binding in context.carried, index in [:context.carried.size] do
    let previous := scope.find? (fun current => current.slot == binding.slot)
    if !assigned.contains binding.slot && previous.any (·.model?.isSome) then
      continue
    let projection ← fieldProjection context.carried.size index state
    let projected ← value [snapshot] projection (some binding.type)
    let nativeName := mkIdent (← mkFreshUserName (binding.name.getId.appendAfter "_native"))
    after := after.map fun current =>
      if current.slot == binding.slot then
        { current with nativeName, model? := projected.model?.map (·.toBindingModel) }
      else current
    let type ← termOfExpr binding.type.nativeType
    nativePrefix := nativePrefix.push (← `(doElem| let $nativeName:ident : $type := $projection))
  return (snapshot, after, nativePrefix)

/-- Rebuild the slots carried by an enclosing boundary. Mutable fields come
from the completion; omitted immutable fields retain their entry observations,
whose validity in the final heap is still checked through the same call trace.
Neither case reconstructs heap handles or emits source projections. -/
def CompletionSummary.project? (origin target : CompletionContext)
    (scope : List Binding)
    (summary : Option CompletionSummary) : TermElabM (Option CompletionSummary) := do
  let some summary := summary | return none
  if origin.carried.map (·.slot) == target.carried.map (·.slot) then
    return some summary
  let (snapshot, native) ← completionSnapshot summary
  let state ← `(Prod.snd $(snapshot.name):ident)
  let mut fields := #[]
  let mut observations := [snapshot]
  for binding in target.carried do
    if let some index := origin.carried.findIdx? (fun candidate => candidate.slot == binding.slot) then
      fields := fields.push (← fieldProjection origin.carried.size index state)
    else
      if binding.mutable then return none
      let some retained := scope.find? (fun candidate => candidate.slot == binding.slot)
        | return none
      if retained.mutable || retained.model?.isNone then return none
      observations := { retained with name := retained.nativeName } :: observations
      fields := fields.push ⟨retained.nativeName.raw⟩
  let selected ← fieldsTerm fields.toList
  let projected ← value observations (← `((Prod.fst $(snapshot.name):ident, $selected)))
    (some (.prod (.option target.resultType) target.stateType))
  let some model := projected.model? | return none
  let shared ← shareCompletionModel summary model.model
  let projected := { projected with model? := some { model with model := shared } }
  return some {
    native := #[native, ← `(doElem| return $(model.native))]
    calls := summary.calls, returned := projected }


/-- Raw statements and their normal lexical successor are independent of the
optional mathematical body, call trace and returned-value summary. -/
structure PreparedBlock where
  raw : Array (TSyntax `doElem)
  native? : Option (Array (TSyntax `doElem))
  calls? : Option (Array Trace)
  returned? : Option Value
  normalScope? : Option (List Binding)
  completion? : Option CompletionSummary := none

/-- Close a branch's local declarations by slot identity. Shadowing introduces
a new slot, while the latest assignment retains the enclosing slot. -/
def closeScope (entry exit : List Binding) : List Binding :=
  entry.map fun binding =>
    (exit.find? (fun candidate => candidate.slot == binding.slot)).getD binding

/-- A value result does not also summarize assignments to its enclosing locals.
Keep their actual slots, but discard precisely those outdated mathematical views.
Unknown branch effects additionally invalidate heap-content observations. -/
def valueBlockScope (scope : List Binding) (firstAssignment : Nat)
    (hasModel : Bool) : PrepareM (List Binding) := do
  let assigned := (← get).assignedSlots
  let assigned := assigned.extract firstAssignment assigned.size
  let scope := if hasModel then scope else invalidateObservations scope true
  return scope.map fun binding =>
    if assigned.contains binding.slot then { binding with model? := none } else binding

/-- A join of observations, not a new source local or instruction. -/
structure ChoiceModel where
  result : Binding
  native : TSyntax `term
  trace : Trace

def choiceModel (available : Bool) (type : NativeType)
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

/-- Join control-sensitive mathematical summaries with the same branch model
and trace used for ordinary value branches. No runtime result slot is added. -/
def completionChoice (available : Bool) (context : CompletionContext)
    (yes no : Option CompletionSummary)
    (choose : Bool → TSyntax `term → TSyntax `term → TermElabM (TSyntax `term))
    (trace : Array Trace → Array Trace → Value → Value → Binding → Trace) :
    TermElabM (Option CompletionSummary) := do
  let some yes := yes | return none
  let some no := no | return none
  let asBlock (summary : CompletionSummary) : PreparedBlock := {
    raw := #[], native? := some summary.native, calls? := some summary.calls
    returned? := some summary.returned, normalScope? := none }
  let type := NativeType.prod (.option context.resultType) context.stateType
  let some choice ← choiceModel available type (asBlock yes) (asBlock no) choose trace
    | return none
  let returned : Value := {
    type, raw := ⟨choice.result.rawName.raw⟩
    model? := choice.result.model?.map fun model => {
      toBindingModel := model, native := choice.native } }
  return some {
    native := #[← `(doElem| return $(choice.native))]
    calls := #[choice.trace], returned }

/-- Pack only proof-side normal results. Actual branch bodies keep their
fallthrough and never receive a synthesized source return. -/
def normalSummary (entry : List Binding) (mutable : Array Binding)
    (type : NativeType) (block : PreparedBlock) : TermElabM PreparedBlock := do
  let some scope := block.normalScope? | return block
  let state ← stateValue mutable
  let returned ← value (closeScope entry scope) state (some type)
  let native ← mapModelsM block.native? returned.model? fun native model => do
    return native.push (← `(doElem| return $(model.native)))
  return { block with native? := native, returned? := some returned }

end Internal

end Complexity.Language.Syntax.Represented
