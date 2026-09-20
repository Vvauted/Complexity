/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Expression
import Complexity.Language.Representation.Preservation

/-!
# Common proof construction for represented correspondence

Build correspondence headers, current-heap observations and preservation
proofs. Proof traces only reassociate the same source action; they neither
insert runtime calls nor assign costs to mathematical observations.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def normalizeAction : TermElabM (TSyntax `tactic) :=
  `(tactic| simp only [Id.run, Id.instMonad, Bind.bind, Pure.pure, Functor.map,
    MonadLift.monadLift, ExceptT.lift,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run,
    StateT.bind, StateT.pure, StateT.map, Part.bind_some, Part.map_some,
    Bool.false_eq_true, reduceCtorEq, ↓reduceIte, Option.elim_none, Option.elim_some])

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

structure CorrespondenceHeader where
  nativeName : TSyntax `ident
  rawEquation : TSyntax `ident
  heap : TSyntax `ident
  parameters : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  nativeValue : TSyntax `term
  rawAction : TSyntax `term
  relations : Array RetainedObservation

def correspondenceHeader (names : DeclarationNames) (fn : Function) :
    TermElabM CorrespondenceHeader := do
  let nativeName := modelName names fn.name
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

def observationAt (argument : Value) (heap : TSyntax `term)
    (relations : Array RetainedObservation) : TermElabM (TSyntax `term) := do
  observationProof (← argument.requireModel).observation heap relations

partial def preservation (type : NativeType) (initial finish shape : TSyntax `term)
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
def resolveRaw (term : TSyntax `term) (known : Array (Name × TSyntax `term)) :
    TSyntax `term := ⟨term.raw.rewriteBottomUp fun stx =>
  if stx.isIdent then
    ((known.find? (fun entry => entry.1 == stx.getId)).map (·.2.raw)).getD stx
  else stx⟩
structure TraceContext where
  heap : TSyntax `term
  relations : Array RetainedObservation
  known : Array (Name × TSyntax `term)
  scalarEqualities : Array (TSyntax `term)
  shape : TSyntax `term
  contents : TSyntax `term

abbrev TraceFinish := TraceContext → TermElabM (Array (TSyntax `tactic))

abbrev RangeBodyProof :=
  Array Trace → Value → TSyntax `term → Array RetainedObservation →
    Array (Name × TSyntax `term) → Bool → TraceFinish →
      TermElabM (Array (TSyntax `tactic))
partial def traceAction (trace : List Trace) (returned : Value)
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
/-- Normalize proof composition against the very same generated source action.
The proof-only trace neither inserts a call nor changes its charged body. -/
def compositionTactics (header : CorrespondenceHeader) (model : FunctionModel) :
    TermElabM (Array (TSyntax `tactic)) := do
  if !model.calls.any Trace.containsRange && model.calls.any (fun | .call _ => false | _ => true) then
    let action ← traceAction model.calls.toList model.returned
    let canonical := mkIdent (← mkFreshUserName `sourceComposition)
    return #[← `(tactic|
      have $canonical:ident : $(header.rawAction) = $action := by
        rw [$(header.rawEquation):ident]
        simp only [Id.run, Id.instMonad, pure_bind, bind_pure, bind_assoc,
          bind_conditional, bind_optionMatch, Bool.false_eq_true, reduceCtorEq,
          ↓reduceIte, Option.elim_none, Option.elim_some]
        all_goals repeat' first
          | rfl
          | (split <;> simp_all only [Option.some.injEq, reduceCtorEq,
              Option.elim_none, Option.elim_some])
          | (congr 1; funext value)
        all_goals rfl),
      ← `(tactic| rw [$canonical:ident])]
  return #[← `(tactic| rw [$(header.rawEquation):ident])]

end Internal

end Complexity.Language.Syntax.Represented
