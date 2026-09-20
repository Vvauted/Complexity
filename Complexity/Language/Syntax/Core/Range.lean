/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Pure
import Complexity.Language.Eval.Locals.Captures

/-!
# Generated finite-range correspondence

Constructs the raw and native finite-range correspondence declarations from the actual named
source loop, its coordinates and native step. Locally completed ranges retain their separate
control boundary and do not acquire the ordinary always-active range model.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

private def nativeRangeCorrespondenceDeclarations (program : TSyntax `ident)
    (callees : Array Callee) (sites : Array BlockSite) (site : BlockSite)
    (nativeResult : NativeCoordinate) (nativeSimplifications : Array (TSyntax `ident)) :
    MacroM (Array Syntax) := do
  let range ← standardRange site
  let name := loopMember site "eq_pure"
  let nativeName := loopMember site "eq_pure_native"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let regroup := loopMember site "regroup_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let code := loopMember site "Code"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardObserved := loopMember site "guard_observe"
  let bodyObserved := loopMember site "body_observe"
  let guardEquation := loopMember site "guard_eq"
  let bodyObservation := loopMember site "body"
  let nativeGuardEquation := loopMember site "native_guard_eq"
  let nativeBodyTransport := loopMember site "native_body_eq_of_eq"
  let nativeBodyEquation := loopMember site "native_body_eq"
  let nativeCaptured := loopMember site "NativeCaptured"
  let nativeRangeStop := loopMember site "nativeRangeStop"
  let nativeRangeStride := loopMember site "nativeRangeStep"
  let nativeBodyStep := loopMember site "nativeBodyStep"
  let resultType ← typeTerm site.result
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeNativeTypes mutableScope
  let capturedScope := site.scope.filter (! ·.isMutable)
  let captures ← scopeTuple capturedScope
  let capturedFields ← encodeNativeFields capturedScope (capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term))
  let nativeCaptureView := loopMember site "NativeCaptureView"
  let index ← freshProofName site.name `index
  let mutable ← freshProofName site.name `mutable
  let outcome ← freshProofName site.name `outcome
  let value ← freshProofName site.name `value
  let next ← freshProofName site.name `nextMutable
  let groupedCaptures ← freshProofName site.name `captures
  let groupedFields ← tupleFields capturedScope ⟨groupedCaptures.raw⟩
  let bindCaptures (term : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut term := term
    for (binding, field) in (capturedScope.toArray.zip groupedFields).reverse do
      if term.raw.hasIdent binding.proofName.getId then
        term ← `(let $(binding.proofName):ident : $(← bindingNativeType binding) := $field; $term)
    return term
  let groupedStop ← bindCaptures (← nativeMarkedValue range.stop)
  let groupedStride ← bindCaptures (← nativeMarkedValue range.stride)
  let tupleEta ← freshProofName site.name `mutableTupleEta
  let bodyPure ← freshProofName site.name `bodyPure
  let positive ← freshProofName site.name `positiveStep
  let tupleEtaRules := if mutableScope.isEmpty then #[] else #[tupleEta]
  let tupleEtaArgs ← namedSimpArgs tupleEtaRules
  let guardTupleEta ← if mutableScope.isEmpty then `(tactic| cases $mutable:ident) else do
    let rebuilt ← fieldsTuple (← tupleFields mutableScope ⟨mutable.raw⟩)
    `(tactic| have $tupleEta:ident : $rebuilt = $mutable:ident := $(← tupleExtProof mutableScope))
  let bodyTupleEta ← if mutableScope.isEmpty then `(tactic| cases $next:ident) else do
    let rebuilt ← fieldsTuple (← tupleFields mutableScope ⟨next.raw⟩)
    `(tactic| have $tupleEta:ident : $rebuilt = $next:ident := $(← tupleExtProof mutableScope))
  let step ← nativeRangeStep callees sites site
  let groupedStep ← bindCaptures step
  let initial ← scopeTuple mutableScope
  let inputFields ← encodeNativeFields mutableScope
    (← tupleFields mutableScope ⟨mutable.raw⟩)
  let bodyInvocation := Lean.Syntax.mkApp ⟨bodyObservation.raw⟩
    (mergeScopeFields site.scope (#[⟨index.raw⟩] ++ inputFields) capturedFields)
  let outputFields ← encodeNativeFields mutableScope
    (← tupleFields mutableScope (← `(($outcome:ident).2)))
  let normalLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[← `($index:ident + $(range.stride))] ++ outputFields) capturedFields)
  let returnedLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[⟨index.raw⟩] ++ outputFields) capturedFields)
  let encode ← `(($(nativeResult.equiv)).toFun)
  let bodyPremise ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) → $bodyInvocation =
      (let $outcome:ident := ($step:term) $index:ident $mutable:ident
       pure (match ($outcome:ident).1 with
         | none => (Complexity.Language.Control.normal, $normalLocals)
         | some $value:ident =>
             (Complexity.Language.Control.returned ($encode $value:ident), $returnedLocals))))
  let nativeGuardType ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $guard:ident $program:ident
      (($index:ident, $mutable:ident), $captures) =
      pure (Complexity.Language.Control.returned (decide ($index:ident < $(range.stop))),
        (($index:ident, $mutable:ident), $captures)))
  let nativeBodyType ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) →
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $body:ident $program:ident
      (($index:ident, $mutable:ident), $captures) =
      pure (match ($step:term) $index:ident $mutable:ident with
        | (none, $next:ident) => (Complexity.Language.Control.normal,
            (($index:ident + $(range.stride), $next:ident), $captures))
        | (some $value:ident, $next:ident) =>
            (Complexity.Language.Control.returned ($encode $value:ident),
              (($index:ident, $next:ident), $captures))))
  let groupedGuardType ← `(∀ ($groupedCaptures:ident : $nativeCaptured:ident)
    ($index:ident : Nat) ($mutable:ident : $mutableType),
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $guard:ident $program:ident
      (($index:ident, $mutable:ident), $groupedCaptures:ident) =
      pure (Complexity.Language.Control.returned
        (decide ($index:ident < $nativeRangeStop:ident $groupedCaptures:ident)),
        (($index:ident, $mutable:ident), $groupedCaptures:ident)))
  let groupedBodyType ← `(∀ ($groupedCaptures:ident : $nativeCaptured:ident)
    ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $nativeRangeStop:ident $groupedCaptures:ident →
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $body:ident $program:ident
      (($index:ident, $mutable:ident), $groupedCaptures:ident) =
      pure (match $nativeBodyStep:ident $groupedCaptures:ident $index:ident $mutable:ident with
        | (none, $next:ident) => (Complexity.Language.Control.normal,
            (($index:ident + $nativeRangeStride:ident $groupedCaptures:ident, $next:ident),
              $groupedCaptures:ident))
        | (some $value:ident, $next:ident) =>
            (Complexity.Language.Control.returned ($encode $value:ident),
              (($index:ident, $next:ident), $groupedCaptures:ident))))
  let groupedProof (type proof : TSyntax `term) : MacroM (TSyntax `term) := do
    let checked ← freshProofName site.name `checked
    let capturedEta ← freshProofName site.name `capturedTupleEta
    let rebuilt ← fieldsTuple groupedFields
    let applied := Lean.Syntax.mkApp ⟨checked.raw⟩ groupedFields
    `(by
      intro $groupedCaptures:ident
      have $checked:ident : $(← quantifyNativeScope capturedScope type) := $proof
      have $capturedEta:ident : $rebuilt = $groupedCaptures:ident := $(← tupleExtProof capturedScope)
      simpa only [$nativeRangeStop:ident, $nativeRangeStride:ident, $nativeBodyStep:ident, $capturedEta:ident,
        Equiv.refl_symm, Equiv.refl_apply] using $applied)
  let nativeGuardProof ← `(by
    intro $index:ident $mutable:ident
    $guardTupleEta:tactic
    simp only [$nativeCaptureView:ident, Complexity.Language.Stmt.observe_reindex, $captureView:ident,
      $guardObserved:ident, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map]
    simp only [$guardEquation:ident, map_pure, $regroup:ident,
      Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_apply_apply, Prod.map, Prod.mk.eta, $tupleEtaArgs,*])
  let nativeBodyProof ← `(fun $bodyPure:ident => by
    intro $index:ident $mutable:ident inside
    simp only [$nativeCaptureView:ident, Complexity.Language.Stmt.observe_reindex, $captureView:ident,
      $bodyObserved:ident, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map]
    simp only [Equiv.refl_apply] at $bodyPure:ident
    rw [$bodyPure:ident $index:ident $mutable:ident inside]
    cases stepEq : ($step:term) $index:ident $mutable:ident with
    | mk returned $next:ident =>
        $bodyTupleEta:tactic
        cases returned <;> simp only [stepEq, map_pure, $regroup:ident,
          Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.refl_apply,
          Equiv.symm_apply_apply, Prod.map, Prod.mk.eta, $tupleEtaArgs,*])
  let capturedArguments := capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term)
  let guardApplication := Lean.Syntax.mkApp ⟨nativeGuardEquation.raw⟩ #[captures]
  let bodyTransportApplication := Lean.Syntax.mkApp ⟨nativeBodyTransport.raw⟩ capturedArguments
  let priorSites := sites.takeWhile (fun other => other.name.getId != site.name.getId)
  let bodyElements := range.body ++ priorSites.flatMap fun other =>
    other.finiteRange.map (·.body) |>.getD #[]
  let dependencies := callees.filter fun callee =>
    bodyElements.any (fun element => element.raw.hasIdent callee.observation.getId)
  let equations ← dependencies.mapM fun callee => do
    let some equation := callee.pureEquation
      | Macro.throwErrorAt callee.name "a pure source callee must have a correspondence theorem"
    return equation
  let equations := equations ++ nativeSimplifications
  let loopRules := (priorSites.filter (·.hasStandardRange)).map fun other => loopMember other "eq_pure"
  let bodyRules := sites.map fun other => loopMember other "body_eq"
  let nativeBodyEquationProof ← curryNativeScope capturedScope (← `(by
    apply $bodyTransportApplication
    source_pure_block_correspondence [$equations:ident,*]
      ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*]))
  let native ← nativeRangeValue callees sites site (some ⟨positive.raw⟩)
  let actualArguments ← encodeNativeFields site.scope (site.scope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term))
  let actualInvocation := Lean.Syntax.mkApp ⟨site.name.raw⟩ actualArguments
  let actualLocals ← fieldsTuple actualArguments
  let finalLocals ← fieldsTuple (← encodeNativeFields site.scope
    (← tupleFields site.scope (← `(($outcome:ident).2))))
  let observedResult ← `(let $outcome:ident := $native
     pure ((($outcome:ident).1.elim
       (Complexity.Language.Control.normal (result := $resultType))
       (fun value => Complexity.Language.Control.returned (result := $resultType) ($encode value))),
       $finalLocals))
  let conclusion ← `($actualInvocation = $observedResult)
  let unquantified ← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $conclusion)
  let mut nativeType := unquantified
  let mut nativeProof ← `(fun $positive:ident $bodyPure:ident => by
    have actual := Complexity.Language.Stmt.observe_while_eq_forIn_range_step_encoded
      $nativeCaptureView:ident $program:ident $guard:ident $body:ident $captures
      $(range.stop) $(range.stride) $positive:ident $encode $step
      $guardApplication ($bodyTransportApplication $bodyPure:ident)
      $(range.cursor):ident $initial
    change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $actualLocals = _
    rw [$code:ident]
    funext heap
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    have execution := Complexity.Language.Stmt.observe_eq_some_iff.mp (congrFun actual heap)
    simpa only [$nativeCaptureView:ident, $captureView:ident, Equiv.symm_trans_apply, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map] using execution)
  for binding in site.scope.reverse do
    let type ← bindingNativeType binding
    nativeType ← `(∀ ($(binding.proofName):ident : $type), $nativeType)
    nativeProof ← `(fun ($(binding.proofName):ident : $type) => $nativeProof)
  -- Quantify raw coordinates for reliable rewriting at arbitrary source locals.
  -- The checked inverse is used only in this theorem, never in source execution.
  let mut rawScope : Scope := []
  let mut decodedArguments : Array (TSyntax `term) := #[]
  for binding in site.scope do
    let raw ← freshProofName site.name binding.proofName.getId
    rawScope := rawScope ++ [{ binding with proofName := raw, native := none }]
    decodedArguments := decodedArguments.push (← decodeNativeField binding ⟨raw.raw⟩)
  -- A rewrite rule must expose the raw invocation itself, not an
  -- encode/decode round trip around metavariables that rewriting cannot infer.
  let rawConclusion ← `($(scopeApplication rawScope site.name) = $observedResult)
  let mut rawType ← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $rawConclusion)
  for (binding, decoded) in (site.scope.toArray.zip decodedArguments).reverse do
    rawType ← `(let $(binding.proofName):ident : $(← bindingNativeType binding) := $decoded; $rawType)
  rawType ← quantifyScope rawScope rawType
  let nativeApplication := Lean.Syntax.mkApp ⟨nativeName.raw⟩ decodedArguments
  let rawProof ← curryScope rawScope (← `(by
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply, Equiv.refl_symm]
      using $nativeApplication))
  return #[
    (← `(command|
      /-- The actual fixed range endpoint selected from this loop's native captures. -/
      def $nativeRangeStop:ident ($groupedCaptures:ident : $nativeCaptured:ident) : Nat :=
        $groupedStop)).raw,
    (← `(command|
      /-- The actual fixed stride selected from this loop's native captures. -/
      def $nativeRangeStride:ident ($groupedCaptures:ident : $nativeCaptured:ident) : Nat :=
        $groupedStride)).raw,
    (← `(command|
      /-- The generated pure single-step view, with native mutable values and possible early return.
      Naming this view adds neither a source operation nor a separate user-written implementation. -/
      def $nativeBodyStep:ident ($groupedCaptures:ident : $nativeCaptured:ident) :
          Nat → $mutableType → Option $(nativeResult.type) × $mutableType := $groupedStep)).raw,
    (← `(command|
      /-- The actual guard observed at native mutable locals and fixed captures. -/
      theorem $nativeGuardEquation:ident : $groupedGuardType :=
        $(← groupedProof nativeGuardType (← curryNativeScope capturedScope nativeGuardProof)))).raw,
    (← `(command|
      /-- Transport the same body equation into native locals, retaining actual early returns. -/
      theorem $nativeBodyTransport:ident :
          $(← quantifyNativeScope capturedScope (← `($bodyPremise → $nativeBodyType))) :=
        $(← curryNativeScope capturedScope nativeBodyProof))).raw,
    (← `(command|
      /-- The same source body in native locals, using the already proved callee correspondences.
      Its result keeps normal continuation and early return distinct and preserves the heap. -/
      theorem $nativeBodyEquation:ident : $groupedBodyType :=
        $(← groupedProof nativeBodyType nativeBodyEquationProof))).raw,
    (← `(command|
      /-- The existing source range in checked native local coordinates. Encoding
      changes neither its iterations, early exits, heap nor source operation costs. -/
      theorem $nativeName:ident : $nativeType := $nativeProof)).raw,
    (← `(command|
      /-- The same range correspondence at arbitrary raw locals, reconstructed
      through the registered lossless native coordinates for theorem composition. -/
      theorem $name:ident : $rawType := $rawProof)).raw]

def rangeCorrespondenceDeclarations (program : TSyntax `ident)
    (callees : Array Callee) (sites : Array BlockSite) (site : BlockSite)
    (nativeSimplifications : Array (TSyntax `ident)) : MacroM Syntax := do
  let range ← standardRange site
  if let some native := site.nativeResult then
    return mkNullNode
      (← nativeRangeCorrespondenceDeclarations program callees sites site native nativeSimplifications)
  let name := loopMember site "eq_pure"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let regroup := loopMember site "regroup_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let code := loopMember site "Code"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardObserved := loopMember site "guard_observe"
  let bodyObserved := loopMember site "body_observe"
  let guardEquation := loopMember site "guard_eq"
  let bodyObservation := loopMember site "body"
  let resultType ← typeTerm site.result
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeValueTypes mutableScope
  let capturedScope := site.scope.filter (! ·.isMutable)
  let captures ← scopeTuple capturedScope
  let capturedFields := capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term)
  let index ← freshProofName site.name `index
  let mutable ← freshProofName site.name `mutable
  let outcome ← freshProofName site.name `outcome
  let value ← freshProofName site.name `value
  let bodyPure ← freshProofName site.name `bodyPure
  let positive ← freshProofName site.name `positiveStep
  let step ← nativeRangeStep callees sites site
  let initial ← scopeTuple mutableScope
  let inputFields ← tupleFields mutableScope ⟨mutable.raw⟩
  let bodyInvocation := Lean.Syntax.mkApp ⟨bodyObservation.raw⟩
    (mergeScopeFields site.scope (#[⟨index.raw⟩] ++ inputFields) capturedFields)
  let outputFields ← tupleFields mutableScope (← `(($outcome:ident).2))
  let normalLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[← `($index:ident + $(range.stride))] ++ outputFields) capturedFields)
  let returnedLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[⟨index.raw⟩] ++ outputFields) capturedFields)
  let bodyPremise ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) → $bodyInvocation =
      (let $outcome:ident := ($step:term) $index:ident $mutable:ident
       pure (match ($outcome:ident).1 with
         | none => (Complexity.Language.Control.normal, $normalLocals)
         | some $value:ident => (Complexity.Language.Control.returned $value:ident, $returnedLocals))))
  let native ← nativeRangeValue callees sites site (some ⟨positive.raw⟩)
  let conclusion ← `($(scopeApplication site.scope site.name) =
    (let $outcome:ident := $native
     pure ((($outcome:ident).1.elim
       (Complexity.Language.Control.normal (result := $resultType))
       (Complexity.Language.Control.returned (result := $resultType))),
       ($outcome:ident).2)))
  let type ← quantifyScope site.scope
    (← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $conclusion))
  let proof ← curryScope site.scope (← `(fun $positive:ident $bodyPure:ident => by
    have actual := Complexity.Language.Stmt.observe_while_eq_forIn_range_step
      $captureView:ident $program:ident $guard:ident $body:ident $captures
      $(range.stop) $(range.stride) $positive:ident $step
      (by
        intro $index:ident $mutable:ident
        simp only [$captureView:ident, Complexity.Language.Stmt.observe_reindex,
          $guardObserved:ident, $regroupSymm:ident]
        simp [$guardEquation:ident, $regroup:ident])
      (by
        intro $index:ident $mutable:ident inside
        simp only [$captureView:ident, Complexity.Language.Stmt.observe_reindex,
          $bodyObserved:ident, $regroupSymm:ident]
        rw [$bodyPure:ident $index:ident $mutable:ident inside]
        cases stepEq : ($step:term) $index:ident $mutable:ident with
        | mk returned next =>
            cases returned <;> simp only [stepEq, map_pure, $regroup:ident] <;> rfl)
      $(range.cursor):ident $initial
    change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $(← scopeTuple site.scope) = _
    rw [$code:ident]
    funext heap
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    have execution := Complexity.Language.Stmt.observe_eq_some_iff.mp (congrFun actual heap)
    simpa only [$captureView:ident, Equiv.symm_trans_apply, $regroupSymm:ident] using execution))
  return (← `(command|
    /-- Finite iteration correspondence, with its one-body obligation left in
    the enclosing function's callee and recursive-hypothesis scope. -/
    theorem $name:ident : $type := $proof)).raw

end Core

end Complexity.Language.Syntax
