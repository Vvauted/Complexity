/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Coordinates
import Complexity.Language.Eval.Locals.Verification

/-!
# Generated loop contracts and termination rules

Constructs raw/native loop contracts, independent guard/body rules, related mathematical-state
contracts and well-founded, natural-variant or counted-frame wrappers. The author still supplies
invariants and step contracts; these builders only compose the existing source semantic rules.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def loopNativeContractDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  unless hasNativeCoordinates site do return #[]
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutable := loopMember site "NativeMutable"
  let captured := loopMember site "NativeCaptured"
  let view := loopMember site "NativeCaptureView"
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let pre ← freshProofName site.name `pre
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let afterFields ← tupleFields mutableScope (← `(($after:ident).1))
  let app (name : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨name.raw⟩ arguments
  let preType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let normalType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyNativeScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let rawPre ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap) =>
    $(app pre (beforeFields.push ⟨heap.raw⟩)))
  let rawNormal ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap)
    ($after:ident : $mutable:ident × $captured:ident) ($finish:ident : Complexity.Language.Heap) =>
    $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let captures ← scopeTuple capturedScope
  let mut declarations := #[]
  for (suffix, codeSuffix, result) in
      [("native_guard_contract", "Guard", Ty.bool),
       ("native_body_contract", "Body", site.result),
       ("native_contract", "Code", site.result)] do
    let name := loopMember site suffix
    let code := loopMember site codeSuffix
    let rawResult ← valueTypeTerm result
    let nativeResult := if codeSuffix == "Guard" then none else site.nativeResult
    let resultType ← match nativeResult with
      | some native => pure native.type
      | none => pure rawResult
    let decoded ← match nativeResult with
      | some native => `(($(native.equiv)).symm $value:ident)
      | none => pure (⟨value.raw⟩ : TSyntax `term)
    let returnedType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap →
      $resultType → $(← quantifyNativeScope afterScope (← `(Complexity.Language.Heap → Prop)))))
    let rawReturned ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap)
      ($value:ident : $rawResult) ($after:ident : $mutable:ident × $captured:ident)
      ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (beforeFields ++ #[⟨heap.raw⟩, decoded] ++ afterFields ++ #[⟨finish.raw⟩])))
    let type ← quantifyNativeScope capturedScope (← `($preType → $normalType → $returnedType → Prop))
    let definition ← curryNativeScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident =>
      Complexity.Language.Stmt.BlockSpec
        (fun ($before:ident : $mutable:ident) =>
          Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
            ($before:ident, $captures)) $rawPre $rawNormal $rawReturned))
    declarations := declarations.push (← `(command|
      /-- The actual block contract with native mutable parameters and fixed captures.
      Only the returned predicate decodes the source value; control and both heaps stay unchanged. -/
      abbrev $name:ident : $type := $definition)).raw
  return declarations

def loopContractDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutableType := loopMember site "Mutable"
  let capturedType := loopMember site "Captured"
  let localsType := loopMember site "Locals"
  let captureView := loopMember site "CaptureView"
  let captures ← scopeTuple capturedScope
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let current ← freshProofName site.name `current
  let value ← freshProofName site.name `value
  let pre ← freshProofName site.name `pre
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let mutableAfterFields ← tupleFields mutableScope ⟨after.raw⟩
  let afterFields ← tupleFields mutableScope (← `(($after:ident).1))
  let nativeAfterFields := (splitScopeFields site.scope
    (← tupleFields site.scope ⟨after.raw⟩)).1
  let sourceBefore := mutableScope.toArray.map fun binding => (⟨binding.proofName.raw⟩ : TSyntax `term)
  let app (name : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨name.raw⟩ arguments
  let preType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let normalType ← quantifyScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let rawPre ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) => $(app pre (beforeFields.push ⟨heap.raw⟩)))
  let rawNormal ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap)
    ($after:ident : $mutableType:ident × $capturedType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let mutableNormal ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ mutableAfterFields ++ #[⟨finish.raw⟩])))
  let mut declarations := #[]
  for (suffix, observationSuffix, codeSuffix, result) in
      [("guard_contract", "guard", "Guard", Ty.bool),
       ("body_contract", "body", "Body", site.result),
       ("contract", "", "Code", site.result)] do
    let name := loopMember site suffix
    let iffName := loopMember site (suffix ++ "_iff")
    let observation := if observationSuffix.isEmpty then site.name
      else loopMember site observationSuffix
    let observed := loopMember site
      (if observationSuffix.isEmpty then "observe" else observationSuffix ++ "_observe")
    let code := loopMember site codeSuffix
    let resultType ← typeTerm result
    let result ← valueTypeTerm result
    let returnedType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → $result →
      $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
    let rawReturned ← `(fun ($before:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) ($value:ident : $result)
      ($after:ident : $mutableType:ident × $capturedType:ident)
      ($finish:ident : Complexity.Language.Heap) =>
        $(app returned (beforeFields ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          afterFields ++ #[⟨finish.raw⟩])))
    let mutableReturned ← `(fun ($before:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) ($value:ident : $result)
      ($after:ident : $mutableType:ident) ($finish:ident : Complexity.Language.Heap) =>
        $(app returned (beforeFields ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          mutableAfterFields ++ #[⟨finish.raw⟩])))
    let type ← quantifyScope capturedScope
      (← `($preType → $normalType → $returnedType → Prop))
    let definition ← curryScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident =>
      Complexity.Language.Stmt.BlockSpec
        (fun ($before:ident : $mutableType:ident) =>
          Complexity.Language.Stmt.observe $captureView:ident $code:ident $program:ident
            ($before:ident, $captures)) $rawPre $rawNormal $rawReturned))
    declarations := declarations.push (← `(command|
      /-- Relational total correctness with ordinary mutable parameters and fixed captures.
      The existing block contract retains both actual heaps and excludes faults. -/
      abbrev $name:ident : $type := $definition)).raw
    let contract := app name
      ((capturedScope.toArray.map fun binding => ⟨binding.proofName.raw⟩) ++
        #[⟨pre.raw⟩, ⟨normal.raw⟩, ⟨returned.raw⟩])
    let normalPost := app normal (sourceBefore ++ #[⟨heap.raw⟩] ++
      nativeAfterFields ++ #[⟨finish.raw⟩])
    let returnedPost := app returned (sourceBefore ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
      nativeAfterFields ++ #[⟨finish.raw⟩])
    let ordinary ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
      $(app pre (sourceBefore.push ⟨heap.raw⟩)) →
      Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
        $(scopeApplication site.scope observation)
        (fun $current:ident => ⟨$current:ident = $heap:ident⟩)
        (fun outcome $finish:ident => ⟨match outcome.1 with
          | .normal => let $after:ident : $localsType:ident := outcome.2; $normalPost
          | .returned $value:ident =>
              let $after:ident : $localsType:ident := outcome.2; $returnedPost
          | .fault _ => False⟩, ⟨⟩)))
    let iffType ← quantifyScope capturedScope (← `(∀ ($pre:ident : $preType)
      ($normal:ident : $normalType) ($returned:ident : $returnedType), $contract ↔ $ordinary))
    let regroup := loopMember site "regroup_apply"
    let regroupSymm := loopMember site "regroup_symm_apply"
    let outcome ← freshProofName site.name `outcome
    -- The generic and declaration-specialized matches have distinct motives.
    -- Compare only their actual control branches, leaving the action opaque.
    let postProof ← `(by
      apply Iff.of_eq
      congr 1
      apply Prod.ext
      · funext $outcome:ident $finish:ident
        rcases $outcome:ident with ⟨control, locals⟩
        cases control <;> rfl
      · rfl)
    -- `Prod.forall` also exposes a product-valued individual binding. Expand
    -- exactly those source types, stopping before the opaque Triple itself.
    let rec productCongr (type : Ty) (proof : TSyntax `term) : MacroM (TSyntax `term) := do
      match type with
      | .prod left right => productCongr left (← productCongr right proof)
      | _ =>
          let parameter ← freshProofName site.name `mutableField
          `(forall_congr' (fun ($parameter:ident : $(← valueTypeTerm type)) => $proof))
    let mut matchProof ← `(forall_congr' (fun ($heap:ident : Complexity.Language.Heap) =>
      imp_congr_right (fun _ => $postProof)))
    for binding in mutableScope.reverse do
      matchProof ← productCongr binding.type matchProof
    let proof ← curryScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident => by
      simp only [$name:ident, $captureView:ident, Complexity.Language.Stmt.observe_reindex]
      simp only [Complexity.Language.Stmt.BlockSpec.map_iff]
      simp only [$observed:ident, $regroup:ident, $regroupSymm:ident,
        Complexity.Language.Stmt.BlockSpec,
        $mutableType:ident, Prod.forall, forall_const]
      exact $matchProof))
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Introduce named mutable variables directly, without unpacking internal coordinates. -/
      theorem $iffName:ident : $iffType := $proof)).raw
    let specName := loopMember site
      (if observationSuffix.isEmpty then "spec" else observationSuffix ++ "_spec")
    let frame := loopMember site
      (if observationSuffix.isEmpty then "preservesCaptures"
       else observationSuffix ++ "_preservesCaptures")
    let view := loopMember site "View"
    let regroupName := loopMember site "Regroup"
    let specification ← freshProofName site.name `specification
    let post ← freshProofName site.name `post
    let postType ← `(Std.Do.PostCond
      (Complexity.Language.Control $resultType × $localsType:ident)
      (.arg Complexity.Language.Heap .pure))
    let finalValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
    let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
    let finalLocals ← fieldsTuple (mergeScopeFields site.scope finalValues capturedValues)
    let normalConsequence ← quantifyScope afterScope
      (← `(∀ ($finish:ident : Complexity.Language.Heap),
        $(app normal (sourceBefore ++ #[⟨heap.raw⟩] ++ finalValues ++ #[⟨finish.raw⟩])) →
        (($post:ident).1 (.normal, $finalLocals) $finish:ident).down))
    let returnedConsequenceBody ← quantifyScope afterScope
      (← `(∀ ($finish:ident : Complexity.Language.Heap),
        $(app returned (sourceBefore ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          finalValues ++ #[⟨finish.raw⟩])) →
        (($post:ident).1 (.returned $value:ident, $finalLocals) $finish:ident).down))
    let returnedConsequence ← `(∀ ($value:ident : $result), $returnedConsequenceBody)
    let nativeSpec ← quantifyScope mutableScope (← `(∀ ($post:ident : $postType),
      Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
        $(scopeApplication site.scope observation)
        (fun $heap:ident => ⟨$(app pre (sourceBefore.push ⟨heap.raw⟩)) ∧
          $normalConsequence ∧ $returnedConsequence⟩) $post:ident))
    let specType ← quantifyScope capturedScope (← `(∀ {$pre:ident : $preType}
      {$normal:ident : $normalType} {$returned:ident : $returnedType}
      ($specification:ident : $contract), $nativeSpec))
    let specProof ← curryScope mutableScope (← `(fun $post:ident => by
      simpa only [$regroupSymm:ident, $observed:ident, Prod.forall, forall_const] using
        Complexity.Language.Stmt.observe_fixed_spec $view:ident $regroupName:ident
          $program:ident $code:ident $frame:ident $captures
          (pre := $rawPre) (normal := $mutableNormal) (returned := $mutableReturned)
          $specification:ident
          $(← scopeTuple mutableScope) $post:ident))
    let specProof ← curryScope capturedScope
      (← `(fun {$pre:ident} {$normal:ident} {$returned:ident} $specification:ident => $specProof))
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Apply a chosen mathematical contract to the native block action.
      Continuations see ordinary mutable outputs; proved frames restore the fixed captures. -/
      theorem $specName:ident : $specType := $specProof)).raw
  return declarations

private def loopTerminationStepType (site : BlockSite)
    (invariant progress normal returned : TSyntax `ident) (wellFoundedMode : Bool) :
    MacroM (TSyntax `term) := do
  let afterGuardScope ← freshMutableScope site "afterGuard_"
  let afterBodyScope ← freshMutableScope site "afterBody_"
  let startHeap ← freshProofName site.name `startHeap
  let currentHeap ← freshProofName site.name `currentHeap
  let guardOutcome ← freshProofName site.name `guardOutcome
  let afterGuardHeap ← freshProofName site.name `afterGuardHeap
  let bodyOutcome ← freshProofName site.name `bodyOutcome
  let afterBodyHeap ← freshProofName site.name `afterBodyHeap
  let value ← freshProofName site.name `value
  let again ← freshProofName site.name `again
  let decrease ← if wellFoundedMode then do
      let afterMutable ← scopeTuple (afterBodyScope.filter (·.isMutable))
      let beforeMutable ← scopeTuple (site.scope.filter (·.isMutable))
      `($progress:ident ($afterMutable, $afterBodyHeap:ident)
        ($beforeMutable, $startHeap:ident))
    else
      `($(mutableApplication afterBodyScope progress ⟨afterBodyHeap.raw⟩) <
        $(mutableApplication site.scope progress ⟨startHeap.raw⟩))
  let bodyNormal ← `($(mutableApplication afterBodyScope invariant ⟨afterBodyHeap.raw⟩) ∧
    $decrease)
  let bodyReturned := mutableApplication afterBodyScope returned ⟨afterBodyHeap.raw⟩ #[⟨value.raw⟩]
  let bodyPost ← `(match ($bodyOutcome:ident).1 with
    | .normal => $bodyNormal
    | .returned $value:ident => $bodyReturned
    | .fault _ => False)
  let bodyPost ← bindMutableFields afterBodyScope (← `(($bodyOutcome:ident).2)) bodyPost
  let bodyInvocation := scopeApplication afterGuardScope (loopMember site "body")
  let bodySpec ← `(Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
    $bodyInvocation (fun $currentHeap:ident => ⟨$currentHeap:ident = $afterGuardHeap:ident⟩)
    (fun $bodyOutcome:ident $afterBodyHeap:ident => ⟨$bodyPost⟩, ⟨⟩))
  let guardNormal := mutableApplication afterGuardScope normal ⟨afterGuardHeap.raw⟩
  let guardPost ← `(match ($guardOutcome:ident).1 with
    | .returned $again:ident => if $again:ident then $bodySpec else $guardNormal
    | .normal => False
    | .fault _ => False)
  let guardPost ← bindMutableFields afterGuardScope (← `(($guardOutcome:ident).2)) guardPost
  let guardInvocation := scopeApplication site.scope (loopMember site "guard")
  let step ← `(∀ ($startHeap:ident : Complexity.Language.Heap),
    $(mutableApplication site.scope invariant ⟨startHeap.raw⟩) →
    Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
      $guardInvocation (fun $currentHeap:ident => ⟨$currentHeap:ident = $startHeap:ident⟩)
      (fun $guardOutcome:ident $afterGuardHeap:ident => ⟨$guardPost⟩, ⟨⟩))
  quantifyScope (site.scope.filter (·.isMutable)) step

def loopIndependentContractDeclaration (program : TSyntax `ident) (site : BlockSite)
    (wellFoundedMode : Bool) : MacroM Syntax := do
  let name := loopMember site
    (if wellFoundedMode then "wellFounded_contract" else "variant_contract")
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutableType := loopMember site "Mutable"
  let captureView := loopMember site "CaptureView"
  let invariant ← freshProofName site.name `invariant
  let progress ← freshProofName site.name (if wellFoundedMode then `relation else `variant)
  let wellFounded ← freshProofName site.name `wellFounded
  let ready ← freshProofName site.name `ready
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let guardSpec ← freshProofName site.name `guardSpec
  let bodySpec ← freshProofName site.name `bodySpec
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let again ← freshProofName site.name `again
  let initial ← freshProofName site.name `initial
  let captures ← scopeTuple capturedScope
  let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let beforeValues := mutableScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let afterValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let app (function : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨function.raw⟩ arguments
  let contract (suffix : String) (pre normal returned : TSyntax `term) :=
    app (loopMember site suffix) (capturedValues ++ #[pre, normal, returned])
  let ignoreStart (body : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut result ← `(fun _ => $body)
    for _ in mutableScope do result ← `(fun _ => $result)
    return result
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let readyType ← quantifyScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let result ← valueTypeTerm site.result
  let returnedType ← `($result → $predicateType)
  let progressType ← if wellFoundedMode then
      `(($mutableType:ident × Complexity.Language.Heap) →
        ($mutableType:ident × Complexity.Language.Heap) → Prop)
    else quantifyScope mutableScope (← `(Complexity.Language.Heap → Nat))
  let falseNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) => False)))
  let guardReturned ← curryScope mutableScope
    (← `(fun ($heap:ident : Complexity.Language.Heap) ($again:ident : Bool) =>
      $(← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
        if $again:ident then
          $(app ready (beforeValues ++ #[⟨heap.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩]))
        else $(app normal (afterValues.push ⟨finish.raw⟩)))))))
  let guardType := contract "guard_contract" ⟨invariant.raw⟩ falseNormal guardReturned
  let decrease ← if wellFoundedMode then
      `($progress:ident ($(← scopeTuple afterScope), $finish:ident)
        ($(← scopeTuple mutableScope), $heap:ident))
    else
      `($(app progress (afterValues.push ⟨finish.raw⟩)) <
        $(app progress (beforeValues.push ⟨heap.raw⟩)))
  let bodyNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app invariant (afterValues.push ⟨finish.raw⟩)) ∧ $decrease)))
  let finalReturnedBody ← curryScope afterScope
    (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩]))))
  let finalReturned ← ignoreStart (← `(fun ($value:ident : $result) => $finalReturnedBody))
  let bodyType ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
    $(app invariant (beforeValues.push ⟨heap.raw⟩)) →
    $(contract "body_contract" (app ready (beforeValues.push ⟨heap.raw⟩))
      bodyNormal finalReturned)))
  let finalNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (afterValues.push ⟨finish.raw⟩)))))
  let conclusion := contract "contract" ⟨invariant.raw⟩ finalNormal finalReturned
  let mut type ← `(∀ ($ready:ident : $readyType) ($normal:ident : $predicateType)
    ($returned:ident : $returnedType) ($guardSpec:ident : $guardType)
    ($bodySpec:ident : $bodyType), $conclusion)
  if wellFoundedMode then
    type ← `(∀ ($wellFounded:ident : WellFounded $progress:ident), $type)
  type ← quantifyScope capturedScope (← `(∀ ($invariant:ident : $predicateType)
    ($progress:ident : $progressType), $type))
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let afterFields ← tupleFields mutableScope ⟨after.raw⟩
  let rawPredicate (predicate : TSyntax `ident) :=
    `(fun ($before:ident : $mutableType:ident) ($heap:ident : Complexity.Language.Heap) =>
      $(app predicate (beforeFields.push ⟨heap.raw⟩)))
  let rawReady ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app ready (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let rawReturned ← `(fun ($value:ident : $result) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let rawBody ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) $initial:ident =>
      $(app bodySpec (beforeFields ++ #[⟨heap.raw⟩, ⟨initial.raw⟩])))
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let specification ← if wellFoundedMode then
      `(Complexity.Language.Stmt.observe_while_fixed_contract
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $(← rawPredicate invariant)
        $progress:ident $wellFounded:ident $rawReady $(← rawPredicate normal)
        $rawReturned $guardSpec:ident $rawBody)
    else
      `(Complexity.Language.Stmt.observe_while_fixed_variant_contract
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $(← rawPredicate invariant)
        $(← rawPredicate progress) $rawReady $(← rawPredicate normal)
        $rawReturned $guardSpec:ident $rawBody)
  let mut proof ← `(fun $ready:ident $normal:ident $returned:ident
    $guardSpec:ident $bodySpec:ident => $specification)
  if wellFoundedMode then proof ← `(fun $wellFounded:ident => $proof)
  proof ← curryScope capturedScope (← `(fun $invariant:ident $progress:ident => $proof))
  return (← `(command|
    /-- Prove a named loop from independent mathematical guard and body contracts.
    Actual guard effects and early body returns are retained; only normal iterations decrease. -/
    theorem $name:ident : $type := $proof)).raw

/-- Specialize the existing loop rule to a counted traversal and a transitive
heap frame. Source contracts, not the syntax of the body, justify each step. -/
def loopCountFrameContractDeclaration (program : TSyntax `ident) (site : BlockSite) :
    MacroM Syntax := do
  let name := loopMember site "count_frame_contract"
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let count ← freshProofName site.name `count
  let limit ← freshProofName site.name `limit
  let invariant ← freshProofName site.name `invariant
  let frame ← freshProofName site.name `frame
  let frameTrans ← freshProofName site.name `frameTrans
  let normal ← freshProofName site.name `normal
  let guardSpec ← freshProofName site.name `guardSpec
  let bodySpec ← freshProofName site.name `bodySpec
  let exit ← freshProofName site.name `exit
  let initial ← freshProofName site.name `initial
  let before ← freshProofName site.name `before
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let again ← freshProofName site.name `again
  let captures ← scopeTuple capturedScope
  let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let beforeValues := mutableScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let afterValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let app (function : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨function.raw⟩ arguments
  let contract (suffix : String) (pre normal returned : TSyntax `term) :=
    app (loopMember site suffix) (capturedValues ++ #[pre, normal, returned])
  let ignoreStart (body : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut result ← `(fun _ => $body)
    for _ in mutableScope do result ← `(fun _ => $result)
    return result
  let countType ← quantifyScope mutableScope (← `(Nat))
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let falseNormal ← ignoreStart
    (← curryScope afterScope (← `(fun (_ : Complexity.Language.Heap) => False)))
  let falseReturned ← ignoreStart (← `(fun _ =>
    $(← curryScope afterScope (← `(fun (_ : Complexity.Language.Heap) => False)))))
  let guardReturned ← curryScope mutableScope
    (← `(fun ($heap:ident : Complexity.Language.Heap) ($again:ident : Bool) =>
      $(← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
        $(app count afterValues) = $(app count beforeValues) ∧
        $finish:ident = $heap:ident ∧
        $(app invariant (afterValues.push ⟨finish.raw⟩)) ∧
        ($again:ident = true ↔ $(app count afterValues) < $limit:ident))))))
  let bodyPre ← curryScope mutableScope (← `(fun ($heap:ident : Complexity.Language.Heap) =>
    $(app invariant (beforeValues.push ⟨heap.raw⟩)) ∧
      $(app count beforeValues) < $limit:ident))
  let bodyNormal ← curryScope mutableScope (← `(fun ($heap:ident : Complexity.Language.Heap) =>
    $(← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app count afterValues) = $(app count beforeValues) + 1 ∧
      $(app invariant (afterValues.push ⟨finish.raw⟩)) ∧
      $frame:ident $heap:ident $finish:ident)))))
  let pre ← curryScope mutableScope (← `(fun ($heap:ident : Complexity.Language.Heap) =>
    $(app invariant (beforeValues.push ⟨heap.raw⟩)) ∧ $frame:ident $initial:ident $heap:ident))
  let finalNormal ← ignoreStart (← curryScope afterScope
    (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $normal:ident $finish:ident ∧ $frame:ident $initial:ident $finish:ident)))
  let exitType ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
    $(app invariant (beforeValues.push ⟨heap.raw⟩)) →
      $limit:ident ≤ $(app count beforeValues) → $normal:ident $heap:ident))
  let type ← quantifyScope capturedScope (← `(∀ ($count:ident : $countType)
    ($limit:ident : Nat) ($invariant:ident : $predicateType)
    ($frame:ident : Complexity.Language.Heap → Complexity.Language.Heap → Prop)
    ($frameTrans:ident : ∀ {a b c}, $frame:ident a b → $frame:ident b c → $frame:ident a c)
    ($normal:ident : Complexity.Language.Heap → Prop)
    ($guardSpec:ident : $(contract "guard_contract" ⟨invariant.raw⟩ falseNormal guardReturned))
    ($bodySpec:ident : $(contract "body_contract" bodyPre bodyNormal falseReturned))
    ($exit:ident : $exitType) ($initial:ident : Complexity.Language.Heap),
    $(contract "contract" pre finalNormal falseReturned)))
  let mutableType := loopMember site "Mutable"
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let rawCount ← `(fun ($before:ident : $mutableType:ident) => $(app count beforeFields))
  let rawInvariant ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) =>
      $(app invariant (beforeFields.push ⟨heap.raw⟩)))
  let rawExit ← `(fun ($before:ident : $mutableType:ident) => $(app exit beforeFields))
  let view := loopMember site "CaptureView"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let proof ← curryScope capturedScope (← `(fun $count:ident $limit:ident $invariant:ident
    $frame:ident $frameTrans:ident $normal:ident $guardSpec:ident $bodySpec:ident
    $exit:ident $initial:ident =>
      Complexity.Language.Stmt.observe_while_fixed_count_frame_contract
        $view:ident $program:ident $guard:ident $body:ident $guardFrame:ident $bodyFrame:ident
        $captures $rawCount $limit:ident $rawInvariant $frame:ident $frameTrans:ident
        $normal:ident $guardSpec:ident $bodySpec:ident $rawExit $initial:ident))
  return (← `(command|
    /-- Compose an increasing count and a transitive heap frame from the actual
    guard and body contracts. The guard preserves the count and heap; normal
    body steps increase the count by one. Array effects and the exit consequence
    remain supplied mathematical facts, without a runtime budget. -/
    theorem $name:ident : $type := $proof)).raw

/-- Expose a related mathematical loop state with named mutable arguments.
The generated frame theorems keep captured values out of the author's relation. -/
def loopRelatedContractDeclaration (program : TSyntax `ident) (site : BlockSite) :
    MacroM Syntax := do
  let name := loopMember site "rel_contract"
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutableType := loopMember site "Mutable"
  let captureView := loopMember site "CaptureView"
  let modelType ← freshProofName site.name `Model
  let model ← freshProofName site.name `model
  let next ← freshProofName site.name `next
  let stateRel ← freshProofName site.name `stateRel
  let invariant ← freshProofName site.name `invariant
  let relation ← freshProofName site.name `relation
  let wellFounded ← freshProofName site.name `wellFounded
  let ready ← freshProofName site.name `ready
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let guardSpec ← freshProofName site.name `guardSpec
  let bodySpec ← freshProofName site.name `bodySpec
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let again ← freshProofName site.name `again
  let valid ← freshProofName site.name `valid
  let observed ← freshProofName site.name `observed
  let captures ← scopeTuple capturedScope
  let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let beforeValues := mutableScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let afterValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let app (function : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨function.raw⟩ arguments
  let contract (suffix : String) (pre normal returned : TSyntax `term) :=
    app (loopMember site suffix) (capturedValues ++ #[pre, normal, returned])
  let ignoreStart (body : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut result ← `(fun _ => $body)
    for _ in mutableScope do result ← `(fun _ => $result)
    return result
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let readyType ← quantifyScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let result ← valueTypeTerm site.result
  let falseNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) => False)))
  let guardReturned ← curryScope mutableScope
    (← `(fun ($heap:ident : Complexity.Language.Heap) ($again:ident : Bool) =>
      $(← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
        if $again:ident then
          $(app ready (#[⟨model.raw⟩] ++ beforeValues ++ #[⟨heap.raw⟩] ++
            afterValues ++ #[⟨finish.raw⟩]))
        else $(app normal (afterValues.push ⟨finish.raw⟩)))))))
  let guardType ← `(∀ ($model:ident : $modelType:ident), $invariant:ident $model:ident →
    $(contract "guard_contract" (app stateRel #[⟨model.raw⟩]) falseNormal guardReturned))
  let bodyNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      ∃ ($next:ident : $modelType:ident), $invariant:ident $next:ident ∧
        $(app stateRel (#[⟨next.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩])) ∧
        $relation:ident $next:ident $model:ident)))
  let finalReturnedBody ← curryScope afterScope
    (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩]))))
  let finalReturned ← ignoreStart (← `(fun ($value:ident : $result) => $finalReturnedBody))
  let bodyType ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
    $invariant:ident $model:ident →
    $(app stateRel (#[⟨model.raw⟩] ++ beforeValues ++ #[⟨heap.raw⟩])) →
    $(contract "body_contract"
      (app ready (#[⟨model.raw⟩] ++ beforeValues ++ #[⟨heap.raw⟩])) bodyNormal finalReturned)))
  let bodyType ← `(∀ ($model:ident : $modelType:ident), $bodyType)
  let finalNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (afterValues.push ⟨finish.raw⟩)))))
  let conclusion := contract "contract" (app stateRel #[⟨model.raw⟩]) finalNormal finalReturned
  let type ← quantifyScope capturedScope (← `(∀ {$modelType:ident : Type}
    ($stateRel:ident : $modelType:ident → $predicateType)
    ($invariant:ident : $modelType:ident → Prop)
    {$relation:ident : $modelType:ident → $modelType:ident → Prop}
    ($wellFounded:ident : WellFounded $relation:ident)
    ($ready:ident : $modelType:ident → $readyType) ($normal:ident : $predicateType)
    ($returned:ident : $result → $predicateType)
    ($guardSpec:ident : $guardType) ($bodySpec:ident : $bodyType)
    ($model:ident : $modelType:ident) ($valid:ident : $invariant:ident $model:ident), $conclusion))
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let afterFields ← tupleFields mutableScope ⟨after.raw⟩
  let rawStateRel ← `(fun ($model:ident : $modelType:ident)
    ($before:ident : $mutableType:ident) ($heap:ident : Complexity.Language.Heap) =>
      $(app stateRel (#[⟨model.raw⟩] ++ beforeFields ++ #[⟨heap.raw⟩])))
  let rawReady ← `(fun ($model:ident : $modelType:ident)
    ($before:ident : $mutableType:ident) ($heap:ident : Complexity.Language.Heap)
    ($after:ident : $mutableType:ident) ($finish:ident : Complexity.Language.Heap) =>
      $(app ready (#[⟨model.raw⟩] ++ beforeFields ++ #[⟨heap.raw⟩] ++
        afterFields ++ #[⟨finish.raw⟩])))
  let rawNormal ← `(fun ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (afterFields.push ⟨finish.raw⟩)))
  let rawReturned ← `(fun ($value:ident : $result) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let rawBody ← `(fun ($model:ident : $modelType:ident)
    ($before:ident : $mutableType:ident) ($heap:ident : Complexity.Language.Heap)
    $valid:ident $observed:ident =>
      $(app bodySpec (#[⟨model.raw⟩] ++ beforeFields ++
        #[⟨heap.raw⟩, ⟨valid.raw⟩, ⟨observed.raw⟩])))
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let specification ← `(Complexity.Language.Stmt.observe_while_fixed_rel_contract
    $captureView:ident $program:ident $guard:ident $body:ident
    $guardFrame:ident $bodyFrame:ident $captures $rawStateRel $invariant:ident
    $wellFounded:ident $rawReady $rawNormal $rawReturned $guardSpec:ident $rawBody
    $model:ident $valid:ident)
  let proof ← curryScope capturedScope (← `(fun {$modelType:ident} $stateRel:ident
    $invariant:ident {$relation:ident} $wellFounded:ident $ready:ident $normal:ident
    $returned:ident $guardSpec:ident $bodySpec:ident $model:ident $valid:ident => $specification))
  return (← `(command|
    /-- Prove this actual loop using a related mathematical state and well-founded progress.
    Fixed captures are retained by the generated execution frames. -/
    theorem $name:ident : $type := $proof)).raw

private def loopVariantPost (site : BlockSite) (normal returned : TSyntax `ident)
    (fullScope : Bool) : MacroM (TSyntax `term) := do
  let finishScope ← freshMutableScope site "final_"
  let finishScope := if fullScope then finishScope else finishScope.filter (·.isMutable)
  let outcome ← freshProofName site.name `outcome
  let heap ← freshProofName site.name `heap
  let value ← freshProofName site.name `value
  let normalPost := mutableApplication finishScope normal ⟨heap.raw⟩
  let returnPost := mutableApplication finishScope returned ⟨heap.raw⟩ #[⟨value.raw⟩]
  let post ← `(match ($outcome:ident).1 with
    | .normal => $normalPost
    | .returned $value:ident => $returnPost
    | .fault _ => False)
  let post ← bindMutableFields finishScope (← `(($outcome:ident).2)) post
  `((fun $outcome:ident $heap:ident => ⟨$post⟩, ⟨⟩))

def loopTerminationDeclaration (program : TSyntax `ident) (site : BlockSite)
    (wellFoundedMode : Bool) :
    MacroM Syntax := do
  let name := loopMember site (if wellFoundedMode then "wellFounded_spec" else "variant_spec")
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutableType := loopMember site "Mutable"
  let captureView := loopMember site "CaptureView"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let invariant ← freshProofName site.name `invariant
  let progress ← freshProofName site.name (if wellFoundedMode then `relation else `variant)
  let wellFounded ← freshProofName site.name `wellFounded
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let step ← freshProofName site.name `step
  let mutable ← freshProofName site.name `mutable
  let heap ← freshProofName site.name `heap
  let initial ← freshProofName site.name `initial
  let captures ← scopeTuple capturedScope
  let initialMutable ← scopeTuple mutableScope
  let fields ← tupleFields mutableScope ⟨mutable.raw⟩
  let invApplication := Lean.Syntax.mkApp ⟨invariant.raw⟩ (fields.push ⟨heap.raw⟩)
  let rawInvariant ← `(fun ($mutable:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) => $invApplication)
  let rawProgress ← if wellFoundedMode then `($progress:ident) else do
    let application := Lean.Syntax.mkApp ⟨progress.raw⟩ (fields.push ⟨heap.raw⟩)
    `(fun ($mutable:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) => $application)
  let rawPost ← loopVariantPost site normal returned false
  let actualPost ← loopVariantPost site normal returned true
  let transportArgs ← namedSimpArgs #[captureView,
    loopMember site "regroup_apply", loopMember site "regroup_symm_apply",
    loopMember site "guard_observe", loopMember site "body_observe", loopMember site "observe"]
  let transportArgs := transportArgs ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.observe_reindex, ``Std.Do.Triple, ``Std.Do.WP.map])
  let wpArgs ← constantSimpArgs
    #[``Std.Do.WP.wp, ``Std.Do.PredTrans.pushArg, ``Part.TotalCorrectness.wp]
  let stepApplication := Lean.Syntax.mkApp ⟨step.raw⟩
    (fields ++ #[⟨heap.raw⟩, ⟨initial.raw⟩])
  let rawStep ← `(by
    intro $mutable:ident $heap:ident $initial:ident
    have checked := $stepApplication
    simp only [$transportArgs,*] at checked ⊢
    simp only [$wpArgs,*] at checked ⊢
    intro currentHeap sameHeap
    obtain ⟨⟨⟨guardControl, guardLocals⟩, guardHeap⟩, guardMember, guardPost⟩ :=
      checked currentHeap sameHeap
    refine ⟨((guardControl, guardLocals), guardHeap), guardMember, ?_⟩
    cases guardControl with
    | normal => exact guardPost
    | fault error => exact guardPost
    | returned again =>
        cases again with
        | false => exact guardPost
        | true =>
            intro currentHeap sameHeap
            obtain ⟨⟨⟨bodyControl, bodyLocals⟩, bodyHeap⟩, bodyMember, bodyPost⟩ :=
              guardPost currentHeap sameHeap
            refine ⟨((bodyControl, bodyLocals), bodyHeap), bodyMember, ?_⟩
            cases bodyControl <;> exact bodyPost)
  let invocation := scopeApplication site.scope site.name
  let finalType ← `(Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
    (ps := .arg Complexity.Language.Heap .pure) $invocation
    (fun $heap:ident => ⟨$(mutableApplication site.scope invariant ⟨heap.raw⟩)⟩) $actualPost)
  let stepType ← loopTerminationStepType site invariant progress normal returned wellFoundedMode
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let progressType ← if wellFoundedMode then
      `(($mutableType:ident × Complexity.Language.Heap) →
        ($mutableType:ident × Complexity.Language.Heap) → Prop)
    else quantifyScope mutableScope (← `(Complexity.Language.Heap → Nat))
  let result ← valueTypeTerm site.result
  let returnType ← `($result → $predicateType)
  let conclusion ← `(∀ ($normal:ident : $predicateType)
    ($returned:ident : $returnType) ($step:ident : $stepType),
      $(← quantifyScope mutableScope finalType))
  let conclusion ← if wellFoundedMode then
      `(∀ ($wellFounded:ident : WellFounded $progress:ident), $conclusion)
    else pure conclusion
  let type ← quantifyScope capturedScope (← `(∀ ($invariant:ident : $predicateType)
    ($progress:ident : $progressType), $conclusion))
  let specification ← if wellFoundedMode then
      `(Complexity.Language.Stmt.observe_while_fixed_spec
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $rawInvariant $rawProgress
        $wellFounded:ident $rawPost $rawStep $initialMutable)
    else
      `(Complexity.Language.Stmt.observe_while_fixed_variant_spec
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $rawInvariant $rawProgress $rawPost
        $rawStep $initialMutable)
  let proof ← curryScope mutableScope (← `(by
    have specification := $specification
    simp only [$transportArgs,*] at specification ⊢
    simp only [$wpArgs,*] at specification ⊢
    intro currentHeap initial
    obtain ⟨⟨⟨control, locals⟩, finalHeap⟩, member, post⟩ := specification currentHeap initial
    refine ⟨((control, locals), finalHeap), member, ?_⟩
    cases control <;> exact post))
  let proof ← `(fun $normal:ident $returned:ident $step:ident => $proof)
  let proof ← if wellFoundedMode then `(fun $wellFounded:ident => $proof) else pure proof
  let proof ← curryScope capturedScope (← `(fun $invariant:ident $progress:ident => $proof))
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Prove this actual loop with fixed captures and well-founded progress on its mutable locals.
    Only normal body exits must decrease; guard effects, returns and faults retain their real heap. -/
    theorem $name:ident : $type := $proof)).raw

end Core

end Complexity.Language.Syntax
