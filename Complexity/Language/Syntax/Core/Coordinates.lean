/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Expression
import Complexity.Language.Eval.Locals.Captures
import Complexity.Language.Eval.Locals.LocalReturn
import Complexity.Language.Eval.Locals.Effects

/-!
# Generated block coordinates and capture frames

Constructs declarations for actual block code, complete lexical observations, mutable/captured
coordinate equivalences and execution-based capture frames. The emitter controls when these
checked declarations are installed. These builders do not alter the underlying source blocks.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def loopCodeDeclarations (signatures : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let locals := loopMember site "Locals"
  let view := loopMember site "View"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let code := loopMember site "Code"
  let types ← scopeTypes site.scope
  let result ← typeTerm site.result
  let localsType ← scopeValueTypes site.scope
  let viewTerm ← scopeView site.scope
  let viewApply := loopMember site "view_apply"
  let viewSymmApply := loopMember site "view_symm_apply"
  let entry ← freshProofName site.name `entry
  let values ← freshProofName site.name `values
  let fields ← tupleFields site.scope ⟨values.raw⟩
  let mut projected ← `(())
  let mut restored ← `(Complexity.Language.Env.empty)
  for (binding, index) in site.scope.zipIdx.reverse do
    let sourceVar ← variableTerm index
    projected ← `((Complexity.Language.Env.get $entry:ident $sourceVar, $projected))
    let type ← typeTerm binding.type
    restored ← `(Complexity.Language.Env.cons (τ := $type) $(fields[index]!) $restored)
  let mut declarations := #[
    (← `(command| /-- Complete lexical coordinates for this source block. -/
      abbrev $locals:ident := $localsType)).raw,
    (← `(command| /-- Lossless proof coordinates, including fixed and shadowed captures. -/
      def $view:ident : Complexity.Language.Env $types ≃ $locals:ident := $viewTerm)).raw,
    (← `(command| /-- Observe lexical coordinates without unfolding the equivalence structure. -/
      theorem $viewApply:ident ($entry:ident : Complexity.Language.Env $types) :
          $view:ident $entry:ident = $projected := rfl)).raw,
    (← `(command| /-- Restore complete lexical coordinates without unfolding proof fields. -/
      theorem $viewSymmApply:ident ($values:ident : $locals:ident) :
          ($view:ident).symm $values:ident = $restored := by
        apply ($view:ident).injective
        simp only [Equiv.apply_symm_apply, $viewApply:ident,
          Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there] <;>
          (symm; exact $(← tupleExtProof site.scope)))).raw]
  if let some guardTerm := site.guard then
    declarations := declarations.push (← `(command|
      /-- The actual value-producing guard, reevaluated on every iteration. -/
      def $guard:ident : Complexity.Language.Stmt $signatures:ident $types .bool := $guardTerm)).raw
  declarations := declarations.push (← `(command|
    /-- The actual parsed lexical body, with its enclosing return type. -/
    def $body:ident : Complexity.Language.Stmt $signatures:ident $types $result := $(site.body))).raw
  let codeTerm ← match site.guard with
    | some _ => `(Complexity.Language.Stmt.while $guard:ident $body:ident)
    | none => `(Complexity.Language.Stmt.scope $body:ident)
  declarations := declarations.push (← `(command|
    /-- This actual source block, retaining its loop or allocation-scope semantics. -/
    def $code:ident : Complexity.Language.Stmt $signatures:ident $types $result := $codeTerm)).raw
  return declarations

def loopObservationDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let localsType := loopMember site "Locals"
  let view := loopMember site "View"
  let tuple ← scopeTuple site.scope
  let mut declarations := #[]
  let observations := (if site.guard.isSome then [("guard", "Guard", Ty.bool)] else []) ++
    [("body", "Body", site.result), ("", "Code", site.result)]
  for (suffix, codeSuffix, result) in observations do
    let name := if suffix.isEmpty then site.name else loopMember site suffix
    let code := loopMember site codeSuffix
    let result ← typeTerm result
    let type ← quantifyScope site.scope
      (← `(StateT Complexity.Language.Heap Part
        (Complexity.Language.Control $result × $localsType:ident)))
    let value ← curryScope site.scope
      (← `(Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident $tuple))
    declarations := declarations.push (← `(command|
      /-- The actual source block observed with ordinary named local inputs. -/
      noncomputable def $name:ident : $type := $value)).raw
    let foldName := loopMember site (if suffix.isEmpty then "observe" else suffix ++ "_observe")
    let current ← freshProofName site.name `locals
    let applied ← tupleApplication site.scope name ⟨current.raw⟩
    declarations := declarations.push (← `(command|
      /-- Coordinate conversion for composing this named observation. -/
      theorem $foldName:ident ($current:ident : $localsType:ident) :
          Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident $current:ident =
            $applied := rfl)).raw
  return declarations

def loopCaptureDeclarations (site : BlockSite) : MacroM (Array Syntax) := do
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutableType ← scopeValueTypes mutableScope
  let capturedType ← scopeValueTypes capturedScope
  let locals := loopMember site "Locals"
  let mutable := loopMember site "Mutable"
  let captured := loopMember site "Captured"
  let regroup := loopMember site "Regroup"
  let regroupApply := loopMember site "regroup_apply"
  let regroupSymmApply := loopMember site "regroup_symm_apply"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let captureViewApply := loopMember site "captureView_apply"
  let captureViewSymmApply := loopMember site "captureView_symm_apply"
  let types ← scopeTypes site.scope
  let values ← freshProofName site.name `values
  let grouped ← freshProofName site.name `grouped
  let entry ← freshProofName site.name `entry
  let fields ← tupleFields site.scope ⟨values.raw⟩
  let (mutableFields, capturedFields) := splitScopeFields site.scope fields
  let regrouped ← `(( $(← fieldsTuple mutableFields), $(← fieldsTuple capturedFields) ))
  let mutableValues ← tupleFields mutableScope (← `(($grouped:ident).1))
  let capturedValues ← tupleFields capturedScope (← `(($grouped:ident).2))
  let restored ← fieldsTuple (mergeScopeFields site.scope mutableValues capturedValues)
  let leftProof ← tupleExtProof site.scope
  let rightProof ← `(Prod.ext $(← tupleExtProof mutableScope) $(← tupleExtProof capturedScope))
  let mut entryFields := #[]
  for (_, index) in site.scope.zipIdx do
    entryFields := entryFields.push
      (← `(Complexity.Language.Env.get $entry:ident $(← variableTerm index)))
  let (mutableEntries, capturedEntries) := splitScopeFields site.scope entryFields
  let projected ← `(( $(← fieldsTuple mutableEntries), $(← fieldsTuple capturedEntries) ))
  return #[
    (← `(command| /-- The ordinary mutable locals of this source loop. -/
      abbrev $mutable:ident := $mutableType)).raw,
    (← `(command| /-- Fixed lexical captures, independent of the shared heap. -/
      abbrev $captured:ident := $capturedType)).raw,
    (← `(command| /-- A lossless coordinate permutation; no source operation is executed. -/
      def $regroup:ident : $locals:ident ≃ ($mutable:ident × $captured:ident) where
        toFun $values:ident := $regrouped
        invFun $grouped:ident := $restored
        left_inv _ := $leftProof
        right_inv _ := $rightProof)).raw,
    (← `(command| theorem $regroupApply:ident ($values:ident : $locals:ident) :
      $regroup:ident $values:ident = $regrouped := rfl)).raw,
    (← `(command| theorem $regroupSymmApply:ident
        ($grouped:ident : $mutable:ident × $captured:ident) :
      ($regroup:ident).symm $grouped:ident = $restored := rfl)).raw,
    (← `(command| /-- The same complete environment, grouped by source mutability. -/
      def $captureView:ident : Complexity.Language.Env $types ≃
          ($mutable:ident × $captured:ident) := ($view:ident).trans $regroup:ident)).raw,
    (← `(command| theorem $captureViewApply:ident ($entry:ident : Complexity.Language.Env $types) :
      $captureView:ident $entry:ident = $projected := rfl)).raw,
    (← `(command| /-- Restore grouped locals using the checked coordinate projection laws. -/
      theorem $captureViewSymmApply:ident ($grouped:ident : $mutable:ident × $captured:ident) :
          ($captureView:ident).symm $grouped:ident = ($view:ident).symm $restored := by
        simp only [$captureView:ident, Equiv.symm_trans_apply, $regroupSymmApply:ident])).raw]

def hasNativeCoordinates (site : BlockSite) : Bool :=
  site.nativeResult.isSome || site.scope.any (·.native.isSome)

def loopNativeCaptureDeclarations (site : BlockSite) : MacroM (Array Syntax) := do
  unless hasNativeCoordinates site do return #[]
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutable := loopMember site "NativeMutable"
  let captured := loopMember site "NativeCaptured"
  let view := loopMember site "NativeCaptureView"
  let viewApply := loopMember site "native_captureView_apply"
  let symmApply := loopMember site "native_captureView_symm_apply"
  let rawView := loopMember site "CaptureView"
  let rawViewApply := loopMember site "captureView_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let viewSymm := loopMember site "view_symm_apply"
  let types ← scopeTypes site.scope
  let coordinate ← `(Equiv.prodCongr $(← scopeNativeEquiv mutableScope)
    $(← scopeNativeEquiv capturedScope))
  let entry ← freshProofName site.name `entry
  let mut entryFields := #[]
  for (binding, index) in site.scope.zipIdx do
    let field ← `(Complexity.Language.Env.get $entry:ident $(← variableTerm index))
    entryFields := entryFields.push (← decodeNativeField binding field)
  let (mutableEntries, capturedEntries) := splitScopeFields site.scope entryFields
  let projected ← `(($(← fieldsTuple mutableEntries), $(← fieldsTuple capturedEntries)))
  let grouped ← freshProofName site.name `grouped
  let fields := mergeScopeFields site.scope
    (← tupleFields mutableScope (← `(($grouped:ident).1)))
    (← tupleFields capturedScope (← `(($grouped:ident).2)))
  let encoded ← encodeNativeFields site.scope fields
  let mut restored ← `(Complexity.Language.Env.empty)
  for (binding, field) in (site.scope.toArray.zip encoded).reverse do
    restored ← `(Complexity.Language.Env.cons (τ := $(← typeTerm binding.type)) $field $restored)
  return #[
    (← `(command| /-- Mutable loop coordinates in their registered native types. -/
      abbrev $mutable:ident := $(← scopeNativeTypes mutableScope))).raw,
    (← `(command| /-- Immutable captures in their registered native types. -/
      abbrev $captured:ident := $(← scopeNativeTypes capturedScope))).raw,
    (← `(command| /-- A native view of the same environment, with no runtime conversion. -/
      def $view:ident : Complexity.Language.Env $types ≃ ($mutable:ident × $captured:ident) :=
        ($rawView:ident).trans ($coordinate).symm)).raw,
    (← `(command| /-- Observe native loop coordinates without unfolding registered equivalences. -/
      theorem $viewApply:ident ($entry:ident : Complexity.Language.Env $types) :
          $view:ident $entry:ident = $projected := by
        simp only [$view:ident, Equiv.trans_apply, Equiv.prodCongr_symm,
          Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Prod.map,
          $rawViewApply:ident])).raw,
    (← `(command| /-- Restore native loop coordinates without unfolding equivalence proofs. -/
      theorem $symmApply:ident ($grouped:ident : $mutable:ident × $captured:ident) :
          ($view:ident).symm $grouped:ident = $restored := by
        simp only [$view:ident, $rawView:ident, Equiv.symm_trans_apply, Equiv.symm_symm,
          Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map, $regroupSymm:ident,
          $viewSymm:ident])).raw]

def loopCaptureFrameDeclarations (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM (Array Syntax) := do
  let types ← scopeTypes site.scope
  let captureView := loopMember site "CaptureView"
  let captureViewApply := loopMember site "captureView_apply"
  let preservedArgs ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let preservedArgs := preservedArgs ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.PreservesLocal, ``Complexity.Language.Var.index,
      ``Complexity.Language.Stmt.LocalReturn.store, ``Complexity.Language.Stmt.LocalReturn.resume,
      ``Complexity.Language.Stmt.LocalReturn.guard])
  let entry ← freshProofName site.name `entry
  let finish ← freshProofName site.name `finish
  let control ← freshProofName site.name `control
  let execution ← freshProofName site.name `execution
  let mut capturesProof ← `(rfl)
  for (binding, index) in site.scope.zipIdx.reverse do
    unless binding.isMutable do
      let sourceVar ← variableTerm index
      capturesProof ← `(Prod.ext
        (Complexity.Language.Exec.get_eq $execution:ident $sourceVar
          (by simp [$preservedArgs,*])) $capturesProof)
  let mut declarations := #[]
  for (suffix, codeSuffix, result) in
      [("guard_preservesCaptures", "Guard", Ty.bool),
       ("body_preservesCaptures", "Body", site.result),
       ("preservesCaptures", "Code", site.result)] do
    let name := loopMember site suffix
    let code := loopMember site codeSuffix
    let result ← typeTerm result
    declarations := declarations.push (← `(command|
      /-- Source lexical immutability preserves these captures on every actual exit. -/
      theorem $name:ident {$entry:ident $finish:ident : Complexity.Language.State $types}
          {$control:ident : Complexity.Language.Control $result}
          ($execution:ident : Complexity.Language.Exec $program:ident $code:ident
            $entry:ident $finish:ident $control:ident) :
          ($captureView:ident ($finish:ident).locals).2 =
            ($captureView:ident ($entry:ident).locals).2 := by
        simp only [$captureViewApply:ident]
        exact $capturesProof)).raw
    if hasNativeCoordinates site then
      let nativeName := loopMember site ("native_" ++ suffix)
      let nativeView := loopMember site "NativeCaptureView"
      let capturedEquiv ← scopeNativeEquiv (site.scope.filter (! ·.isMutable))
      declarations := declarations.push (← `(command|
        /-- The same actual exit preserves its native immutable captures. -/
        theorem $nativeName:ident {$entry:ident $finish:ident : Complexity.Language.State $types}
            {$control:ident : Complexity.Language.Control $result}
            ($execution:ident : Complexity.Language.Exec $program:ident $code:ident
              $entry:ident $finish:ident $control:ident) :
            ($nativeView:ident ($finish:ident).locals).2 =
              ($nativeView:ident ($entry:ident).locals).2 :=
          congrArg (fun captures => ($capturedEquiv).symm captures) ($name:ident $execution:ident))).raw
  return declarations

end Core

end Complexity.Language.Syntax
