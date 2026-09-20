/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Basic
import Complexity.Language.Buffer.Copy.Native
import Complexity.Language.Buffer.RepresentedCopy
import Complexity.Language.List.Fold.Native
import Complexity.Language.List.Cons.Native
import Complexity.Language.List.Uncons.Native
import Complexity.Language.List.IsEmpty.Native

/-!
# Declarations for concrete represented operations

Emit source entries and checked mathematical interfaces for the selected linked
list fold, cons, uncons and emptiness operations. These declarations reuse the
existing operation implementations and their actual heap-indexed contracts.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

private def relationalFoldProofDeclarations (registration : FoldRegistration)
    (callbackRelation : Name) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let source := mkCIdent (callback.sourceFamily ++ `program)
  let fn := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "Id")
  let observe := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_observe")
  let native := mkCIdent callback.nativeName
  let same := name `callback_signature
  let evaluated := name `callback_eval
  let contract := name `callback_contract
  let fold := name `fold
  let program := name `program
  let foldId := name `foldId
  let accTy ← termOfExpr (coreTypeExpr callback.accumulator.coreTy)
  let accType ← termOfExpr callback.accumulator.nativeType
  let rawAccType ← actualTypeTerm callback.accumulator.coreTy
  let kind ← kindTerm callback.kind
  let headType ← termOfExpr (match callback.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let representation ← termOfExpr callback.accumulator.representation
  let represented ← `(($representation : Complexity.Language.Representation $accType $accTy))
  let initial := mkIdent `initial
  let actual := mkIdent `actual
  let head := mkIdent `head
  let heap := mkIdent `heap
  let accObserved := mkIdent `accObserved
  let mut callbackArgs : Array (TSyntax `term) := #[⟨initial.raw⟩, ⟨head.raw⟩]
  let mut callbackProof := #[]
  let mut roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let (actualAcc, accProof) ← match callback.accumulator with
    | .pure _ | .raw _ => do
        callbackProof := callbackProof.push (← `(tactic|
          change $initial:ident = $actual:ident at $accObserved:ident))
        callbackProof := callbackProof.push (← `(tactic| subst $actual:ident))
        pure ((⟨initial.raw⟩ : TSyntax `term), ← `(rfl))
    | _ => do
        callbackArgs := callbackArgs.push ⟨actual.raw⟩
        roots := roots.push (← `(bracketedBinder| ($actual:ident : $rawAccType)))
        observations := observations.push (← `(bracketedBinder|
          ($accObserved:ident : ($represented).Rel $initial:ident $actual:ident $heap:ident)))
        pure ((⟨actual.raw⟩ : TSyntax `term), (⟨accObserved.raw⟩ : TSyntax `term))
  callbackArgs := callbackArgs.push ⟨heap.raw⟩
  unless callback.accumulator.isIdentity do callbackArgs := callbackArgs.push ⟨accObserved.raw⟩
  let invocation := Lean.Syntax.mkApp ⟨(mkCIdent callbackRelation).raw⟩ callbackArgs
  callbackProof := callbackProof.push (← `(tactic|
    obtain ⟨value, finish, executed, related, _⟩ := $invocation))
  callbackProof := callbackProof.push (← `(tactic| refine ⟨value, finish, ?_, related⟩))
  callbackProof := callbackProof.push (← `(tactic|
    change ($source:ident).eval $fn:ident
      (Complexity.Language.Env.cons $actualAcc
        (Complexity.Language.Env.cons $head:ident Complexity.Language.Env.empty)) $heap:ident = _))
  callbackProof := callbackProof.push (← `(tactic| rw [$observe:ident]))
  callbackProof := callbackProof.push (← `(tactic| exact executed))
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    theorem $evaluated:ident ($initial:ident : $accType) ($actual:ident : $rawAccType)
        ($head:ident : $headType) ($heap:ident : Complexity.Language.Heap) (_ : True)
        ($accObserved:ident : ($represented).Rel $initial:ident $actual:ident $heap:ident) :
        ∃ value finish,
          Complexity.Language.List.Fold.calleeEval $source:ident $fn:ident $same:ident
            $actual:ident $head:ident $heap:ident = Part.some (.ok value, finish) ∧
          ($represented).Rel ($native:ident $initial:ident $head:ident) value finish := by
      $callbackProof:tactic*)).raw
  declarations := declarations.push (← `(command|
    theorem $contract:ident : Complexity.Language.List.Fold.Contract $source:ident $fn:ident $same:ident
        $represented $native:ident (fun _ _ => True) :=
      Complexity.Language.List.Fold.Contract.of_eval
        (source := $source:ident) (fn := $fn:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (R := $represented)
        (step := $native:ident) (domain := fun _ _ => True) $evaluated:ident)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.relation):ident ($initial:ident : $accType) (values : List $headType)
        $roots:bracketedBinder* (root : Option (Complexity.Language.NodeRef $kind))
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder*
        (observed : (Complexity.Language.Representation.list $kind).Rel values root $heap:ident) :
        ∃ value finish,
          $fold:ident $actualAcc root $heap:ident = Part.some (.ok value, finish) ∧
          ($represented).Rel (values.foldl $native:ident $initial:ident) value finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨value, finish, executed, related, _, preserved⟩ :=
        Complexity.Language.List.Fold.eval_exists
          (source := $source:ident) (fn := $fn:ident) (same := $same:ident)
          (accTy := $accTy) (kind := $kind) (R := $represented)
          (step := $native:ident) (domain := fun _ _ => True)
          $contract:ident $initial:ident values $actualAcc root $heap:ident
          (by intro processed head suffix equality; trivial) $accProof observed
      exact ⟨value, finish, executed, related, preserved⟩)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $foldId:ident (Complexity.Language.List.Fold.representation $represented $kind)
        (fun _ => True) (fun input => input.2.foldl $native:ident input.1) := by
      intro input _
      exact Complexity.Language.List.Fold.program_refines $contract:ident input
        (by intro processed head suffix equality; trivial))).raw
  return declarations

def foldDeclarations (registration : FoldRegistration) : TermElabM (Array Syntax) := do
  let callback := registration.callback
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let originalProgram := mkCIdent (callback.sourceFamily ++ `program)
  let originalSignatures := mkCIdent (callback.sourceFamily ++ `signatures)
  let originalId := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "Id")
  let originalObserve := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_observe")
  let originalPure := mkCIdent ((callback.sourceFamily ++ callback.sourceName).appendAfter "_action_eq_pure")
  let native := mkCIdent callback.nativeName
  let accTy ← termOfExpr (coreTypeExpr callback.accumulator.coreTy)
  let accType ← termOfExpr callback.accumulator.nativeType
  let rawAccType ← actualTypeTerm callback.accumulator.coreTy
  let kind ← kindTerm callback.kind
  let headType ← termOfExpr (match callback.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let same := name `callback_signature
  let callbackPure := name `callback_pure
  let callbackContract := name `callback_contract
  let foldId := name `foldId
  let fold := name `fold
  let observe := name `fold_observe
  let resultRepresentation ← termOfExpr operation.result.representation
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    theorem $same:ident : $originalSignatures:ident[$originalId:ident] =
        Complexity.Language.List.Fold.stepSignature $accTy $kind := rfl)).raw
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      Complexity.Language.List.Fold.foldSignature $accTy $kind :: $originalSignatures:ident)).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Fold.program $originalProgram:ident $originalId:ident $same:ident)).raw
  declarations := declarations.push (← `(command|
    abbrev $foldId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Fold.entry $accTy $kind $originalSignatures:ident)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $fold:ident (initial : $rawAccType)
        (root : Option (Complexity.Language.NodeRef $kind)) :
        ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part) $rawAccType :=
      Complexity.Language.List.Fold.foldEval $originalProgram:ident $originalId:ident $same:ident
        initial root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Fold.foldSignature $accTy $kind).params,
        ($program:ident).eval $foldId:ident args = $fold:ident args.head args.tail.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro initial
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  if let some relation := callback.relation then
    return declarations ++ (← relationalFoldProofDeclarations registration relation)
  let some equation := operationModel.equation | throwError "registered pure fold is missing its exact equation"
  declarations := declarations.push (← `(command|
    theorem $callbackPure:ident (initial : $accType) (head : $headType) (_ : True) :
        Complexity.Language.List.Fold.calleeEval $originalProgram:ident $originalId:ident
          $same:ident initial head = pure ($native:ident initial head) := by
      change ($originalProgram:ident).eval $originalId:ident
        (Complexity.Language.Env.cons initial
          (Complexity.Language.Env.cons head Complexity.Language.Env.empty)) = _
      rw [$originalObserve:ident]
      exact $originalPure:ident initial head)).raw
  declarations := declarations.push (← `(command|
    theorem $callbackContract:ident : Complexity.Language.List.Fold.Contract
        $originalProgram:ident $originalId:ident $same:ident
        (Complexity.Language.Representation.ofEmbedding (Function.Embedding.refl $accType))
        $native:ident (fun _ _ => True) :=
      Complexity.Language.List.Fold.Contract.of_pure_eval
        (source := $originalProgram:ident) (fn := $originalId:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (step := $native:ident) (domain := fun _ _ => True)
        (Function.Embedding.refl $accType) $callbackPure:ident)).raw
  declarations := declarations.push (← `(command|
    theorem $equation:ident (initial : $accType) (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        $fold:ident initial root heap = Part.some (.ok (values.foldl $native:ident initial), heap) := by
      exact Complexity.Language.List.Fold.eval_eq_pure_of_contents
        (source := $originalProgram:ident) (fn := $originalId:ident) (same := $same:ident)
        (accTy := $accTy) (kind := $kind) (step := $native:ident) (domain := fun _ _ => True)
        (Function.Embedding.refl $accType) $callbackPure:ident initial values root heap
        (by intro processed head suffix equality; trivial) observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.relation):ident (initial : $accType) (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $fold:ident initial root heap = Part.some (.ok returned, finish) ∧
          ($resultRepresentation : Complexity.Language.Representation $accType $accTy).Rel
            (values.foldl $native:ident initial) returned finish ∧
          heap.ShapeExtends finish := by
      exact ⟨_, heap, $equation:ident initial values root heap observed, rfl,
        Complexity.Language.Heap.ShapeExtends.refl heap⟩)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $foldId:ident
        (Complexity.Language.List.Fold.representation
          (Complexity.Language.Representation.ofEmbedding (Function.Embedding.refl $accType)) $kind)
        (fun _ => True) (fun input => input.2.foldl $native:ident input.1) := by
      intro input _
      exact Complexity.Language.List.Fold.program_refines $callbackContract:ident input
        (by intro processed head suffix equality; trivial))).raw
  return declarations

def consDeclarations (registration : ConsRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let consId := name `consId
  let cons := name `cons
  let observe := name `cons_observe
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.Cons.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Cons.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $consId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Cons.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $cons:ident (head : $headType)
        (tail : Option (Complexity.Language.NodeRef $kind)) :
        ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part)
          (Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.Cons.consEval $kind head tail)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Cons.signature $kind).params,
        ($program:ident).eval $consId:ident args = $cons:ident args.head args.tail.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro head
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro tail
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.relation):ident (head : $headType) (values : List $headType)
        (tail : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values tail heap) :
        ∃ returned finish,
          $cons:ident head tail heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.Representation.list $kind).Rel (head :: values) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Cons.eval_exists $kind head values tail heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $consId:ident (Complexity.Language.List.Cons.representation $kind)
        (fun _ => True) (fun input => input.1 :: input.2) :=
      Complexity.Language.List.Cons.refines $kind)).raw
  return declarations

def unconsDeclarations (registration : UnconsRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let unconsId := name `unconsId
  let uncons := name `uncons
  let observe := name `uncons_observe
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.Uncons.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.Uncons.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $unconsId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.Uncons.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $uncons:ident (root : Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.Uncons.unconsEval $kind root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.Uncons.signature $kind).params,
        ($program:ident).eval $unconsId:ident args = $uncons:ident args.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $uncons:ident root heap = Part.some (.ok returned, finish) ∧
          (Complexity.Language.List.Uncons.resultRepresentation $kind).Rel
            (values.head?.map (fun head => (head, values.tail))) returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.Uncons.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $unconsId:ident (Complexity.Language.List.Uncons.representation $kind)
        (fun _ => True) (fun values => values.head?.map (fun head => (head, values.tail))) :=
      Complexity.Language.List.Uncons.refines $kind)).raw
  return declarations

def isEmptyDeclarations (registration : IsEmptyRegistration) : TermElabM (Array Syntax) := do
  let operation := registration.operation
  let operationModel ← operation.requireModel
  let name (suffix : Name) := mkIdentFrom operation.family (operation.family.getId ++ suffix)
  let kind ← kindTerm registration.kind
  let headType ← termOfExpr (match registration.kind with
    | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  let signatures := name `signatures
  let program := name `program
  let isEmptyId := name `isEmptyId
  let isEmpty := name `isEmpty
  let observe := name `isEmpty_observe
  let some equation := operationModel.equation
    | throwError "registered emptiness test is missing its unchanged-heap equation"
  let mut declarations := #[]
  declarations := declarations.push (← `(command|
    abbrev $signatures:ident : List Complexity.Language.Signature :=
      [Complexity.Language.List.IsEmpty.signature $kind])).raw
  declarations := declarations.push (← `(command|
    def $program:ident : Complexity.Language.Program $signatures:ident :=
      Complexity.Language.List.IsEmpty.program $kind)).raw
  declarations := declarations.push (← `(command|
    abbrev $isEmptyId:ident : Fin ($signatures:ident).length :=
      Complexity.Language.List.IsEmpty.entry $kind)).raw
  declarations := declarations.push (← `(command|
    noncomputable def $isEmpty:ident (root : Option (Complexity.Language.NodeRef $kind)) :=
      Complexity.Language.List.IsEmpty.isEmptyEval $kind root)).raw
  declarations := declarations.push (← `(command|
    theorem $observe:ident : ∀ args : Complexity.Language.Env
        (Complexity.Language.List.IsEmpty.signature $kind).params,
        ($program:ident).eval $isEmptyId:ident args = $isEmpty:ident args.head := by
      refine (Complexity.Language.Env.forall_cons _).mpr ?_
      intro root
      refine (Complexity.Language.Env.forall_nil _).mpr ?_
      rfl)).raw
  declarations := declarations.push (← `(command|
    theorem $equation:ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        $isEmpty:ident root heap = Part.some (.ok values.isEmpty, heap) := by
      obtain ⟨returned, finish, evaluated, related, unchanged⟩ :=
        Complexity.Language.List.IsEmpty.eval_exists_heap_eq $kind values root heap observed
      change values.isEmpty = returned at related
      rw [← related, unchanged] at evaluated
      exact evaluated)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.relation):ident (values : List $headType)
        (root : Option (Complexity.Language.NodeRef $kind)) (heap : Complexity.Language.Heap)
        (observed : (Complexity.Language.Representation.list $kind).Rel values root heap) :
        ∃ returned finish,
          $isEmpty:ident root heap = Part.some (.ok returned, finish) ∧
          Complexity.Language.Representation.bool.Rel values.isEmpty returned finish ∧
          heap.ShapeExtends finish := by
      exact Complexity.Language.List.IsEmpty.eval_exists $kind values root heap observed)).raw
  declarations := declarations.push (← `(command|
    theorem $(operationModel.refinement):ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $isEmptyId:ident (Complexity.Language.List.IsEmpty.representation $kind)
        (fun _ => True) (fun values => values.isEmpty) :=
      Complexity.Language.List.IsEmpty.refines $kind)).raw
  return declarations

end Internal

end Complexity.Language.Syntax.Represented
