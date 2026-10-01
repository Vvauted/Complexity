/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Basic
import Complexity.Language.Syntax.Represented.ArrayReplication
import Complexity.Language.Buffer.GetD
import Complexity.Language.Buffer.Ragged.GetD
import Complexity.Language.Buffer.Prod.Replicate
import Complexity.Language.Eval.Simp

/-!
# Composite array operations and observations

Assemble a concrete source function from existing scalar and ragged column
reads. Products and checked record field views only describe how these actual
reads are combined. Generated theorems retain the unchanged heap and observe
the original Lean element, including the entire supplied out-of-bounds default.
The generated source body, including every column call, is compiled normally;
the representation is not an executable or uncharged mathematical decoder.

Scalar-record replication instead reuses an existing initialized allocator
directly, transporting its result and preservation contracts through the same
checked field view without generating another source body.
-/

namespace Complexity.Language.Syntax.Represented.Internal

open Lean Meta Elab Term Command
open Lean.Parser.Term

private structure ReadPlan where
  body : Array (TSyntax `doElem) := #[]
  proof : Array (TSyntax `tactic) := #[]
  equations : Array (TSyntax `ident) := #[]
  sourceValue : TSyntax `term
  returned : TSyntax `term
  related : TSyntax `term
  splitValues : Array (TSyntax `term) := #[]

private def relationTerm (type : NativeType) (value actual heap : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let representation ← termOfExpr type.representation
  let native ← termOfExpr type.nativeType
  let core ← termOfExpr (coreTypeExpr type.coreTy)
  `(($representation : Complexity.Language.Representation $native $core).Rel $value $actual $heap)

/-- Only the resolver's column and record views are unfolded here. An arbitrary
injective view alone would not justify an executable element reader. -/
private partial def readPlan (array result : NativeType) (path : String)
    (rows index fallback storage defaultView heap observed defaultObserved : TSyntax `term) :
    TermElabM ReadPlan := do
  let selected ← `(($rows).getD $index $fallback)
  let checked (returned proof : TSyntax `term) : TermElabM (TSyntax `term) := do
    let relation ← relationTerm result selected returned heap
    `(show $relation from by simpa only [Array.getD_map] using $proof)
  let pair (left right : NativeType) : TermElabM ReadPlan := do
    let (leftResult, rightResult) ← match result with
      | .prod left right => pure (left, right)
      | .pure _ => do
          let args := result.nativeType.getAppArgs
          pure (← resolveNativeType args[0]!, ← resolveNativeType args[1]!)
      | _ => throwError "array column result must retain its product layout"
    let first ← readPlan left leftResult (path ++ "L")
      (← `(($rows).map Prod.fst)) index (← `(($fallback).1))
      (← `(($storage).1)) (← `(($defaultView).1)) heap
      (← `(And.left $observed))
      (← if result.isIdentity then `(congrArg Prod.fst $defaultObserved)
        else `(And.left $defaultObserved))
    let second ← readPlan right rightResult (path ++ "R")
      (← `(($rows).map Prod.snd)) index (← `(($fallback).2))
      (← `(($storage).2)) (← `(($defaultView).2)) heap
      (← `(And.right $observed))
      (← if result.isIdentity then `(congrArg Prod.snd $defaultObserved)
        else `(And.right $defaultObserved))
    let returned ← `(($(first.returned), $(second.returned)))
    let related ← if result.isIdentity then `(congrArg₂ Prod.mk $(first.related) $(second.related))
      else `(And.intro $(first.related) $(second.related))
    return {
      body := first.body ++ second.body
      proof := first.proof ++ second.proof
      equations := first.equations ++ second.equations
      sourceValue := ← `(($(first.sourceValue), $(second.sourceValue)))
      returned, related := ← checked returned related
      splitValues := first.splitValues ++ second.splitValues }
  match array with
  | .arrayView element columns _ =>
      match element with
      | .scalar _ embedding => do
          let view ← termOfExpr embedding
          let layout ← resolveType (← `(Nat))
          let inner ← readPlan columns layout path (← `(($rows).map $view)) index
            (← `($view $fallback)) storage defaultView heap observed defaultObserved
          return { inner with related := ← checked inner.returned inner.related }
      | .int => do
          let view := mkCIdent ``Representation.intEquiv
          let layout ← resolveType (← `(Bool × Nat))
          let inner ← readPlan columns layout path (← `(($rows).map $view:ident)) index
            (← `($view:ident $fallback)) storage defaultView heap observed defaultObserved
          return { inner with related := ← checked inner.returned inner.related }
      | .option payload => do
          let (initialDefault, rawDefault) ← payload.optionColumnDefault
          let packed := mkIdent (Name.mkSimple ("packedDefault" ++ path))
          let unpacked := mkIdent (Name.mkSimple ("unpacked" ++ path))
          let fields := NativeType.prod (← resolveType (← `(Bool))) payload
          let rawFields ← rawTypeTerm fields.coreTy
          let rawResult ← rawTypeTerm result.coreTy
          let rep ← `(($(← termOfExpr payload.representation) :
            Complexity.Language.Representation $(← termOfExpr payload.nativeType)
              $(← termOfExpr (coreTypeExpr payload.coreTy))))
          let view ← `(Complexity.Language.Representation.optionEmbedding $initialDefault)
          let inner ← readPlan columns fields path (← `(($rows).map $view)) index
            (← `($view $fallback)) storage ⟨packed.raw⟩ heap observed
            (← `(Complexity.Language.Representation.optionEmbedding_rel
              (payload := $rep) (default := $initialDefault) (rawDefault := $rawDefault)
              (value := $fallback) (actual := $defaultView) (heap := $heap)
              (by rfl) $defaultObserved))
          let returned ← `(Complexity.Language.Representation.optionUnpack $(inner.returned))
          let relation ← relationTerm result selected returned heap
          return { inner with
            body := #[← `(doElem| let mut $packed:ident : $rawFields := (false, $rawDefault)),
              ← `(doElem| match $defaultView:term with
                | none => $packed:ident := (false, $rawDefault)
                | some payload => $packed:ident := (true, payload))] ++ inner.body ++
              #[← `(doElem| let mut $unpacked:ident : $rawResult := none),
                ← `(doElem| if ($(inner.sourceValue)).1 then
                  $unpacked:ident := some ($(inner.sourceValue)).2
                else
                  $unpacked:ident := none)]
            proof := #[← `(tactic| let $packed:ident :=
              Complexity.Language.Representation.optionEmbedding $rawDefault $defaultView)] ++ inner.proof
            equations := inner.equations.push packed
            sourceValue := ⟨unpacked.raw⟩, returned
            related := ← `(show $relation from
              Complexity.Language.Representation.optionUnpack_rel
                (payload := $rep) (default := $initialDefault) (value := $selected)
                (by simpa only [Array.getD_map] using $(inner.related)))
            splitValues := inner.splitValues.push defaultView }
      | .record _ layout embedding => do
          let view ← termOfExpr embedding
          let inner ← readPlan columns layout path (← `(($rows).map $view)) index
            (← `($view $fallback)) storage defaultView heap observed defaultObserved
          return { inner with related := ← checked inner.returned inner.related }
      | _ =>
          let .prod left right := columns
            | throwError "unsupported composite array storage"
          pair left right
  | .arrayProd left right => pair (.array left) (.array right)
  | .array kind | .raggedArray (.array kind) => do
      let ragged := match array with | .raggedArray _ => true | _ => false
      let family := if ragged then `Complexity.Language.Buffer.Ragged.GetD
        else `Complexity.Language.Buffer.GetD
      let fn := family ++ (match kind with | .nat => `getNat | .bool => `getBool)
      let call := mkCIdent fn
      let sourceCall := mkIdent fn
      let evaluated := mkCIdent (fn.appendAfter "_eval")
      let column := mkIdent (Name.mkSimple ("column" ++ path))
      let defaultColumn := mkIdent (Name.mkSimple ("default" ++ path))
      let sourceValue := mkIdent (Name.mkSimple ("value" ++ path))
      let returned := mkIdent (Name.mkSimple ("returned" ++ path))
      let execution := mkIdent (Name.mkSimple ("execution" ++ path))
      let observation := mkIdent (Name.mkSimple ("observed" ++ path))
      let body ← #[
        `(doElem| let $column:ident := $storage),
        `(doElem| let $defaultColumn:ident := $defaultView),
        `(doElem| let $sourceValue:ident ← $sourceCall:ident $column:ident $index $defaultColumn:ident)].mapM id
      if ragged then
        return {
          body := body
          proof := #[← `(tactic|
            obtain ⟨$returned:ident, $execution:ident, $observation:ident⟩ :=
              $evaluated:ident $rows $index $fallback $storage $defaultView $heap
                $observed $defaultObserved)]
          equations := #[execution]
          sourceValue := ⟨sourceValue.raw⟩, returned := ⟨returned.raw⟩
          related := ← checked ⟨returned.raw⟩ ⟨observation.raw⟩ }
      else
        let same := mkIdent (Name.mkSimple ("defaultEq" ++ path))
        let scalarRelation ← relationTerm result selected selected heap
        return {
          body := body
          proof := #[
            ← `(tactic| have $same:ident : $fallback = $defaultView := $defaultObserved),
            ← `(tactic| have $execution:ident :
                $call:ident $storage $index $defaultView $heap =
                  Part.some (.ok $selected, $heap) := by
              rw [← $same:ident]
              exact $evaluated:ident $rows $index $fallback $storage $heap $observed)]
          equations := #[execution], sourceValue := ⟨sourceValue.raw⟩
          returned := selected, related := ← `(show $scalarRelation from rfl) }
  | .raggedArray payload => do
      let pairRows (left right : NativeType) : TermElabM ReadPlan := do
        let first ← readPlan (.raggedArray left) left (path ++ "L")
          (← `(($rows).map (Array.map Prod.fst))) index (← `(($fallback).map Prod.fst))
          (← `((($storage).1, ($storage).2.1))) (← `(($defaultView).1)) heap
          (← `(Complexity.Language.Representation.raggedArrayOf_fst $observed))
          (← `(And.left $defaultObserved))
        let second ← readPlan (.raggedArray right) right (path ++ "R")
          (← `(($rows).map (Array.map Prod.snd))) index (← `(($fallback).map Prod.snd))
          (← `((($storage).1, ($storage).2.2))) (← `(($defaultView).2)) heap
          (← `(Complexity.Language.Representation.raggedArrayOf_snd $observed))
          (← `(And.right $defaultObserved))
        let returned ← `(($(first.returned), $(second.returned)))
        return {
          body := first.body ++ second.body
          proof := first.proof ++ second.proof
          equations := first.equations ++ second.equations
          sourceValue := ← `(($(first.sourceValue), $(second.sourceValue)))
          returned, related := ← checked returned
            (← `(And.intro $(first.related) $(second.related))) }
      match payload with
      | .arrayProd left right => pairRows (.array left) (.array right)
      | .arrayView element columns _ =>
          match element with
          | .int => do
              let view := mkCIdent ``Representation.intEquiv
              let columnRep ← termOfExpr columns.representation
              let inner ← readPlan (.raggedArray columns) columns path
                (← `(($rows).map (Array.map $view:ident))) index
                (← `(($fallback).map $view:ident)) storage defaultView heap
                (← `(Complexity.Language.Representation.raggedArrayOf_map
                  $columnRep (Equiv.toEmbedding $view:ident) $observed)) defaultObserved
              return { inner with related := ← checked inner.returned inner.related }
          | .record _ _ embedding | .scalar _ embedding => do
              let view ← termOfExpr embedding
              let columnRep ← termOfExpr columns.representation
              let inner ← readPlan (.raggedArray columns) columns path
                (← `(($rows).map (Array.map $view))) index (← `(($fallback).map $view))
                storage defaultView heap
                (← `(Complexity.Language.Representation.raggedArrayOf_map
                  $columnRep $view $observed)) defaultObserved
              return { inner with related := ← checked inner.returned inner.related }
          | _ =>
              let .prod left right := columns
                | throwError "unsupported row payload columns"
              pairRows left right
      | _ => throwError "row payloads require supported scalar array columns"
  | _ => throwError "this array layout has no executable defaulted element reader"

/-- Emit an actual source reader and checked mathematical/frame contracts. -/
def arrayReadDeclarations (registration : ArrayReadRegistration) :
    TermElabM (Array Syntax) := do
  let array := registration.array
  let result := registration.operation.result
  let family := registration.operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let rows := mkIdent `rows
  let index := mkIdent `index
  let fallback := mkIdent `fallback
  let storage := mkIdent `storage
  let defaultView := mkIdent `defaultView
  let heap := mkIdent `heap
  let observed := mkIdent `observed
  let defaultObserved := mkIdent `defaultObserved
  let term (name : TSyntax `ident) : TSyntax `term := ⟨name.raw⟩
  let plan ← readPlan array result "" (term rows) (term index) (term fallback)
    (term storage) (term defaultView) (term heap) (term observed) (term defaultObserved)
  let body := plan.body.push (← `(doElem| return $(plan.sourceValue)))
  let sequence : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (body.map (·.raw))⟩
  let declaration : ParsedDeclaration := {
    name := mkIdent `getD
    params := #[{ name := storage, type := ← rawTypeTerm array.coreTy },
      { name := index, type := ← `(Nat) },
      { name := defaultView, type := ← rawTypeTerm result.coreTy }]
    result := ← rawTypeTerm result.coreTy
    body := ← `(do $sequence:doSeq)
    termination := ← `(Lean.Parser.Termination.suffix|) }
  let function ← liftMacroM declaration.toSyntax
  let scalarReads := mkIdent `Complexity.Language.Buffer.GetD
  let rowReads := mkIdent `Complexity.Language.Buffer.Ragged.GetD
  let source ← `(command| source_program% $family:ident importing
    $scalarReads:ident, $rowReads:ident where
      $function:sourceFunction)
  let arrayType ← termOfExpr array.nativeType
  let resultType ← termOfExpr result.nativeType
  let rawArray ← actualTypeTerm array.coreTy
  let rawResult ← actualTypeTerm result.coreTy
  let arrayRep ← `(($(← termOfExpr array.representation) : Complexity.Language.Representation
    $arrayType $(← termOfExpr (coreTypeExpr array.coreTy))))
  let resultRep ← `(($(← termOfExpr result.representation) : Complexity.Language.Representation
    $resultType $(← termOfExpr (coreTypeExpr result.coreTy))))
  let rowsRelated ← relationTerm array (term rows) (term storage) (term heap)
  let fallbackRelated ← relationTerm result (term fallback) (term defaultView) (term heap)
  let returnedRelated ← relationTerm result (← `(($rows:ident).getD $index:ident $fallback:ident))
    (← `(returned)) (term heap)
  let getD := name `getD
  let equation := name `getD_eq
  let evaluated := name `getD_eval
  let equations ← plan.equations.mapM fun equation => `(Lean.Parser.Tactic.simpLemma| $equation:ident)
  let mut proof := plan.proof
  proof := proof.push (← `(tactic| refine ⟨$(plan.returned), ?_, $(plan.related)⟩))
  let simpRules := #[← `(Lean.Parser.Tactic.simpLemma| $equation:ident),
    ← `(Lean.Parser.Tactic.simpLemma| source_eval),
    ← `(Lean.Parser.Tactic.simpLemma| Complexity.Language.Representation.optionEmbedding_none),
    ← `(Lean.Parser.Tactic.simpLemma| Complexity.Language.Representation.optionEmbedding_some),
    ← `(Lean.Parser.Tactic.simpLemma| Complexity.Language.Representation.optionUnpack),
    ← `(Lean.Parser.Tactic.simpLemma| Option.isSome),
    ← `(Lean.Parser.Tactic.simpLemma| Option.getD)] ++ equations
  if plan.splitValues.isEmpty then
    proof := proof.push (← `(tactic| simp only [$simpRules,*]))
  else
    for value in plan.splitValues do
      proof := proof.push (← `(tactic| all_goals cases $value:term))
    proof := proof.push (← `(tactic| all_goals simp_all only [$simpRules,*]))
    proof := proof.push (← `(tactic| all_goals split_ifs <;> simp_all only [$simpRules,*]))
  let evaluation ← `(command|
    theorem $evaluated:ident ($rows:ident : $arrayType) ($index:ident : Nat)
        ($fallback:ident : $resultType) ($storage:ident : $rawArray)
        ($defaultView:ident : $rawResult) ($heap:ident : Complexity.Language.Heap)
        ($observed:ident : $rowsRelated) ($defaultObserved:ident : $fallbackRelated) :
        ∃ returned, $getD:ident $storage:ident $index:ident $defaultView:ident $heap:ident =
          Part.some (.ok returned, $heap:ident) ∧ $returnedRelated := by
      $proof:tactic*)
  let mut roots : Array (TSyntax ``bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``bracketedBinder) := #[]
  let actualDefault ← if result.isIdentity then pure (term fallback) else do
    roots := roots.push (← `(bracketedBinder| ($defaultView:ident : $rawResult)))
    observations := observations.push (← `(bracketedBinder| ($defaultObserved:ident : $fallbackRelated)))
    pure (term defaultView)
  let defaultProof ← if result.isIdentity then `(rfl) else pure (term defaultObserved)
  let relation := name `getD_eval_exists
  let preserving := name `getD_eval_exists_preserving
  let relationDecl ← `(command|
    theorem $relation:ident ($rows:ident : $arrayType) ($index:ident : Nat)
        ($fallback:ident : $resultType) ($storage:ident : $rawArray) $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) ($observed:ident : $rowsRelated)
        $observations:bracketedBinder* :
        ∃ returned finish,
          $getD:ident $storage:ident $index:ident $actualDefault $heap:ident =
            Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (($rows:ident).getD $index:ident $fallback:ident) returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨returned, execution, related⟩ := $evaluated:ident
        $rows:ident $index:ident $fallback:ident $storage:ident $actualDefault $heap:ident
        $observed:ident $defaultProof
      exact ⟨returned, $heap:ident, execution, related,
        Complexity.Language.Heap.ShapeExtends.refl $heap:ident⟩)
  let preservingDecl ← `(command|
    theorem $preserving:ident ($rows:ident : $arrayType) ($index:ident : Nat)
        ($fallback:ident : $resultType) ($storage:ident : $rawArray) $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) ($observed:ident : $rowsRelated)
        $observations:bracketedBinder* :
        ∃ returned finish,
          $getD:ident $storage:ident $index:ident $actualDefault $heap:ident =
            Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (($rows:ident).getD $index:ident $fallback:ident) returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
          Complexity.Language.Buffer.PreservesContents $heap:ident finish := by
      obtain ⟨returned, execution, related⟩ := $evaluated:ident
        $rows:ident $index:ident $fallback:ident $storage:ident $actualDefault $heap:ident
        $observed:ident $defaultProof
      exact ⟨returned, $heap:ident, execution, related,
        Complexity.Language.Heap.ShapeExtends.refl $heap:ident,
        fun {_} _ _ contents => contents⟩)
  let signatures := name `signatures
  let program := name `program
  let getDId := name `getDId
  let representation := name `representation
  let refines := name `getD_refines
  let observe := name `getD_observe
  let representationDecl ← `(command|
    def $representation:ident : Complexity.Language.FunctionRepresentation
        ($arrayType × Nat × $resultType) (fun _ => $resultType) $signatures:ident[$getDId:ident] :=
      Complexity.Language.FunctionRepresentation.ofResult
        (Complexity.Language.ArgumentRepresentation.cons $arrayRep
          (Complexity.Language.ArgumentRepresentation.cons Complexity.Language.Representation.nat
            (Complexity.Language.ArgumentRepresentation.single $resultRep)))
        (fun _ => $resultRep))
  let refinement ← `(command|
    theorem $refines:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $getDId:ident $representation:ident (fun _ => True)
        (fun input => input.1.getD input.2.1 input.2.2) := by
      intro input _
      apply Complexity.Language.FunctionTotal.iff_eval.mpr
      intro args heap observed
      rcases observed with ⟨contents, index, fallback⟩
      change input.2.1 = args.tail.head at index
      obtain ⟨returned, execution, result⟩ := $evaluated:ident input.1 input.2.1 input.2.2
        args.head args.tail.tail.head heap contents fallback
      refine ⟨returned, heap, ?_, result⟩
      rw [$observe:ident, ← index]
      exact execution)
  return #[source.raw, evaluation.raw, relationDecl.raw, preservingDecl.raw,
    representationDecl.raw, refinement.raw]

/-- Transport a real initialized allocator through a checked scalar or direct
record view. No source wrapper, executable map or new cost convention is added. -/
def arrayReplicateDeclarations (registration : ArrayReplicateRegistration) :
    TermElabM (Array Syntax) := do
  let some base := registration.base | return ← compositeReplicateDeclarations registration
  let array := registration.operation.result
  let .arrayView element storage _ := array
    | throwError "replication requires a checked scalar or direct field view"
  let embedding ← match element with
    | .record _ _ embedding | .scalar _ embedding => pure embedding
    | _ => throwError "replication requires a checked scalar or direct field view"
  let name (suffix : Name) := mkIdentFrom registration.contracts
    (registration.contracts.getId ++ suffix)
  let sourceName := base.family.getId ++ base.sourceName
  let source := mkCIdent sourceName
  let sourcePreserving := mkCIdent (sourceName.appendAfter "_eval_exists_preserving")
  let sourceObserve := mkCIdent (sourceName.appendAfter "_observe")
  let signatures := mkCIdent (base.family.getId ++ `signatures)
  let program := mkCIdent (base.family.getId ++ `program)
  let functionId := mkCIdent (sourceName.appendAfter "Id")
  let initialType ← termOfExpr element.nativeType
  let resultType ← termOfExpr array.nativeType
  let rawInitial ← actualTypeTerm element.coreTy
  let view ← termOfExpr embedding
  let initialRep ← `(($(← termOfExpr element.representation) :
    Complexity.Language.Representation $initialType $(← termOfExpr (coreTypeExpr element.coreTy))))
  let resultRep ← `(($(← termOfExpr array.representation) :
    Complexity.Language.Representation $resultType $(← termOfExpr (coreTypeExpr array.coreTy))))
  let storageRep ← `(($(← termOfExpr storage.representation) :
    Complexity.Language.Representation $(← termOfExpr storage.nativeType)
      $(← termOfExpr (coreTypeExpr storage.coreTy))))
  let preserving := name `replicate_eval_exists_preserving
  let relation := name `replicate_eval_exists
  let representation := name `representation
  let refines := name `replicate_refines
  let preservingDecl ← `(command|
    theorem $preserving:ident (length : Nat) (initial : $initialType)
        (value : $rawInitial) (heap : Complexity.Language.Heap)
        (observed : ($initialRep).Rel initial value heap) :
        ∃ returned finish,
          $source:ident length value heap = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (Array.replicate length initial) returned finish ∧
          Complexity.Language.Heap.ShapeExtends heap finish ∧
          Complexity.Language.Buffer.PreservesContents heap finish := by
      have same : $view initial = value := by
        simpa only [Complexity.Language.Representation.comap_rel,
          Complexity.Language.Representation.prod_rel,
          Complexity.Language.Representation.ofEmbedding_rel, Prod.ext_iff] using observed
      rw [← same]
      obtain ⟨returned, finish, executed, related, shape, preserved⟩ :=
        $sourcePreserving:ident length ($view initial) heap
      refine ⟨returned, finish, executed, ?_, shape, preserved⟩
      change ($storageRep).Rel ((Array.replicate length initial).map $view) returned finish
      simpa only [Array.map_replicate] using related)
  let relationDecl ← `(command|
    theorem $relation:ident (length : Nat) (initial : $initialType)
        (value : $rawInitial) (heap : Complexity.Language.Heap)
        (observed : ($initialRep).Rel initial value heap) :
        ∃ returned finish,
          $source:ident length value heap = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (Array.replicate length initial) returned finish ∧
          Complexity.Language.Heap.ShapeExtends heap finish := by
      obtain ⟨returned, finish, executed, related, shape, _⟩ :=
        $preserving:ident length initial value heap observed
      exact ⟨returned, finish, executed, related, shape⟩)
  let representationDecl ← `(command|
    def $representation:ident : Complexity.Language.FunctionRepresentation
        (Nat × $initialType) (fun _ => $resultType) $signatures:ident[$functionId:ident] :=
      Complexity.Language.FunctionRepresentation.ofResult
        (Complexity.Language.ArgumentRepresentation.cons Complexity.Language.Representation.nat
          (Complexity.Language.ArgumentRepresentation.single $initialRep))
        (fun _ => $resultRep))
  let refinement ← `(command|
    theorem $refines:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $functionId:ident $representation:ident (fun _ => True)
        (fun input => Array.replicate input.1 input.2) := by
      intro input _
      apply Complexity.Language.FunctionTotal.iff_eval.mpr
      intro args heap observed
      rcases observed with ⟨length, initial⟩
      change input.1 = args.head at length
      obtain ⟨returned, finish, executed, related, _⟩ :=
        $relation:ident input.1 input.2 args.tail.head heap initial
      refine ⟨returned, finish, ?_, related⟩
      rw [$sourceObserve:ident, ← length]
      exact executed)
  return #[preservingDecl.raw, relationDecl.raw, representationDecl.raw, refinement.raw]

end Complexity.Language.Syntax.Represented.Internal
