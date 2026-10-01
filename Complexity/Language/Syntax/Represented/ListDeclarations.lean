/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic
import Complexity.Language.Eval.Simp

/-!
# Compositional linked product operations

The two field operations execute in sequence at their actual heaps. Constructor
calls allocate real nodes and retain the original shared tails; readers use the
existing head/tail operations. Mathematical unzip is only a representation,
never executable preprocessing. Nested products compose the same declarations.
-/

namespace Complexity.Language.Syntax.Represented.Internal

open Lean Meta Elab Term Command
open Lean.Parser.Term

private def represented (type : NativeType) : TermElabM (TSyntax `term) := do
  `(($(← termOfExpr type.representation) : Complexity.Language.Representation
    $(← termOfExpr type.nativeType) $(← termOfExpr (coreTypeExpr type.coreTy))))

private def constructorInvocation (operation : Operation)
    (head values value roots heap headObserved tailObserved : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let some element := operation.inputs[0]?
    | throwError "a linked constructor needs a head"
  let some contract := (← operation.requireModel).preservingRelation
    | throwError "a linked constructor needs its actual contents frame"
  if element.isIdentity then
    `($contract:ident $value $values $roots $heap $tailObserved)
  else
    `($contract:ident $head $values $value $roots $heap $headObserved $tailObserved)

/-- Emit one source operation and checked ordinary list correspondence. -/
def productListDeclarations (registration : ProductListRegistration) :
    TermElabM (Array Syntax) := do
  let { construct, list, element, left, right, operation } := registration
  let .listView _ (.prod leftList rightList) _ := list
    | throwError "product-list declarations require two linked field views"
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let named (suffix : String) := name (operation.sourceName.appendAfter suffix)
  let fn := name operation.sourceName
  let equation := named "_eq"
  let observe := named "_observe"
  let preserving := named "_rel_preserving"
  let relation := named "_rel"
  let refinement := named "_refines"
  let representation := named "_representation"
  let fnId := named "Id"
  let signatures := name `signatures
  let program := name `program
  let leftCall := mkIdent (left.family.getId ++ left.sourceName)
  let rightCall := mkIdent (right.family.getId ++ right.sourceName)
  let headType ← termOfExpr element.nativeType
  let listType ← termOfExpr list.nativeType
  let resultType ← termOfExpr operation.result.nativeType
  let rawHead ← actualTypeTerm element.coreTy
  let rawRoots ← actualTypeTerm list.coreTy
  let headRep ← represented element
  let listRep ← represented list
  let resultRep ← represented operation.result
  let rawHeadName := mkIdent (if element.isIdentity then `head else `value)
  let rawHeadTerm : TSyntax `term := ⟨rawHeadName.raw⟩
  let headTerm ← if element.isIdentity then pure rawHeadTerm else `(head)
  let roots := mkIdent `roots
  let sourceBody ← if construct then
      `(do
        let leftHead := ($rawHeadTerm).1
        let rightHead := ($rawHeadTerm).2
        let leftTail := $roots:ident.1
        let rightTail := $roots:ident.2
        let first ← $leftCall:ident leftHead leftTail
        let second ← $rightCall:ident rightHead rightTail
        return (first, second))
    else
      `(do
        let leftRoot := $roots:ident.1
        let rightRoot := $roots:ident.2
        let first ← $leftCall:ident leftRoot
        let second ← $rightCall:ident rightRoot
        match first with
        | none => return none
        | some first =>
          match second with
          | none => return none
          | some second => return some ((first.1, second.1), (first.2, second.2)))
  let mut parameters : Array ParsedParameter := #[]
  if construct then
    parameters := parameters.push { name := rawHeadName, type := ← rawTypeTerm element.coreTy }
  parameters := parameters.push { name := roots, type := ← rawTypeTerm list.coreTy }
  let declaration : ParsedDeclaration := {
    name := mkIdent operation.sourceName, params := parameters
    result := ← rawTypeTerm operation.result.coreTy
    body := sourceBody, termination := ← `(Lean.Parser.Termination.suffix|) }
  let function ← liftMacroM declaration.toSyntax
  let imports := if left.family.getId == right.family.getId then #[left.family]
    else #[left.family, right.family]
  let source ← `(command| source_program% $family:ident importing $imports:ident,* where
    $function:sourceFunction)
  let mut binders : Array (TSyntax ``bracketedBinder) := #[]
  if construct then
    binders := binders.push (← if element.isIdentity then
      `(bracketedBinder| ($rawHeadName:ident : $headType))
      else `(bracketedBinder| (head : $headType)))
  binders := binders.push (← `(bracketedBinder| (values : $listType)))
  if construct && !element.isIdentity then
    binders := binders.push (← `(bracketedBinder| ($rawHeadName:ident : $rawHead)))
  binders := binders.push (← `(bracketedBinder| ($roots:ident : $rawRoots)))
  binders := binders.push (← `(bracketedBinder| (heap : Complexity.Language.Heap)))
  if construct && !element.isIdentity then
    binders := binders.push (← `(bracketedBinder|
      (headObserved : ($headRep).Rel head $rawHeadTerm heap)))
  binders := binders.push (← `(bracketedBinder| (observed : ($listRep).Rel values $roots:ident heap)))
  let call ← if construct then `($fn:ident $rawHeadTerm $roots:ident heap)
    else `($fn:ident $roots:ident heap)
  let model ← if construct then `($headTerm :: values)
    else `(values.head?.map (fun head => (head, values.tail)))
  let mut proof : Array (TSyntax `tactic) := #[]
  let secondTailFrame ← preservation rightList (← `(heap)) (← `(middle))
    (← `(firstShape)) (some (← `(firstContents)))
  if construct then
    let some leftHead := left.inputs[0]?
      | throwError "left constructor requires a head"
    let some rightHead := right.inputs[0]?
      | throwError "right constructor requires a head"
    let leftObserved ← if element.isIdentity then `(rfl) else `(And.left headObserved)
    let rightObserved ← if element.isIdentity then `(rfl) else `(And.right headObserved)
    let leftArgs ← constructorInvocation left (← `(($headTerm).1)) (← `(values.map Prod.fst))
      (← `(($rawHeadTerm).1)) (← `($roots:ident.1)) (← `(heap)) leftObserved
      (← `(And.left observed))
    proof := proof.push (← `(tactic|
      obtain ⟨first, middle, firstExecuted, firstRelated, firstShape, firstContents⟩ := $leftArgs))
    let leftAdjust ← if leftHead.isIdentity then
        `(tactic| exact (by
          have same : ($headTerm).1 = ($rawHeadTerm).1 := $leftObserved
          simpa only [same] using firstRelated))
      else `(tactic| exact firstRelated)
    proof := proof.push (← `(tactic| have firstRelatedMath :
        ($(← represented leftList)).Rel (($headTerm).1 :: values.map Prod.fst) first middle := by
      $leftAdjust:tactic))
    let rightHeadFrame ← preservation rightHead (← `(heap)) (← `(middle))
      (← `(firstShape)) (some (← `(firstContents)))
    let rightArgs ← constructorInvocation right (← `(($headTerm).2)) (← `(values.map Prod.snd))
      (← `(($rawHeadTerm).2)) (← `($roots:ident.2)) (← `(middle))
      (← `($rightHeadFrame $rightObserved)) (← `($secondTailFrame (And.right observed)))
    proof := proof.push (← `(tactic|
      obtain ⟨second, finish, secondExecuted, secondRelated, secondShape, secondContents⟩ := $rightArgs))
    let rightAdjust ← if rightHead.isIdentity then
        `(tactic| exact (by
          have same : ($headTerm).2 = ($rawHeadTerm).2 := $rightObserved
          simpa only [same] using secondRelated))
      else `(tactic| exact secondRelated)
    proof := proof.push (← `(tactic| have secondRelatedMath :
        ($(← represented rightList)).Rel (($headTerm).2 :: values.map Prod.snd) second finish := by
      $rightAdjust:tactic))
    let firstFrame ← preservation leftList (← `(middle)) (← `(finish))
      (← `(secondShape)) (some (← `(secondContents)))
    proof := proof.push (← `(tactic| have retained := $firstFrame firstRelatedMath))
    proof := proof.push (← `(tactic| refine ⟨(first, second), finish, ?_, ?_,
      firstShape.trans secondShape, fun {_} view contents old =>
        secondContents view contents (firstContents view contents old)⟩))
    proof := proof.push (← `(tactic| · simp only [$equation:ident, source_eval,
      firstExecuted, secondExecuted]))
    proof := proof.push (← `(tactic| · exact And.intro retained secondRelatedMath))
  else
    let some leftContract := (← left.requireModel).preservingRelation
      | throwError "linked reader requires a preservation contract"
    let some rightContract := (← right.requireModel).preservingRelation
      | throwError "linked reader requires a preservation contract"
    proof := proof.push (← `(tactic|
      obtain ⟨first, middle, firstExecuted, firstRelated, firstShape, firstContents⟩ :=
        $leftContract:ident (values.map Prod.fst) $roots:ident.1 heap (And.left observed)))
    proof := proof.push (← `(tactic|
      obtain ⟨second, finish, secondExecuted, secondRelated, secondShape, secondContents⟩ :=
        $rightContract:ident (values.map Prod.snd) $roots:ident.2 middle
          ($secondTailFrame (And.right observed))))
    let firstFrame ← preservation left.result (← `(middle)) (← `(finish))
      (← `(secondShape)) (some (← `(secondContents)))
    proof := proof.push (← `(tactic| have retained := $firstFrame firstRelated))
    proof := proof.push (← `(tactic| have secondObserved :
        ($(← represented right.result)).Rel
          ((values.map Prod.snd).head?.map (fun head => (head, (values.map Prod.snd).tail)))
          second finish := secondRelated))
    proof := proof.push (← `(tactic|
      let returned := first.bind (fun l => second.map (fun r => ((l.1, r.1), (l.2, r.2))))))
    proof := proof.push (← `(tactic|
      refine ⟨returned, finish, ?_, ?_, firstShape.trans secondShape,
        fun {_} view contents old => secondContents view contents (firstContents view contents old)⟩))
    proof := proof.push (← `(tactic| · cases first <;> cases second <;>
      simp only [$equation:ident, source_eval, firstExecuted, secondExecuted, returned,
        Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]))
    proof := proof.push (← `(tactic| ·
      clear firstExecuted secondExecuted firstRelated secondRelated observed
        firstShape firstContents secondShape secondContents
      cases values <;> cases first <;> cases second <;>
      simp_all [returned, Complexity.Language.Representation.option,
        Complexity.Language.Representation.prod, Complexity.Language.Representation.ofEmbedding,
        Complexity.Language.Representation.comap, Complexity.Language.Representation.listUnzip,
        Equiv.listEquivOfEquiv, Function.Embedding.refl, -Function.Embedding.mk_id,
        Function.Embedding.prodMap,
        Prod.map, Prod.ext_iff, Function.comp_def]))
  let preservingDecl ← `(command|
    theorem $preserving:ident $binders:bracketedBinder* :
        ∃ returned finish, $call = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel $model returned finish ∧
          heap.ShapeExtends finish ∧ Complexity.Language.Buffer.PreservesContents heap finish := by
      $proof:tactic*)
  let mut arguments : Array (TSyntax `term) := #[]
  if construct then arguments := arguments.push headTerm
  arguments := arguments.push (← `(values))
  if construct && !element.isIdentity then arguments := arguments.push rawHeadTerm
  arguments := arguments ++ #[⟨roots.raw⟩, ← `(heap)]
  if construct && !element.isIdentity then arguments := arguments.push (← `(headObserved))
  arguments := arguments.push (← `(observed))
  let relationDecl ← `(command|
    theorem $relation:ident $binders:bracketedBinder* :
        ∃ returned finish, $call = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel $model returned finish ∧ heap.ShapeExtends finish := by
      obtain ⟨returned, finish, executed, related, shape, _⟩ := $preserving:ident $arguments*
      exact ⟨returned, finish, executed, related, shape⟩)
  let inputType ← if construct then `($headType × $listType) else pure listType
  let argsRep ← if construct then
      `(Complexity.Language.ArgumentRepresentation.cons $headRep
        (Complexity.Language.ArgumentRepresentation.single $listRep))
    else `(Complexity.Language.ArgumentRepresentation.single $listRep)
  let representationDecl ← `(command|
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $inputType (fun _ => $resultType) $signatures:ident[$fnId:ident] :=
      Complexity.Language.FunctionRepresentation.ofResult $argsRep (fun _ => $resultRep))
  let modelFn ← if construct then `(fun input => input.1 :: input.2)
    else `(fun values => values.head?.map (fun head => (head, values.tail)))
  let proofCall ← if construct then
      constructorInvocation operation (← `(input.1)) (← `(input.2)) (← `(args.head))
        (← `(args.tail.head)) (← `(heap)) (← `(observed.1)) (← `(observed.2))
    else `($preserving:ident input args.head heap observed)
  let adjust ← if construct && element.isIdentity then
      `(tactic| exact (by
        have headEq : input.1 = args.head := observed.1
        simpa only [← headEq] using related))
    else `(tactic| exact related)
  let refinementDecl ← `(command|
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $fnId:ident $representation:ident (fun _ => True) $modelFn := by
      intro input _
      apply Complexity.Language.FunctionTotal.iff_eval.mpr
      intro args heap observed
      obtain ⟨returned, finish, executed, related, _, _⟩ := $proofCall
      refine ⟨returned, finish, ?_, ?_⟩
      · rw [$observe:ident]
        exact executed
      · $adjust:tactic)
  return #[source.raw, preservingDecl.raw, relationDecl.raw, representationDecl.raw,
    refinementDecl.raw]

end Complexity.Language.Syntax.Represented.Internal
