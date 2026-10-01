/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Basic
import Complexity.Language.Buffer.Replicate
import Complexity.Language.Eval.Simp

/-!
# Initialized composite array columns

Generate an actual call to the existing initialized allocator for each scalar
column. Recursive product/record views reuse their fixed representation, not
an executable host map. The generated proof retains every intermediate heap,
frames earlier columns across later allocations, and preserves old contents.
Source wrappers and calls are compiled normally and have real costs.
Empty arrays use the same allocators, including one zero boundary at every
ragged level. They require no fabricated initializer for a heap-backed element.
-/

namespace Complexity.Language.Syntax.Represented.Internal

open Lean Meta Elab Term Command
open Lean.Parser.Term

private structure ReplicatePlan where
  body : Array (TSyntax `doElem)
  proof : Array (TSyntax `tactic)
  equations : Array (TSyntax `ident)
  sourceValue : TSyntax `term
  returned : TSyntax `term
  finish : TSyntax `term
  related : TSyntax `term
  shape : TSyntax `term
  contents : TSyntax `term
  splitValues : Array (TSyntax `term) := #[]

private def replicateRelation (array : NativeType)
    (length initial returned heap : TSyntax `term) : TermElabM (TSyntax `term) := do
  let rep ← termOfExpr array.representation
  let native ← termOfExpr array.nativeType
  let core ← termOfExpr (coreTypeExpr array.coreTy)
  `(($rep : Complexity.Language.Representation $native $core).Rel
    (Array.replicate $length $initial) $returned $heap)

private partial def replicatePlan (array element : NativeType) (path : String)
    (length initial value heap observed : TSyntax `term) : TermElabM ReplicatePlan := do
  let checked (plan : ReplicatePlan) : TermElabM ReplicatePlan := do
    let relation ← replicateRelation array length initial plan.returned plan.finish
    return { plan with related := ← `(show $relation from by
      have initialized := $(plan.related)
      simpa only [Complexity.Language.Representation.comap_rel,
        Complexity.Language.Representation.prod_rel,
        Complexity.Language.Representation.arrayProd_rel,
        Complexity.Language.Representation.arrayUnzip, Function.Embedding.arrayMap,
        Function.Embedding.coeFn_mk, Array.map_replicate] using initialized) }
  let pair (left right : NativeType) : TermElabM ReplicatePlan := do
    let (leftElement, rightElement) ← match element with
      | .prod left right => pure (left, right)
      | .pure _ => do
          let args := element.nativeType.getAppArgs
          pure (← resolveNativeType args[0]!, ← resolveNativeType args[1]!)
      | _ => throwError "column replication must retain the initializer's product layout"
    let first ← replicatePlan left leftElement (path ++ "L") length
      (← `(($initial).1)) (← `(($value).1)) heap
      (← if element.isIdentity then `(congrArg Prod.fst $observed) else `(And.left $observed))
    let second ← replicatePlan right rightElement (path ++ "R") length
      (← `(($initial).2)) (← `(($value).2)) first.finish
      (← if element.isIdentity then `(congrArg Prod.snd $observed) else `(And.right $observed))
    let frame ← preservation left first.finish second.finish second.shape (some second.contents)
    let retained ← `($frame $(first.related))
    checked {
      body := first.body ++ second.body
      proof := first.proof ++ second.proof
      equations := first.equations ++ second.equations
      sourceValue := ← `(($(first.sourceValue), $(second.sourceValue)))
      returned := ← `(($(first.returned), $(second.returned)))
      finish := second.finish
      related := ← `(And.intro $retained $(second.related))
      shape := ← `(Complexity.Language.Heap.ShapeExtends.trans $(first.shape) $(second.shape))
      contents := ← `(show Complexity.Language.Buffer.PreservesContents $heap $(second.finish)
        from fun {_} view values contents =>
          $(second.contents) view values ($(first.contents) view values contents))
      splitValues := first.splitValues ++ second.splitValues }
  match array with
  | .arrayView field columns _ =>
      match field with
      | .record _ layout embedding =>
          let view ← termOfExpr embedding
          checked (← replicatePlan columns layout path length (← `($view $initial))
            value heap observed)
      | .scalar _ embedding =>
          let view ← termOfExpr embedding
          checked (← replicatePlan columns (← resolveType (← `(Nat))) path length
            (← `($view $initial)) value heap observed)
      | .int =>
          checked (← replicatePlan columns (← resolveType (← `(Bool × Nat))) path length
            (← `(Complexity.Language.Representation.intEquiv $initial)) value heap observed)
      | .option payload =>
          let (initialDefault, rawDefault) ← payload.optionColumnDefault
          let packed := mkIdent (Name.mkSimple ("packed" ++ path))
          let fields := NativeType.prod (← resolveType (← `(Bool))) payload
          let rawFields ← rawTypeTerm fields.coreTy
          let rep ← `(($(← termOfExpr payload.representation) :
            Complexity.Language.Representation $(← termOfExpr payload.nativeType)
              $(← termOfExpr (coreTypeExpr payload.coreTy))))
          let inner ← replicatePlan columns fields path length
            (← `(Complexity.Language.Representation.optionEmbedding $initialDefault $initial))
            ⟨packed.raw⟩ heap
            (← `(Complexity.Language.Representation.optionEmbedding_rel
              (payload := $rep) (default := $initialDefault) (rawDefault := $rawDefault)
              (value := $initial) (actual := $value) (heap := $heap) (by rfl) $observed))
          checked { inner with
            body := #[← `(doElem| let mut $packed:ident : $rawFields := (false, $rawDefault)),
              ← `(doElem| match $value:term with
                | none => $packed:ident := (false, $rawDefault)
                | some payload => $packed:ident := (true, payload))] ++ inner.body
            proof := #[← `(tactic| let $packed:ident :=
              Complexity.Language.Representation.optionEmbedding $rawDefault $value)] ++ inner.proof
            equations := inner.equations.push packed
            splitValues := inner.splitValues.push value }
      | _ =>
          let .prod left right := columns
            | throwError "replication requires supported scalar field columns"
          pair left right
  | .arrayProd left right => pair (.array left) (.array right)
  | .array kind =>
      let fn := `Complexity.Language.Buffer.Replicate ++
        (match kind with | .nat => `replicateNat | .bool => `replicateBool)
      let call := mkIdent fn
      let contract := mkCIdent (fn.appendAfter "_eval_exists_preserving")
      let named (stem : String) := mkIdent (Name.mkSimple (stem ++ path))
      let sourceInitial := named "initialColumn"
      let sourceValue := named "column"
      let returned := named "returned"
      let finish := named "finish"
      let execution := named "executed"
      let observation := named "related"
      let shape := named "shape"
      let contents := named "contents"
      let same := named "initialEq"
      let term (name : TSyntax `ident) : TSyntax `term := ⟨name.raw⟩
      let relation ← replicateRelation array length initial (term returned) (term finish)
      return {
        body := #[← `(doElem| let $sourceInitial:ident := $value),
          ← `(doElem| let $sourceValue:ident ← $call:ident $length $sourceInitial:ident)]
        proof := #[← `(tactic| have $same:ident : $initial = $value := $observed),
          ← `(tactic| obtain ⟨$returned:ident, $finish:ident, $execution:ident,
              $observation:ident, $shape:ident, $contents:ident⟩ :=
            $contract:ident $length $value $heap)]
        equations := #[execution]
        sourceValue := term sourceValue, returned := term returned, finish := term finish
        related := ← `(show $relation from by simpa only [$same:ident] using $observation:ident)
        shape := term shape, contents := term contents }
  | _ => throwError "replication requires scalar columns; row and linked payloads need other operations"

/-- Generate checked field-column allocation without a fixed arity or task-specific layout. -/
def compositeReplicateDeclarations (registration : ArrayReplicateRegistration) :
    TermElabM (Array Syntax) := do
  let array := registration.operation.result
  let some element := registration.operation.inputs[1]?
    | throwError "array replication requires an initializer"
  let family := registration.contracts
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let length := mkIdent `length
  let initial := mkIdent `initial
  let value := if element.isIdentity then initial else mkIdent `value
  let heap := mkIdent `heap
  let observed := mkIdent `observed
  let term (name : TSyntax `ident) : TSyntax `term := ⟨name.raw⟩
  let observation ← if element.isIdentity then `(rfl) else pure (term observed)
  let plan ← replicatePlan array element "" (term length) (term initial)
    (term value) (term heap) observation
  let body := plan.body.push (← `(doElem| return $(plan.sourceValue)))
  let sequence : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (body.map (·.raw))⟩
  let declaration : ParsedDeclaration := {
    name := mkIdent `replicate
    params := #[{ name := length, type := ← `(Nat) },
      { name := value, type := ← rawTypeTerm element.coreTy }]
    result := ← rawTypeTerm array.coreTy
    body := ← `(do $sequence:doSeq)
    termination := ← `(Lean.Parser.Termination.suffix|) }
  let function ← liftMacroM declaration.toSyntax
  let allocators := mkIdent `Complexity.Language.Buffer.Replicate
  let source ← `(command| source_program% $family:ident importing $allocators:ident where
    $function:sourceFunction)
  let initialType ← termOfExpr element.nativeType
  let resultType ← termOfExpr array.nativeType
  let initialRep ← `(($(← termOfExpr element.representation) :
    Complexity.Language.Representation $initialType $(← termOfExpr (coreTypeExpr element.coreTy))))
  let resultRep ← `(($(← termOfExpr array.representation) :
    Complexity.Language.Representation $resultType $(← termOfExpr (coreTypeExpr array.coreTy))))
  let rawInitial ← actualTypeTerm element.coreTy
  let mut roots : Array (TSyntax ``bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``bracketedBinder) := #[]
  unless element.isIdentity do
    roots := roots.push (← `(bracketedBinder| ($value:ident : $rawInitial)))
    observations := observations.push (← `(bracketedBinder|
      ($observed:ident : ($initialRep).Rel $initial:ident $value:ident $heap:ident)))
  let replicate := name `replicate
  let equation := name `replicate_eq
  let preserving := name `replicate_eval_exists_preserving
  let relation := name `replicate_eval_exists
  let mut proof := plan.proof
  proof := proof.push (← `(tactic|
    refine ⟨$(plan.returned), $(plan.finish), ?_, $(plan.related), $(plan.shape), $(plan.contents)⟩))
  let equations ← plan.equations.mapM fun equation => `(Lean.Parser.Tactic.simpLemma| $equation:ident)
  let simpRules := #[← `(Lean.Parser.Tactic.simpLemma| $equation:ident),
    ← `(Lean.Parser.Tactic.simpLemma| source_eval),
    ← `(Lean.Parser.Tactic.simpLemma| Complexity.Language.Representation.optionEmbedding_none),
    ← `(Lean.Parser.Tactic.simpLemma| Complexity.Language.Representation.optionEmbedding_some),
    ← `(Lean.Parser.Tactic.simpLemma| Option.isSome),
    ← `(Lean.Parser.Tactic.simpLemma| Option.getD)] ++ equations
  if plan.splitValues.isEmpty then
    proof := proof.push (← `(tactic| simp only [$simpRules,*]))
  else
    for value in plan.splitValues do
      proof := proof.push (← `(tactic| all_goals cases $value:term))
    proof := proof.push (← `(tactic| all_goals simp_all only [$simpRules,*]))
  let preservingDecl ← `(command|
    theorem $preserving:ident ($length:ident : Nat) ($initial:ident : $initialType)
        $roots:bracketedBinder* ($heap:ident : Complexity.Language.Heap)
        $observations:bracketedBinder* :
        ∃ returned finish,
          $replicate:ident $length:ident $value:ident $heap:ident = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (Array.replicate $length:ident $initial:ident) returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
          Complexity.Language.Buffer.PreservesContents $heap:ident finish := by
      $proof:tactic*)
  let arguments := if element.isIdentity then #[term length, term initial, term heap]
    else #[term length, term initial, term value, term heap, term observed]
  let relationDecl ← `(command|
    theorem $relation:ident ($length:ident : Nat) ($initial:ident : $initialType)
        $roots:bracketedBinder* ($heap:ident : Complexity.Language.Heap)
        $observations:bracketedBinder* :
        ∃ returned finish,
          $replicate:ident $length:ident $value:ident $heap:ident = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel (Array.replicate $length:ident $initial:ident) returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨returned, finish, executed, related, shape, _⟩ := $preserving:ident $arguments*
      exact ⟨returned, finish, executed, related, shape⟩)
  let signatures := name `signatures
  let program := name `program
  let functionId := name `replicateId
  let observe := name `replicate_observe
  let representation := name `representation
  let refines := name `replicate_refines
  let representationDecl ← `(command|
    def $representation:ident : Complexity.Language.FunctionRepresentation
        (Nat × $initialType) (fun _ => $resultType) $signatures:ident[$functionId:ident] :=
      Complexity.Language.FunctionRepresentation.ofResult
        (Complexity.Language.ArgumentRepresentation.cons Complexity.Language.Representation.nat
          (Complexity.Language.ArgumentRepresentation.single $initialRep))
        (fun _ => $resultRep))
  let arguments ← if element.isIdentity then
      #[`(input.1), `(input.2), `(heap)].mapM id
    else #[`(input.1), `(input.2), `(args.tail.head), `(heap), `(initial)].mapM id
  let adjust ← if element.isIdentity then `(tactic| rw [← initial]) else `(tactic| skip)
  let refinement ← `(command|
    theorem $refines:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $functionId:ident $representation:ident (fun _ => True)
        (fun input => Array.replicate input.1 input.2) := by
      intro input _
      apply Complexity.Language.FunctionTotal.iff_eval.mpr
      intro args heap observed
      rcases observed with ⟨length, initial⟩
      change input.1 = args.head at length
      obtain ⟨returned, finish, executed, related, _⟩ := $relation:ident $arguments*
      refine ⟨returned, finish, ?_, related⟩
      rw [$observe:ident, ← length]
      $adjust:tactic
      exact executed)
  return #[source.raw, preservingDecl.raw, relationDecl.raw, representationDecl.raw, refinement.raw]

private partial def emptyColumns (array : NativeType) : TermElabM (TSyntax `term) := do
  match array with
  | .prod left right => `(($(← emptyColumns left), $(← emptyColumns right)))
  | _ => `((#[] : $(← termOfExpr array.nativeType)))

private partial def emptyPlan (array : NativeType) (path : String)
    (heap : TSyntax `term) : TermElabM ReplicatePlan := do
  let checked (plan : ReplicatePlan) : TermElabM ReplicatePlan := do
    let rep ← termOfExpr array.representation
    let native ← termOfExpr array.nativeType
    let core ← termOfExpr (coreTypeExpr array.coreTy)
    let empty ← emptyColumns array
    return { plan with related := ← `(show
      ($rep : Complexity.Language.Representation $native $core).Rel
        $empty $(plan.returned) $(plan.finish) from by
      have initialized := $(plan.related)
      simpa only [Complexity.Language.Representation.comap_rel,
        Complexity.Language.Representation.prod_rel,
        Complexity.Language.Representation.arrayProd_rel,
        Complexity.Language.Representation.raggedArrayOf_rel,
        Complexity.Language.Representation.arrayUnzip, Function.Embedding.arrayMap,
        Function.Embedding.coeFn_mk, Array.map_empty, Array.flatten_empty,
        Array.flattenOffsets_empty, Array.replicate_zero, Array.replicate_succ]
        using initialized) }
  let join (left : NativeType) (first second : ReplicatePlan) : TermElabM ReplicatePlan := do
    let frame ← preservation left first.finish second.finish second.shape (some second.contents)
    checked {
      body := first.body ++ second.body
      proof := first.proof ++ second.proof
      equations := first.equations ++ second.equations
      sourceValue := ← `(($(first.sourceValue), $(second.sourceValue)))
      returned := ← `(($(first.returned), $(second.returned)))
      finish := second.finish
      related := ← `(And.intro ($frame $(first.related)) $(second.related))
      shape := ← `(Complexity.Language.Heap.ShapeExtends.trans $(first.shape) $(second.shape))
      contents := ← `(show Complexity.Language.Buffer.PreservesContents $heap $(second.finish)
        from fun {_} view values contents =>
          $(second.contents) view values ($(first.contents) view values contents)) }
  let pair (left right : NativeType) : TermElabM ReplicatePlan := do
    let first ← emptyPlan left (path ++ "L") heap
    let second ← emptyPlan right (path ++ "R") first.finish
    join left first second
  match array with
  | .arrayView _ columns _ => checked (← emptyPlan columns path heap)
  | .arrayProd left right => pair (.array left) (.array right)
  | .prod left right => pair left right
  | .raggedArray payload =>
      let scalar ← resolveType (← `(Nat))
      let first ← replicatePlan (.array .nat) scalar (path ++ "L")
        (← `(1)) (← `(0)) (← `(0)) heap (← `(rfl))
      let second ← emptyPlan payload (path ++ "R") first.finish
      join (.array .nat) first second
  | .array kind =>
      let scalar ← resolveType (← match kind with | .nat => `(Nat) | .bool => `(Bool))
      let initial ← match kind with | .nat => `(0) | .bool => `(false)
      checked (← replicatePlan array scalar path (← `(0)) initial initial heap (← `(rfl)))
  | _ => throwError "empty array construction requires supported array columns"

/-- Lower ordinary empty-array syntax to actual canonical column allocations. -/
def arrayEmptyDeclarations (operation : Operation) : TermElabM (Array Syntax) := do
  let array := operation.result
  let family := operation.family
  let name (suffix : Name) := mkIdentFrom family (family.getId ++ suffix)
  let heap := mkIdent `heap
  let plan ← emptyPlan array "" ⟨heap.raw⟩
  let body := plan.body.push (← `(doElem| return $(plan.sourceValue)))
  let sequence : TSyntax ``doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq (body.map (·.raw))⟩
  let declaration : ParsedDeclaration := {
    name := mkIdent `empty, params := #[], result := ← rawTypeTerm array.coreTy
    body := ← `(do $sequence:doSeq)
    termination := ← `(Lean.Parser.Termination.suffix|) }
  let function ← liftMacroM declaration.toSyntax
  let allocators := mkIdent `Complexity.Language.Buffer.Replicate
  let source ← `(command| source_program% $family:ident importing $allocators:ident where
    $function:sourceFunction)
  let resultType ← termOfExpr array.nativeType
  let resultRep ← `(($(← termOfExpr array.representation) :
    Complexity.Language.Representation $resultType $(← termOfExpr (coreTypeExpr array.coreTy))))
  let empty := name `empty
  let equation := name `empty_eq
  let preserving := name `empty_eval_exists_preserving
  let relation := name `empty_eval_exists
  let mut proof := plan.proof
  proof := proof.push (← `(tactic|
    refine ⟨$(plan.returned), $(plan.finish), ?_, $(plan.related), $(plan.shape), $(plan.contents)⟩))
  let equations ← plan.equations.mapM fun equation => `(Lean.Parser.Tactic.simpLemma| $equation:ident)
  proof := proof.push (← `(tactic| simp only [$equation:ident, source_eval, $equations,*]))
  let preservingDecl ← `(command|
    theorem $preserving:ident ($heap:ident : Complexity.Language.Heap) :
        ∃ returned finish,
          $empty:ident $heap:ident = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel #[] returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
          Complexity.Language.Buffer.PreservesContents $heap:ident finish := by
      $proof:tactic*)
  let relationDecl ← `(command|
    theorem $relation:ident ($heap:ident : Complexity.Language.Heap) :
        ∃ returned finish,
          $empty:ident $heap:ident = Part.some (.ok returned, finish) ∧
          ($resultRep).Rel #[] returned finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨returned, finish, executed, related, shape, _⟩ := $preserving:ident $heap:ident
      exact ⟨returned, finish, executed, related, shape⟩)
  let signatures := name `signatures
  let program := name `program
  let functionId := name `emptyId
  let observe := name `empty_observe
  let representation := name `representation
  let refines := name `empty_refines
  let representationDecl ← `(command|
    def $representation:ident : Complexity.Language.FunctionRepresentation
        Unit (fun _ => $resultType) $signatures:ident[$functionId:ident] :=
      Complexity.Language.FunctionRepresentation.ofResult
        Complexity.Language.ArgumentRepresentation.nil (fun _ => $resultRep))
  let refinement ← `(command|
    theorem $refines:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $functionId:ident $representation:ident (fun _ => True)
        (fun _ => #[]) := by
      intro input _
      apply Complexity.Language.FunctionTotal.iff_eval.mpr
      intro args heap _
      obtain ⟨returned, finish, executed, related, _⟩ := $relation:ident heap
      refine ⟨returned, finish, ?_, related⟩
      rw [$observe:ident]
      exact executed)
  return #[source.raw, preservingDecl.raw, relationDecl.raw, representationDecl.raw, refinement.raw]

end Complexity.Language.Syntax.Represented.Internal
