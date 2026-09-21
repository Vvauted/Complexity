/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Relation
import Complexity.Language.Syntax.Represented.Correspondence.Exact

/-!
# Mathematical interfaces of represented functions

Generate native functions, exact or relational correspondence, total source
contracts and fixed representation interfaces from prepared function data.
These declarations publish proofs of the same source implementation.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term


namespace Internal

def rawFunction (fn : Function) : TermElabM (TSyntax `sourceFunction) := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← rawTypeTerm parameter.type.coreTy
    pure ({ name := parameter.name, type } : ParsedParameter)
  let result ← rawTypeTerm fn.result.coreTy
  let declaration : ParsedDeclaration := {
    name := fn.name, params := parameters, result, body := fn.rawBody
    termination := ← `(Lean.Parser.Termination.suffix|) }
  liftMacroM declaration.toSyntax

def nativeDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let parameters ← fn.parameters.mapM fun parameter => do
    let type ← termOfExpr parameter.type.nativeType
    `(bracketedBinder| ($(parameter.name):ident : $type))
  let result ← termOfExpr fn.result.nativeType
  let name := modelName names fn.name
  return (← `(command|
    /-- Ordinary mathematical function generated from the same represented source block. -/
    def $name:ident $parameters:bracketedBinder* : $result := Id.run $(model.nativeBody)
      $(model.termination):suffix)).raw
def equationDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) : TermElabM Syntax := do
  let header ← correspondenceHeader names fn
  let ⟨nativeName, _, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let equationName := fieldName names.publicFamily fn.name "_action_eq_native"
  let value ← encodedValue fn.result nativeValue
  let mut tactics ← compositionTactics header model
  tactics := tactics.push (← `(tactic| unfold $nativeName:ident))
  tactics := tactics ++ (← exactTrace model.calls model.returned ⟨heap.raw⟩ inputRelations)
  tactics ← tactics.mapM fun tactic => `(tactic| all_goals $tactic:tactic)
  return (← `(command|
    /-- The same source execution returns the encoded mathematical result without
    changing its supplied heap, under the actual input representations. -/
    theorem $equationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
        $rawAction $heap:ident = Part.some (.ok $value, $heap:ident) := by
      $tactics:tactic*)).raw

/-- The existing pure reconstruction covers scalar layouts and registered
records with direct scalar fields. An absent reconstruction is not a restriction
on source acceptance or its conditional representation theorem. -/
private def parameterReconstruction? (type : NativeType) : TermElabM (Option Expr) := do
  if type.isIdentity then
    return some (← withLocalDeclD `value type.nativeType fun value =>
      mkLambdaFVars #[value] value)
  let .record name _ _ := type | return none
  let some info := getStructureTypeInfo? (← getEnv) name | return none
  let rec scalarLayout : Ty → Bool
    | .nat | .bool | .unit => true
    | .prod left right => scalarLayout left && scalarLayout right
    | _ => false
  for field in info.fields do
    unless field.binderInfo == .default && scalarLayout field.type.coreTy do return none
    unless ← isDefEq field.type.nativeType
        (mkApp (mkConst ``Complexity.Language.Value) (coreTypeExpr field.type.coreTy)) do
      return none
  let rebuild ← nativeReconstruction (← resolvePureType type.nativeType)
  let encoding ← PureImport.encoding type
  let rawType := mkApp (mkConst ``Complexity.Language.Value) (coreTypeExpr type.coreTy)
  withLocalDeclD `raw rawType fun raw => do
    let value := mkApp rebuild raw
    let encoded ← mkAppM ``Function.Embedding.toFun #[encoding.embedding, value]
    unless ← isDefEq encoded raw do
      throwError "the represented input encoding does not match its checked native reconstruction"
  return some rebuild

def totalDeclaration? (names : DeclarationNames) (fn : Function) :
    TermElabM (Option Syntax) := do
  if !fn.hasExactEquation then return none
  let mut rebuilt := #[]
  for parameter in fn.parameters do
    let some reconstruction ← parameterReconstruction? parameter.type | return none
    rebuilt := rebuilt.push (Lean.Syntax.mkApp (← termOfExpr reconstruction) #[⟨parameter.rawName.raw⟩])
  let name := fieldName names.publicFamily fn.name "_total"
  let contract := fieldName names.sourceFamily fn.name "_contract"
  let totalIff := fieldName names.sourceFamily fn.name "_total_iff"
  let equation := fieldName names.publicFamily fn.name "_action_eq_native"
  let native := modelName names fn.name
  let heap := mkIdent (← mkFreshUserName `initialHeap)
  let finish := mkIdent (← mkFreshUserName `finalHeap)
  let returned := mkIdent (← mkFreshUserName `returned)
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ rebuilt
  let value ← encodedValue fn.result nativeValue
  let mut pre ← `(fun ($heap:ident : Complexity.Language.Heap) => True)
  let resultType ← actualTypeTerm fn.result.coreTy
  let mut post ← `(fun ($heap:ident : Complexity.Language.Heap) ($returned:ident : $resultType)
    ($finish:ident : Complexity.Language.Heap) => $returned:ident = $value ∧ $finish:ident = $heap:ident)
  for parameter in fn.parameters.reverse do
    let type ← actualTypeTerm parameter.type.coreTy
    pre ← `(fun ($(parameter.rawName):ident : $type) => $pre)
    post ← `(fun ($(parameter.rawName):ident : $type) => $post)
  let mut applied := rebuilt
  let mut observations := #[]
  for parameter in fn.parameters, nativeValue in rebuilt do
    unless parameter.type.isIdentity do
      applied := applied.push ⟨parameter.rawName.raw⟩
      let encoding ← PureImport.encoding parameter.type
      let exactEncoding ← encoding.relationSyntax
      observations := observations.push
        (← `(($exactEncoding $nativeValue $(parameter.rawName):ident $heap:ident).mpr rfl))
  applied := applied.push ⟨heap.raw⟩ ++ observations
  let correct := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
  let mut tactics := #[← `(tactic| apply ($totalIff:ident _ _).mpr)]
  for parameter in fn.parameters do
    tactics := tactics.push (← `(tactic| intro $(parameter.rawName):ident))
  tactics := tactics ++ #[← `(tactic| intro $heap:ident _),
    ← `(tactic| exact ⟨$value, $heap:ident, $correct, rfl, rfl⟩)]
  return some (← `(command|
    /-- Exact total source contract derived from the checked encoded-result
    equation and the existing raw-input reconstruction, with the same final heap. -/
    theorem $name:ident : $contract:ident $pre $post := by
      $tactics:tactic*)).raw


def relationDeclaration (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) (preserveArrays : Bool := false)
    (ranges : Array RangeRegistration := #[]) : TermElabM Syntax := do
  let family := names.publicFamily
  let header ← correspondenceHeader names fn
  let ⟨nativeName, _, heap, parameters, roots, observations, nativeValue, rawAction,
    inputRelations⟩ := header
  let relationName := fieldName family fn.name
    (if preserveArrays then "_action_rel_native_preserving" else "_action_rel_native")
  let resultType ← actualTypeTerm fn.result.coreTy
  let resultCoreType ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeResultType ← termOfExpr fn.result.nativeType
  let resultRepresentation ← termOfExpr fn.result.representation
  let heapPost ← if preserveArrays then
      `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
        Complexity.Language.Buffer.PreservesContents $heap:ident finish)
    else `(fun finish => Complexity.Language.Heap.ShapeExtends $heap:ident finish)
  let declaration (tactics : Array (TSyntax `tactic)) : TermElabM Syntax := do
    let termination ← if model.recursive && !(fn.preservesArrays && !preserveArrays) then
        pure model.termination
      else `(Lean.Parser.Termination.suffix|)
    return (← `(command|
      /-- Successful execution observes the native result in its actual final heap
      and retains every previously represented immutable list. -/
      theorem $relationName:ident $parameters:bracketedBinder* $roots:bracketedBinder*
          ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder*
          :
          ∃ (returned : $resultType) (finish : Complexity.Language.Heap),
            $rawAction $heap:ident = Part.some (.ok returned, finish) ∧
            ($resultRepresentation : Complexity.Language.Representation
              $nativeResultType $resultCoreType).Rel $nativeValue returned finish ∧
            $heapPost finish := by
        $tactics:tactic*
      $termination:suffix)).raw
  if fn.hasExactEquation then
    let equation := fieldName family fn.name "_action_eq_native"
    let mut applied := fn.parameters.map (fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term))
    for parameter in fn.parameters do
      unless parameter.type.isIdentity do applied := applied.push ⟨parameter.rawName.raw⟩
    applied := applied.push ⟨heap.raw⟩ ++ inputRelations.map (·.proof)
    let correct := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
    let value ← encodedValue fn.result nativeValue
    let encoding ← PureImport.encoding fn.result
    let exactEncoding ← encoding.relationSyntax
    let related ← `(($exactEncoding $nativeValue $value $heap:ident).mpr rfl)
    let frame ← if preserveArrays then
        `(And.intro (Complexity.Language.Heap.ShapeExtends.refl $heap:ident)
          (by intro kind view values observed; exact observed))
      else `(Complexity.Language.Heap.ShapeExtends.refl $heap:ident)
    return ← declaration #[← `(tactic|
      exact ⟨$value, $heap:ident, $correct, $related, $frame⟩)]
  if fn.preservesArrays && !preserveArrays then
    let strong := fieldName family fn.name "_action_rel_native_preserving"
    let mut applied := fn.parameters.map (fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term))
    for parameter in fn.parameters do
      unless parameter.type.isIdentity do applied := applied.push ⟨parameter.rawName.raw⟩
    applied := applied.push ⟨heap.raw⟩ ++ inputRelations.map (·.proof)
    let correct := Lean.Syntax.mkApp ⟨strong.raw⟩ applied
    return ← declaration #[
      ← `(tactic| obtain ⟨returned, finish, executed, related, shape, _⟩ := $correct),
      ← `(tactic| exact ⟨returned, finish, executed, related, shape⟩)]
  let mut tactics ← compositionTactics header model
  tactics := tactics.push (← `(tactic| unfold $nativeName:ident))
  tactics := tactics ++ (← relationTrace model.calls model.returned ⟨heap.raw⟩ inputRelations
    #[] preserveArrays ranges (publishRounds := !model.recursive))
  declaration tactics

private partial def inputType : List Parameter → TermElabM (TSyntax `term)
  | [] => `(Unit)
  | [parameter] => termOfExpr parameter.type.nativeType
  | parameter :: rest => do `($(← termOfExpr parameter.type.nativeType) × $(← inputType rest))

private partial def inputRepresentation : List Parameter → TermElabM (TSyntax `term)
  | [] => `(Complexity.Language.ArgumentRepresentation.nil)
  | [parameter] => do
      `(Complexity.Language.ArgumentRepresentation.single $(← termOfExpr parameter.type.representation))
  | parameter :: rest => do
      `(Complexity.Language.ArgumentRepresentation.cons
        $(← termOfExpr parameter.type.representation) $(← inputRepresentation rest))

private def inputFields (count : Nat) (input : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  let mut fields := #[]
  let mut rest := input
  for index in [:count] do
    if index + 1 == count then fields := fields.push rest
    else
      fields := fields.push (← `(Prod.fst $rest))
      rest ← `(Prod.snd $rest)
  return fields

def interfaceDeclarations (names : DeclarationNames) (fn : Function) :
    TermElabM (Array Syntax) := do
  let family := names.publicFamily
  let id := fieldName family fn.name "Id"
  let rawId := fieldName names.sourceFamily fn.name "Id"
  let representation := fieldName family fn.name "_representation"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let result ← termOfExpr (coreTypeExpr fn.result.coreTy)
  let nativeInputType ← inputType fn.parameters.toList
  let nativeResultType ← termOfExpr fn.result.nativeType
  let argumentRepresentation ← inputRepresentation fn.parameters.toList
  let resultRepresentation ← termOfExpr fn.result.representation
  let mut declarations := #[]
  if id.getId != rawId.getId then
    declarations := declarations.push (← `(command|
      abbrev $id:ident := $rawId:ident)).raw
  let representationDeclaration ← `(command|
    /-- Ordinary arguments and the actual result observed in their real source heaps.
    This interface does not assert the existence of a total mathematical model. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $nativeInputType (fun _ => $nativeResultType) { params := [$params,*], result := $result } :=
      Complexity.Language.FunctionRepresentation.ofResult $argumentRepresentation
        (fun _ => $resultRepresentation))
  return declarations.push representationDeclaration.raw

def refinementDeclaration (names : DeclarationNames) (fn : Function) :
    TermElabM Syntax := do
  let family := names.publicFamily
  let program := mkIdentFrom family (family.getId ++ `program)
  let id := fieldName family fn.name "Id"
  let native := modelName names fn.name
  let representation := fieldName family fn.name "_representation"
  let refinement := fieldName family fn.name "_refines"
  let equation := fieldName family fn.name "_action_rel_native"
  let params ← fn.parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let nativeInputType ← inputType fn.parameters.toList
  let input := mkIdent (← mkFreshUserName `input)
  let heap := mkIdent (← mkFreshUserName `heap)
  let represented := mkIdent (← mkFreshUserName `represented)
  let fields ← inputFields fn.parameters.size ⟨input.raw⟩
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ fields
  let mut tactics := #[← `(tactic| intro $input:ident _),
    ← `(tactic| apply Complexity.Language.FunctionTotal.iff_eval.mpr)]
  for parameter in fn.parameters, index in [:fn.parameters.size] do
    let type := params[index]!
    let tail := params.extract (index + 1) params.size
    tactics := tactics.push (← `(tactic|
      refine (Complexity.Language.Env.forall_cons (τ := $type) (Γ := [$tail,*]) _).mpr ?_))
    tactics := tactics.push (← `(tactic| intro $(parameter.rawName):ident))
  tactics := tactics.push (← `(tactic| refine (Complexity.Language.Env.forall_nil _).mpr ?_))
  tactics := tactics.push (← `(tactic| intro $heap:ident $represented:ident))
  let mut relationRest : TSyntax `term := ⟨represented.raw⟩
  let mut rawRoots := #[]
  let mut relations := #[]
  for parameter in fn.parameters, index in [:fn.parameters.size] do
    let sourceRelation ← if index + 1 == fn.parameters.size then pure relationRest
      else `(And.left $relationRest)
    if index + 1 < fn.parameters.size then relationRest ← `(And.right $relationRest)
    let representation ← termOfExpr parameter.type.representation
    let field := fields[index]!
    let relation := parameter.relationName
    tactics := tactics.push (← `(tactic|
      have $relation:ident : ($representation).Rel $field $(parameter.rawName):ident $heap:ident :=
        $sourceRelation))
    match parameter.type with
    | .pure _ | .raw _ =>
        tactics := tactics.push (← `(tactic| change $field = $(parameter.rawName):ident at $relation:ident))
        tactics := tactics.push (← `(tactic| subst $(parameter.rawName):ident))
    | _ =>
        rawRoots := rawRoots.push (⟨parameter.rawName.raw⟩ : TSyntax `term)
        relations := relations.push (⟨relation.raw⟩ : TSyntax `term)
  let applied := fields ++ rawRoots ++ #[⟨heap.raw⟩] ++ relations
  let correct := Lean.Syntax.mkApp ⟨equation.raw⟩ applied
  let returned := mkIdent (← mkFreshUserName `returned)
  let finish := mkIdent (← mkFreshUserName `finish)
  let executed := mkIdent (← mkFreshUserName `executed)
  let observed := mkIdent (← mkFreshUserName `observed)
  tactics := tactics.push (← `(tactic|
    obtain ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident, _⟩ := $correct))
  tactics := tactics.push (← `(tactic| exact ⟨$returned:ident, $finish:ident, $executed:ident, $observed:ident⟩))
  let refinementDeclaration ← `(command|
    /-- Automatic correspondence for the same generated source function, without a machine budget. -/
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $id:ident $representation:ident (fun _ => True)
        (fun ($input:ident : $nativeInputType) => $nativeValue) := by
      $tactics:tactic*)
  return refinementDeclaration.raw

end Internal

end Complexity.Language.Syntax.Represented
