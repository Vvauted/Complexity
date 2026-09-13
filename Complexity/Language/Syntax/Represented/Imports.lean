/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.Syntax.Represented.Types
import Complexity.Language.Buffer.Copy
import Complexity.Language.Representation.Preservation

/-!
# Proved function imports for the represented frontend

Completed represented declarations and completed pure declarations use the
shared source-header registry. The adapters here prepare their checked call
contracts; they install no second registry. A pure import reuses its existing source action and native
correspondence, including correspondences already proved for recursion and
finite iteration. Only proof declarations are added: the callee's source family,
function index and program table are unchanged.

Scalar records, products and options use their checked pure encodings only in
these proofs. Their structural observation is proved equivalent to that encoding
and checked against the callee's registered layout. No inverse of a heap-backed
representation, loader, alternate callee or runtime conversion is introduced.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

/-- Checked ordinary and source identities of a completed callable declaration.
The source name selects the original function; an optional action name only
selects its proof-facing observation when the public name is a pure function. -/
structure NativeFunctionInfo where
  sourceFamily : Name
  sourceName : Name
  nativeName : Name
  parameters : Array (Name × NativeType)
  result : NativeType
  equation : Option Name
  relation : Name
  refinement : Name
  /-- The existing action observation, when distinct from the source call name. -/
  actionName : Option Name := none
  /-- An optional stronger observation preserving all old array contents. -/
  preservingRelation : Option Name := none

private def nativeTypeInfo (type : NativeType) : FunctionTypeInfo :=
  ⟨type.nativeType, type.coreTy, type.representation⟩

/-- Store a completed represented call view in the same registry as every
other source declaration. The temporary adapter retains its actual entry. -/
def registerNativeProgramInfo (family : TSyntax `ident) (headers : Array NativeFunctionInfo) :
    CommandElabM Unit := do
  registerProgramInfo family (headers.map fun header => {
    name := header.sourceName
    params := header.parameters.map (fun (name, type) => (name, type.coreTy))
    result := header.result.coreTy
    source? := some {
      family := header.sourceFamily
      name := header.sourceName
      action := header.actionName.getD (header.sourceFamily ++ header.sourceName) }
    mathematical? := some {
      params := header.parameters.map (fun (name, type) => (name, nativeTypeInfo type))
      result := nativeTypeInfo header.result }
    model? := some {
      name := header.nativeName
      equation := header.equation
      relation := some header.relation
      refinement := some header.refinement
      preservingRelation := header.preservingRelation } })

/-- Check a shared mathematical header against the same source type and value
observation, independently of whether that function has a total native model. -/
def resolveTypeInfo (type : FunctionTypeInfo) : TermElabM NativeType := do
  let resolved ← resolveNativeType type.nativeType
  unless resolved.coreTy == type.coreTy do
    throwError "a represented call view disagrees with its registered source layout"
  unless ← isDefEq resolved.representation type.representation do
    throwError "a represented call view disagrees with its registered observation"
  return resolved

/-- Adapt a checked shared header to the represented proof interface. A raw
contract or mathematical signature alone supplies no total call model. Pure
correspondences use the explicit proof transport below instead. -/
def nativeFunctionInfo? (information : FunctionInfo) : TermElabM (Option NativeFunctionInfo) := do
  if information.pure then return none
  let some source := information.source? | return none
  let some mathematical := information.mathematical? | return none
  let some model := information.model? | return none
  let some relation := model.relation | return none
  let some refinement := model.refinement | return none
  let parameters ← mathematical.params.mapM fun (name, type) => do
    return (name, ← resolveTypeInfo type)
  let result ← resolveTypeInfo mathematical.result
  return some {
    sourceFamily := source.family, sourceName := source.name, nativeName := model.name
    parameters, result, equation := model.equation, relation, refinement
    actionName := if source.action == source.family ++ source.name then none else some source.action
    preservingRelation := model.preservingRelation }

/-- Original source headers and their proved ordinary mathematical call views. -/
structure ImportedPrograms where
  source : Array (Name × Array FunctionInfo) := #[]
  native : Array NativeFunctionInfo := #[]

namespace PureImport

universe u v

/-- Product observations agree with the product of their existing pure encodings. -/
theorem prod_rel {α : Type u} {β : Type v} {τ σ : Ty}
    (left : Representation α τ) (right : Representation β σ)
    (first : α ↪ Value τ) (second : β ↪ Value σ)
    (firstExact : ∀ a value heap, left.Rel a value heap ↔ first a = value)
    (secondExact : ∀ b value heap, right.Rel b value heap ↔ second b = value) :
    ∀ pair value heap, (left.prod right).Rel pair value heap ↔
      (first.prodMap second) pair = value := by
  intro pair value heap
  change (left.Rel pair.1 value.1 heap ∧ right.Rel pair.2 value.2 heap) ↔
    (first pair.1, second pair.2) = value
  rw [firstExact, secondExact]
  constructor
  · rintro ⟨firstEqual, secondEqual⟩
    exact Prod.ext firstEqual secondEqual
  · intro equal
    exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩

/-- Optional observations retain the same absent/present cases as pure encoding. -/
theorem option_rel {α : Type u} {τ : Ty} (representation : Representation α τ)
    (encoding : α ↪ Value τ)
    (exactEncoding : ∀ a value heap, representation.Rel a value heap ↔ encoding a = value) :
    ∀ a value heap, representation.option.Rel a value heap ↔ encoding.optionMap a = value := by
  intro a value heap
  cases a <;> cases value <;>
    simp [Representation.option, Function.Embedding.optionMap, exactEncoding]

/-- A record's direct-field view composes its existing encoding, without a
heap-independent reconstruction of any represented reference. -/
theorem comap_rel {α : Type u} {β : Type v} {τ : Ty}
    (representation : Representation α τ) (view : β ↪ α) (encoding : α ↪ Value τ)
    (exactEncoding : ∀ a value heap, representation.Rel a value heap ↔ encoding a = value) :
    ∀ b value heap, (representation.comap view).Rel b value heap ↔
      (view.trans encoding) b = value := by
  intro b value heap
  exact exactEncoding (view b) value heap

private structure Encoding where
  embedding : Expr
  relation : Expr

private partial def encoding : NativeType → TermElabM Encoding
  | .pure type => pure ⟨type.embedding, type.relationEq⟩
  | .raw type => do
      let nativeType := mkApp (mkConst ``Value) (coreTypeExpr type)
      let embedding ← mkAppM ``Function.Embedding.refl #[nativeType]
      let relation ← withLocalDeclD `value nativeType fun value =>
        withLocalDeclD `raw nativeType fun raw =>
          withLocalDeclD `heap (mkConst ``Heap) fun heap => do
            let proof ← mkAppOptM ``Representation.ofEmbedding_rel
              #[some nativeType, some (coreTypeExpr type), some embedding,
                some value, some raw, some heap]
            mkLambdaFVars #[value, raw, heap] proof
      return ⟨embedding, relation⟩
  | .prod left right => do
      let first ← encoding left
      let second ← encoding right
      return {
        embedding := ← mkAppM ``Function.Embedding.prodMap #[first.embedding, second.embedding]
        relation := ← mkAppM ``prod_rel #[left.representation, right.representation,
          first.embedding, second.embedding, first.relation, second.relation] }
  | .option payload => do
      let inner ← encoding payload
      return {
        embedding := ← mkAppM ``Function.Embedding.optionMap #[inner.embedding]
        relation := ← mkAppM ``option_rel
          #[payload.representation, inner.embedding, inner.relation] }
  | .record _ layout view => do
      let inner ← encoding layout
      return {
        embedding := ← mkAppM ``Function.Embedding.trans #[view, inner.embedding]
        relation := ← mkAppM ``comap_rel
          #[layout.representation, view, inner.embedding, inner.relation] }
  | .array _ | .list _ =>
      throwError "a pure source import cannot encode a heap-backed array or linked list"

private structure Parameter where
  name : TSyntax `ident
  type : NativeType
  rawName : TSyntax `ident
  relationName : TSyntax `ident
  encoding : Encoding

private def checkedType (type : PureType) : TermElabM (NativeType × Encoding) := do
  let native ← resolveNativeType type.nativeType
  unless native.coreTy == type.coreTy do
    throwError "the pure callee and native observation have different source layouts"
  let encoded ← encoding native
  let actual ← mkAppM ``Function.Embedding.toFun #[encoded.embedding]
  unless ← withTransparency .all (isDefEq actual type.encoding) do
    throwError "the native observation does not use the pure callee's checked encoding"
  return (native, encoded)

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

private def refinementDeclaration (family function relation name : Name)
    (parameters : Array Parameter) (result : NativeType) : TermElabM Syntax := do
  let program := mkCIdent (family ++ `program)
  let fn := mkCIdent ((family ++ function).appendAfter "Id")
  let observed := mkCIdent ((family ++ function).appendAfter "_observe")
  let native := mkCIdent (family ++ function)
  let relation := mkCIdent relation
  let name := mkIdent (`_root_ ++ name)
  let params ← parameters.mapM (fun parameter => termOfExpr (coreTypeExpr parameter.type.coreTy))
  let resultTy ← termOfExpr (coreTypeExpr result.coreTy)
  let nativeInput ← inputType parameters.toList
  let nativeOutput ← termOfExpr result.nativeType
  let arguments ← inputRepresentation parameters.toList
  let output ← termOfExpr result.representation
  let input := mkIdent (← mkFreshUserName `input)
  let heap := mkIdent (← mkFreshUserName `heap)
  let represented := mkIdent (← mkFreshUserName `represented)
  let fields ← inputFields parameters.size ⟨input.raw⟩
  let model := Lean.Syntax.mkApp ⟨native.raw⟩ fields
  let mut tactics := #[← `(tactic| intro $input:ident _),
    ← `(tactic| apply Complexity.Language.FunctionTotal.iff_eval.mpr)]
  for parameter in parameters, index in [:parameters.size] do
    let type := params[index]!
    let tail := params.extract (index + 1) params.size
    tactics := tactics.push (← `(tactic|
      refine (Complexity.Language.Env.forall_cons (τ := $type) (Γ := [$tail,*]) _).mpr ?_))
    tactics := tactics.push (← `(tactic| intro $(parameter.rawName):ident))
  tactics := tactics.push (← `(tactic| refine (Complexity.Language.Env.forall_nil _).mpr ?_))
  tactics := tactics.push (← `(tactic| intro $heap:ident $represented:ident))
  let mut remaining : TSyntax `term := ⟨represented.raw⟩
  let mut roots := #[]
  let mut relations := #[]
  for parameter in parameters, index in [:parameters.size] do
    let sourceRelation ← if index + 1 == parameters.size then pure remaining
      else `(And.left $remaining)
    if index + 1 < parameters.size then remaining ← `(And.right $remaining)
    let representation ← termOfExpr parameter.type.representation
    let field := fields[index]!
    let proof := parameter.relationName
    tactics := tactics.push (← `(tactic|
      have $proof:ident : ($representation).Rel $field $(parameter.rawName):ident $heap:ident :=
        $sourceRelation))
    if parameter.type.isPure then
      tactics := tactics.push (← `(tactic| change $field = $(parameter.rawName):ident at $proof:ident))
      tactics := tactics.push (← `(tactic| subst $(parameter.rawName):ident))
    else
      roots := roots.push (⟨parameter.rawName.raw⟩ : TSyntax `term)
      relations := relations.push (⟨proof.raw⟩ : TSyntax `term)
  let invoked := Lean.Syntax.mkApp ⟨relation.raw⟩
    (fields ++ roots ++ #[⟨heap.raw⟩] ++ relations)
  let returned := mkIdent (← mkFreshUserName `returned)
  let finish := mkIdent (← mkFreshUserName `finish)
  let executed := mkIdent (← mkFreshUserName `executed)
  let related := mkIdent (← mkFreshUserName `related)
  tactics := tactics.push (← `(tactic| rw [$observed:ident]))
  tactics := tactics.push (← `(tactic|
    obtain ⟨$returned:ident, $finish:ident, $executed:ident, $related:ident, _⟩ := ($invoked:term)))
  tactics := tactics.push (← `(tactic|
    exact ⟨$returned:ident, $finish:ident, $executed:ident, $related:ident⟩))
  return (← `(command|
    /-- The imported original source function retains this structural native view. -/
    theorem $name:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $fn:ident
        (Complexity.Language.FunctionRepresentation.ofResult
          ($arguments : Complexity.Language.ArgumentRepresentation $nativeInput [$params,*])
          (fun _ => ($output : Complexity.Language.Representation $nativeOutput $resultTy)))
        (fun _ => True) (fun ($input:ident : $nativeInput) => $model) := by
      $tactics:tactic*)).raw

private def declarations (family : Name) (info : FunctionInfo) :
    TermElabM (NativeFunctionInfo × Array Syntax) := do
  let some source := info.source?
    | throwError "a pure import must retain its registered source identity"
  let some model := info.model?
    | throwError "a pure import requires its checked mathematical correspondence"
  let some originalEquation := model.equation
    | throwError "a pure import requires its existing source equation"
  let nativeName := model.name
  let actionName := source.action
  let bridge := family ++ `_representedImports ++ info.name
  let equationName := bridge ++ `action_eq
  let relationName := bridge ++ `action_rel
  let preservingName := bridge ++ `action_rel_preserving
  let refinementName := bridge ++ `refines
  let pureParameters ← match info.nativeHeader with
    | some header => pure (header.params.map fun parameter => (parameter.name.getId, parameter.type))
    | none => info.params.mapM fun (name, type) => do
        return (name, ← resolvePureType (mkApp (mkConst ``Value) (coreTypeExpr type)))
  let pureResult ← match info.nativeHeader with
    | some header => pure header.result
    | none => resolvePureType (mkApp (mkConst ``Value) (coreTypeExpr info.result))
  let parameters ← pureParameters.mapM fun (name, type) => do
    let (type, encoding) ← checkedType type
    return ({
      name := mkIdent name, type, encoding
      rawName := mkIdent (← mkFreshUserName `rawArgument)
      relationName := mkIdent (← mkFreshUserName `argumentObserved) } : Parameter)
  let (result, resultEncoding) ← checkedType pureResult
  let header : NativeFunctionInfo := {
    sourceFamily := family, sourceName := info.name, nativeName, actionName := some actionName
    parameters := parameters.map (fun parameter => (parameter.name.getId, parameter.type))
    result, equation := if result.isPure then some equationName else none
    relation := relationName, refinement := refinementName, preservingRelation := some preservingName }
  if (← getEnv).contains refinementName then return (header, #[])
  let heap := mkIdent (← mkFreshUserName `heap)
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut roots : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut observations : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut rawArguments : Array (TSyntax `term) := #[]
  let nativeArguments : Array (TSyntax `term) := parameters.map fun parameter => ⟨parameter.name.raw⟩
  let mut rootArguments : Array (TSyntax `term) := #[]
  let mut hypotheses : Array (TSyntax `term) := #[]
  let mut equationProof := #[]
  for parameter in parameters do
    let nativeType ← termOfExpr parameter.type.nativeType
    binders := binders.push (← `(bracketedBinder| ($(parameter.name):ident : $nativeType)))
    if parameter.type.isPure then rawArguments := rawArguments.push ⟨parameter.name.raw⟩
    else
      let rawType ← actualTypeTerm parameter.type.coreTy
      let representation ← termOfExpr parameter.type.representation
      let encoded ← termOfExpr (← mkAppM ``Function.Embedding.toFun #[parameter.encoding.embedding])
      let exactEncoding ← termOfExpr parameter.encoding.relation
      let equal := mkIdent (← mkFreshUserName `argumentEncoding)
      roots := roots.push (← `(bracketedBinder| ($(parameter.rawName):ident : $rawType)))
      observations := observations.push (← `(bracketedBinder|
        ($(parameter.relationName):ident : ($representation).Rel
          $(parameter.name):ident $(parameter.rawName):ident $heap:ident)))
      rawArguments := rawArguments.push ⟨parameter.rawName.raw⟩
      rootArguments := rootArguments.push ⟨parameter.rawName.raw⟩
      hypotheses := hypotheses.push ⟨parameter.relationName.raw⟩
      equationProof := equationProof.push (← `(tactic|
        have $equal:ident : $encoded $(parameter.name):ident = $(parameter.rawName):ident :=
          ($exactEncoding $(parameter.name):ident $(parameter.rawName):ident $heap:ident).mp
            $(parameter.relationName):ident))
      equationProof := equationProof.push (← `(tactic| rw [← $equal:ident]))
  let nativeValue := Lean.Syntax.mkApp ⟨(mkCIdent nativeName).raw⟩ nativeArguments
  let rawAction := Lean.Syntax.mkApp ⟨(mkCIdent actionName).raw⟩ rawArguments
  let resultType ← actualTypeTerm result.coreTy
  let resultCore ← termOfExpr (coreTypeExpr result.coreTy)
  let nativeResult ← termOfExpr result.nativeType
  let resultRepresentation ← termOfExpr result.representation
  let encoded ← termOfExpr (← mkAppM ``Function.Embedding.toFun #[resultEncoding.embedding])
  let encodedResult ← `($encoded $nativeValue)
  let exactResult ← termOfExpr resultEncoding.relation
  let original := Lean.Syntax.mkApp
    ⟨(mkCIdent originalEquation).raw⟩ nativeArguments
  equationProof := equationProof.push (← `(tactic| exact congrFun $original $heap:ident))
  let equation := mkIdent (`_root_ ++ equationName)
  let equationDeclaration ← `(command|
    /-- The existing pure correspondence observed at the supplied actual heap. -/
    theorem $equation:ident $binders:bracketedBinder* $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
        $rawAction $heap:ident = Part.some (.ok $encodedResult, $heap:ident) := by
      $equationProof:tactic*)
  let applied := nativeArguments ++ rootArguments ++ #[⟨heap.raw⟩] ++ hypotheses
  let executed := Lean.Syntax.mkApp ⟨(mkCIdent equationName).raw⟩ applied
  let preserving := mkIdent (`_root_ ++ preservingName)
  let preservingDeclaration ← `(command|
    /-- This same pure call preserves the entire heap and therefore every old observation. -/
    theorem $preserving:ident $binders:bracketedBinder* $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
        ∃ (value : $resultType) (finish : Complexity.Language.Heap),
          $rawAction $heap:ident = Part.some (.ok value, finish) ∧
          ($resultRepresentation : Complexity.Language.Representation
            $nativeResult $resultCore).Rel $nativeValue value finish ∧
          (Complexity.Language.Heap.ShapeExtends $heap:ident finish ∧
            Complexity.Language.Buffer.PreservesContents $heap:ident finish) := by
      exact ⟨$encodedResult, $heap:ident, $executed,
        ($exactResult $nativeValue $encodedResult $heap:ident).mpr rfl,
        Complexity.Language.Heap.ShapeExtends.refl $heap:ident,
        by intro kind view values observed; exact observed⟩)
  let relation := mkIdent (`_root_ ++ relationName)
  let strong := Lean.Syntax.mkApp ⟨(mkCIdent preservingName).raw⟩ applied
  let relationDeclaration ← `(command|
    /-- The original pure call has the represented frontend's ordinary result contract. -/
    theorem $relation:ident $binders:bracketedBinder* $roots:bracketedBinder*
        ($heap:ident : Complexity.Language.Heap) $observations:bracketedBinder* :
        ∃ (value : $resultType) (finish : Complexity.Language.Heap),
          $rawAction $heap:ident = Part.some (.ok value, finish) ∧
          ($resultRepresentation : Complexity.Language.Representation
            $nativeResult $resultCore).Rel $nativeValue value finish ∧
          Complexity.Language.Heap.ShapeExtends $heap:ident finish := by
      obtain ⟨value, finish, executed, related, shape, _⟩ := ($strong:term)
      exact ⟨value, finish, executed, related, shape⟩)
  let refinement ← refinementDeclaration family info.name relationName refinementName parameters result
  return (header, #[equationDeclaration.raw, preservingDeclaration.raw,
    relationDeclaration.raw, refinement])

end PureImport

/-- Resolve explicitly imported families. Pure functions acquire checked
relational call views from their existing correspondence; impure raw functions
remain source headers and do not gain an unproved native interpretation. -/
def readRepresentedImports (libraries : Array (TSyntax `ident)) : CommandElabM ImportedPrograms := do
  let mut imports : ImportedPrograms := {}
  for family in libraries do
    let (resolved, functions) ← getProgramInfo family
    imports := { imports with source := imports.source.push (resolved, functions) }
    for info in functions do
      if info.pure then
        let (header, declarations) ← liftTermElabM (PureImport.declarations resolved info)
        unless declarations.isEmpty do elabCommand (mkNullNode declarations)
        imports := { imports with native := imports.native.push header }
      else if let some header ← liftTermElabM (nativeFunctionInfo? info) then
        imports := { imports with native := imports.native.push header }
  return imports

end Complexity.Language.Syntax.Represented
