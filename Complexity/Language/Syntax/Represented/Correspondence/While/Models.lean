/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.Relation

/-!
# Mathematical observations of actual while locals

These declarations depend only on source bindings and their representations,
not on a pure guard or body trace. Every observation uses the current heap.
Normal rounds and local completion share this model; raw buffer fields retain
handle identity, not an assertion about their contents.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

/-- Actual site names are already resolved; generated declarations remain global. -/
def whileDeclarationName (name : TSyntax `ident) : TSyntax `ident :=
  mkIdentFrom name (`_root_ ++ name.getId)

def WhileLocalRegistration.site (loop : WhileLocalRegistration) : TermElabM ActualWhileSite :=
  match loop.site? with
  | some site => pure site
  | none => throwError "the prepared while has no actual source site"

def WhileLocalRegistration.slots (loop : WhileLocalRegistration) : TermElabM (Array Nat) := do
  let site ← loop.site
  sourceBindingSlots loop.captured site.scope site.scope

def WhileLocalRegistration.select (loop : WhileLocalRegistration) (locals : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let fields ← sourceFields (← loop.site).scope.size locals
  let slots ← loop.slots
  fieldsTerm (← slots.toList.mapM fun slot =>
    match fields[slot]? with
    | some field => pure field
    | none => throwError "the selected while coordinate is outside its actual locals")

/-- Generate heap-indexed local observations without assuming a pure loop model. -/
def whileModelDeclarations (loop : WhileLocalRegistration) : TermElabM (Array Syntax) := do
  let site ← loop.site
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let modelType := member `Model
  let modelRel := member `modelRel
  let localsType := member `Locals
  let stateType ← termOfExpr loop.state.type.nativeType
  let stateCore ← termOfExpr (coreTypeExpr loop.state.type.coreTy)
  let representation ← termOfExpr loop.state.type.representation
  let model := loop.state.name
  let locals := mkIdent (← mkFreshUserName `locals)
  let heap := mkIdent (← mkFreshUserName `heap)
  let related := loop.state.relationName
  let selected ← loop.select ⟨locals.raw⟩
  let mut declarations := #[
    (← `(command|
      /-- Ordinary mathematical values of the loop's lexical source bindings. -/
      abbrev $(whileDeclarationName modelType):ident := $stateType)).raw,
    (← `(command|
      /-- Observe actual locals at the current heap, retaining their real aliases. -/
      def $(whileDeclarationName modelRel):ident ($model:ident : $modelType:ident)
          ($locals:ident : $localsType:ident) ($heap:ident : Complexity.Language.Heap) : Prop :=
        ($representation : Complexity.Language.Representation $stateType $stateCore).Rel
          $model:ident $selected $heap:ident)).raw]
  let fields ← sourceFields site.scope.size ⟨locals.raw⟩
  let positions ← loop.slots
  let makeModel := member `mkModel
  let mut modelParameters : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut modelFields : Array (TSyntax `term) := #[]
  let mut parameterNames : NameSet := {}
  for binding in loop.captured do
    let userName := binding.name.getId.eraseMacroScopes
    let name ← if parameterNames.contains userName then
        pure (mkIdent (← mkFreshUserName userName))
      else pure (mkIdent userName)
    parameterNames := parameterNames.insert userName
    let type ← termOfExpr binding.type.nativeType
    modelParameters := modelParameters.push (← `(bracketedBinder| ($name:ident : $type)))
    modelFields := modelFields.push ⟨name.raw⟩
  declarations := declarations.push (← `(command|
    /-- Assemble mathematical locals using source-variable parameter names. -/
    def $(whileDeclarationName makeModel):ident $modelParameters:bracketedBinder* :
        $modelType:ident := $(← fieldsTerm modelFields.toList))).raw
  let mut used : NameSet := {}
  for binding in loop.captured, position in positions, index in [:loop.captured.size] do
    let fieldName := binding.name.getId.eraseMacroScopes
    unless used.contains fieldName do
      used := used.insert fieldName
      let name := member (Name.mkSimple ("model_rel_" ++ fieldName.toString))
      let projectionName := member (Name.mkSimple ("model_" ++ fieldName.toString))
      let representationName := member (Name.mkSimple (fieldName.toString ++ "_representation"))
      let projection ← fieldProjection loop.captured.size index ⟨model.raw⟩
      let projected ← value [loop.state] projection
      let representation ← termOfExpr binding.type.representation
      let nativeType ← termOfExpr binding.type.nativeType
      let coreType ← termOfExpr (coreTypeExpr binding.type.coreTy)
      let actual := fields[position]!
      declarations := declarations ++ #[
        (← `(command|
          /-- The source-named mathematical value of this local. -/
          def $(whileDeclarationName projectionName):ident ($model:ident : $modelType:ident) :
              $nativeType := $projection)).raw,
        (← `(command|
          /-- The checked representation of this field at its current heap. -/
          abbrev $(whileDeclarationName representationName):ident :
              Complexity.Language.Representation $nativeType $coreType := $representation)).raw]
      let proof ← if loop.state.type.isIdentity then
          `(by
            change $model:ident = $selected at $related:ident
            subst $model:ident
            rfl)
        else
          observationAt projected ⟨heap.raw⟩
            #[⟨related.getId, loop.state.type, ⟨related.raw⟩⟩]
      declarations := declarations.push (← `(command|
        /-- Extract a field's observation without source-coordinate transport. -/
        theorem $(whileDeclarationName name):ident {$model:ident : $modelType:ident}
            {$locals:ident : $localsType:ident} {$heap:ident : Complexity.Language.Heap}
            ($related:ident : $modelRel:ident $model:ident $locals:ident $heap:ident) :
            ($representation : Complexity.Language.Representation $nativeType $coreType).Rel
              $projection $actual $heap:ident := $proof)).raw
  return declarations

end Internal

end Complexity.Language.Syntax.Represented
