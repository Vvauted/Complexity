/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.While.Models
import Mathlib.Tactic.Tauto

/-!
# Identity observations of completion locals

A complete collection of identity-represented source fields gives an equivalence
between mathematical locals and the actual visible coordinates. The equivalence
only rearranges product fields and the source coordinate spine's final `Unit`;
it does not reconstruct heap-backed contents or change executable statements.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

/-- Equality describes visible locals exactly when identity fields cover every
actual visible slot. This does not assert anything about raw handles' contents. -/
def WhileLocalRegistration.hasIdentityVisible (loop : WhileLocalRegistration) :
    TermElabM Bool := do
  unless loop.captured.all (·.type.isIdentity) do return false
  let site ← loop.site
  let slots ← loop.slots
  let visibleSlots := (site.scope.zipIdx.filter (fun (binding, _) => !binding.privatePending)).map (·.2)
  return slots.size == visibleSlots.size && visibleSlots.all slots.contains

private def visibleCases (count : Nat) (locals : TSyntax `ident) :
    TermElabM (Array (TSyntax `tactic)) := do
  let mut steps := #[]
  let mut current := locals
  for _ in [:count] do
    let field := mkIdent (← mkFreshUserName `field)
    let tail := mkIdent (← mkFreshUserName `tail)
    steps := steps.push (← `(tactic| rcases $current:ident with ⟨$field:ident, $tail:ident⟩))
    current := tail
  return steps.push (← `(tactic| cases $current:ident))

private def modelCases (count : Nat) (model : TSyntax `ident) :
    TermElabM (Array (TSyntax `tactic)) := do
  if count == 0 then return #[← `(tactic| cases $model:ident)]
  let mut steps := #[]
  let mut current := model
  for _ in [:count - 1] do
    let field := mkIdent (← mkFreshUserName `field)
    let tail := mkIdent (← mkFreshUserName `tail)
    steps := steps.push (← `(tactic| rcases $current:ident with ⟨$field:ident, $tail:ident⟩))
    current := tail
  return steps

/-- Generate the exact local-coordinate equivalence when every visible field
uses an identity representation. The legacy constructor observation is retained. -/
def completionIdentityDeclarations (loop : WhileLocalRegistration) :
    TermElabM (Array Syntax) := do
  unless ← loop.hasIdentityVisible do return #[]
  let site ← loop.site
  let slots ← loop.slots
  let visibleSlots := (site.scope.zipIdx.filter (fun (binding, _) => !binding.privatePending)).map (·.2)
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let name := member `visibleModelRel_mkModel_iff
  let relation := member `visibleModelRel
  let modelRel := member `modelRel
  let makeModel := member `mkModel
  let modelType := member `Model
  let visibleType := member `Visible
  let entry := member `entry
  let equivalence := member `modelEquiv
  let model := mkIdent (← mkFreshUserName `model)
  let locals := mkIdent (← mkFreshUserName `locals)
  let heap := mkIdent (← mkFreshUserName `heap)
  let mut parameters : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut arguments : Array (TSyntax `term) := #[]
  for binding in loop.captured do
    let name := mkIdent (← mkFreshUserName binding.name.getId)
    let type ← termOfExpr binding.type.nativeType
    parameters := parameters.push (← `(bracketedBinder| ($name:ident : $type)))
    arguments := arguments.push ⟨name.raw⟩
  let constructed := Lean.Syntax.mkApp ⟨makeModel.raw⟩ arguments
  let rawFields ← visibleSlots.mapM fun slot => do
    let some index := slots.findIdx? (· == slot)
      | throwError "the visible source slot has no identity field"
    pure arguments[index]!
  let rawTuple ← sourceTuple rawFields
  let destruct ← visibleCases visibleSlots.size locals
  let mut declarations := #[(← `(command|
    /-- A complete identity local view is exactly the original visible coordinates.
    Raw handles contribute equality only; contents remain heap-dependent contracts. -/
    @[simp] theorem $(whileDeclarationName name):ident $parameters:bracketedBinder*
        ($locals:ident : $visibleType:ident) ($heap:ident : Complexity.Language.Heap) :
        $relation:ident $constructed $locals:ident $heap:ident ↔ $locals:ident = $rawTuple := by
      $destruct:tactic*
      simp [$relation:ident, $modelRel:ident, $makeModel:ident, $entry:ident,
        Complexity.Language.Representation.prod, Complexity.Language.Representation.ofEmbedding,
        Complexity.Language.Representation.nat, Complexity.Language.Representation.bool,
        Complexity.Language.Representation.unit, eq_comm, and_assoc, and_left_comm, and_comm]
      all_goals tauto)).raw]
  let modelFields ← (List.range loop.captured.size).toArray.mapM fun index =>
    fieldProjection loop.captured.size index ⟨model.raw⟩
  let toVisible ← sourceTuple (← visibleSlots.mapM fun slot => do
    let some index := slots.findIdx? (· == slot)
      | throwError "the visible source slot has no identity field"
    pure modelFields[index]!)
  let visibleFields ← sourceFields visibleSlots.size ⟨locals.raw⟩
  let fromVisible ← fieldsTerm (← slots.toList.mapM fun slot => do
    let some index := visibleSlots.findIdx? (· == slot)
      | throwError "the mathematical identity field has no visible source slot"
    pure visibleFields[index]!)
  let leftProof := (← modelCases loop.captured.size model).push (← `(tactic| rfl))
  let rightProof := destruct.push (← `(tactic| rfl))
  let forward := member `modelEquiv_mkModel
  let backward := member `modelEquiv_symm_tuple
  declarations := declarations ++ #[
    (← `(command|
      /-- Rearrange complete identity locals into their actual visible source order. -/
      def $(whileDeclarationName equivalence):ident : $modelType:ident ≃ $visibleType:ident where
        toFun := fun $model:ident => $toVisible
        invFun := fun $locals:ident => $fromVisible
        left_inv := by
          intro $model:ident
          $leftProof:tactic*
        right_inv := by
          intro $locals:ident
          $rightProof:tactic*)).raw,
    (← `(command|
      /-- A named mathematical constructor has the corresponding visible coordinates. -/
      @[simp] theorem $(whileDeclarationName forward):ident $parameters:bracketedBinder* :
          $equivalence:ident $constructed = $rawTuple := rfl)).raw,
    (← `(command|
      /-- Actual visible coordinates reconstruct the named mathematical locals. -/
      @[simp] theorem $(whileDeclarationName backward):ident $parameters:bracketedBinder* :
          ($equivalence:ident).symm $rawTuple = $constructed := rfl)).raw]
  let checked := mkIdent (← mkFreshUserName `checked)
  let constructorProof := Lean.Syntax.mkApp ⟨name.raw⟩
    (modelFields ++ #[⟨locals.raw⟩, ⟨heap.raw⟩])
  let relationProof := (← modelCases loop.captured.size model).push (← `(tactic|
    simpa only [$equivalence:ident, Equiv.coe_fn_mk, $makeModel:ident] using $checked:ident))
  let iffName := member `visibleModelRel_iff
  declarations := declarations.push (← `(command|
    /-- Complete identity observations coincide with the proved coordinate equivalence. -/
    theorem $(whileDeclarationName iffName):ident ($model:ident : $modelType:ident)
        ($locals:ident : $visibleType:ident) ($heap:ident : Complexity.Language.Heap) :
        $relation:ident $model:ident $locals:ident $heap:ident ↔
          $locals:ident = $equivalence:ident $model:ident := by
      have $checked:ident := $constructorProof
      $relationProof:tactic*)).raw
  return declarations

end Internal

end Complexity.Language.Syntax.Represented
