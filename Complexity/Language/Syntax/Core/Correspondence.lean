/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Pure
import Complexity.Language.RepresentedFunction

/-!
# Generated pure function correspondence and refinement

Constructs checked action/native equations, total contracts and represented refinements for the
optional pure function view. The generated claims concern the same source function and retain
the existing input/result encodings.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def pureCorrespondenceDeclaration (family : TSyntax `ident) (fn : Function)
    (callees : Array Callee) (body : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name "_action_eq_pure"
  let action := actionName family fn.name true
  let equation := generatedName family fn.name "_action_eq"
  let native := generatedName family fn.name ""
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let actualArguments := match fn.nativeView with
    | none => arguments
    | some view => (view.parameterEncodings.zip arguments).map fun (encode, argument) =>
        Lean.Syntax.mkApp encode #[argument]
  let actual := Lean.Syntax.mkApp ⟨action.raw⟩ actualArguments
  let value := Lean.Syntax.mkApp ⟨native.raw⟩ arguments
  let encodedValue := match fn.nativeView with
    | none => value
    | some view => Lean.Syntax.mkApp view.resultEncoding #[value]
  let result ← valueTypeTerm fn.result
  let dependencies := callees.filter fun callee =>
    callee.observation.getId != action.getId &&
      (pureProofElements body).any (fun element => element.raw.hasIdent callee.observation.getId)
  let equations ← dependencies.mapM fun callee => do
    let some equation := callee.pureEquation
      | Macro.throwErrorAt callee.name "a pure source callee must have a correspondence theorem"
    return equation
  let loopRules := (body.sites.filter (·.hasStandardRange)).map fun site => loopMember site "eq_pure"
  let bodyRules := body.sites.map fun site => loopMember site "body_eq"
  let mut type ← `($actual = (pure $encodedValue : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let baseProof : TSyntax `term ← match fn.nativeView with
    | none => `(by
        source_pure_correspondence $value using $equation:ident [$equations:ident,*]
          ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*])
    | some view => `(by
        source_pure_correspondence $value using $equation:ident [$equations:ident,*]
          encodings% [$(view.simplifications):ident,*]
          ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*])
  let mut proof := baseProof
  for (param, index) in fn.params.zipIdx.reverse do
    let parameter := param.name
    let parameterType ← match fn.nativeView with
      | none => valueTypeTerm param.type
      | some view => pure view.parameterTypes[index]!
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    /-- The actual source action terminates with the generated native result and
    preserves every initial heap. Lean's native recursion principle proves this once. -/
    theorem $name:ident : $type := $proof)).raw

def pureRawCorrespondenceDeclaration (family : TSyntax `ident)
    (fn : Function) (view : NativeView) : MacroM Syntax := do
  let name := generatedName family fn.name "_action_eq_pure_raw"
  let action := actionName family fn.name true
  let correspondence := generatedName family fn.name "_action_eq_pure"
  let native := generatedName family fn.name ""
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let rebuilt := (view.parameterRebuilds.zip arguments).map fun (rebuild, argument) =>
    Lean.Syntax.mkApp rebuild #[argument]
  let actual := Lean.Syntax.mkApp ⟨action.raw⟩ arguments
  let value := Lean.Syntax.mkApp view.resultEncoding
    #[Lean.Syntax.mkApp ⟨native.raw⟩ rebuilt]
  let result ← valueTypeTerm fn.result
  let mut type ← `($actual = (pure $value : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof := Lean.Syntax.mkApp ⟨correspondence.raw⟩ rebuilt
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    /-- Observe any raw layout through its checked native reconstruction.
    Reconstruction is proof-side transport, not an additional source operation. -/
    theorem $name:ident : $type := $proof)).raw

def pureTotalDeclaration (family program : TSyntax `ident)
    (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_total"
  let native := generatedName family fn.name ""
  let observed := generatedName family fn.name "_observe"
  let correspondence := generatedName family fn.name
    (if fn.nativeView.isSome then "_action_eq_pure_raw" else "_action_eq_pure")
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let env ← freshProofName fn.name `arguments
  let initial ← freshProofName fn.name `initialHeap
  let finalHeap ← freshProofName fn.name `finalHeap
  let returned ← freshProofName fn.name `value
  let mut remaining ← `($env:ident)
  let mut values := #[]
  for _ in fn.params do
    values := values.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let nativeValues := match fn.nativeView with
    | none => values
    | some view => (view.parameterRebuilds.zip values).map fun (rebuild, value) =>
        Lean.Syntax.mkApp rebuild #[value]
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ nativeValues
  let value := match fn.nativeView with
    | none => nativeValue
    | some view => Lean.Syntax.mkApp view.resultEncoding #[nativeValue]
  return (← `(command|
    /-- Exact total source contract inherited from the generated native function. -/
    theorem $name:ident :
        Complexity.Language.FunctionTotal $program:ident $id:ident (fun _ _ => True)
          (fun $env:ident $initial:ident $returned:ident $finalHeap:ident =>
            $returned:ident = $value ∧ $finalHeap:ident = $initial:ident) := by
      apply Complexity.Language.FunctionTotal.of_eval_eq_pure
        (program := $program:ident) (fn := $id:ident)
        (fun ($env:ident : Complexity.Language.Env $params) => $value)
      · intro $env:ident
        rw [$observed:ident, $correspondence:ident]
      · intro _ _ _
        exact ⟨rfl, rfl⟩)).raw

private def nativeInputType : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `(Unit)
  | [type] => pure type
  | type :: rest => do `($type × $(← nativeInputType rest))

private def nativeInputFields (count : Nat) (input : TSyntax `term) :
    MacroM (Array (TSyntax `term)) := do
  let mut fields := #[]
  let mut rest := input
  for index in [:count] do
    if index + 1 < count then
      fields := fields.push (← `(Prod.fst $rest))
      rest ← `(Prod.snd $rest)
    else
      fields := fields.push rest
  return fields

def nativeRefinementDeclarations (family program : TSyntax `ident)
    (fn : Function) (view : NativeView) : MacroM (Array Syntax) := do
  let inputName := generatedName family fn.name "_inputEmbedding"
  let representation := generatedName family fn.name "_representation"
  let refinement := generatedName family fn.name "_refines"
  let arguments := generatedName family fn.name "_args"
  let native := generatedName family fn.name ""
  let observed := generatedName family fn.name "_observe"
  let correspondence := generatedName family fn.name "_action_eq_pure"
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let result ← typeTerm fn.result
  let inputType ← nativeInputType view.parameterTypes.toList
  let input ← freshProofName fn.name `input
  let left ← freshProofName fn.name `left
  let right ← freshProofName fn.name `right
  let same ← freshProofName fn.name `same
  let raw ← freshProofName fn.name `arguments
  let fields ← nativeInputFields fn.params.size ⟨input.raw⟩
  let encodedFields := (view.parameterEncodings.zip fields).map fun (encode, field) =>
    Lean.Syntax.mkApp encode #[field]
  let rawArguments := Lean.Syntax.mkApp ⟨arguments.raw⟩ encodedFields
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ fields
  let encodedValue := Lean.Syntax.mkApp view.resultEncoding #[nativeValue]
  let mut rawRest ← `($raw:ident)
  let mut equalities := #[]
  for embedding in view.parameterEmbeddings do
    let projection ← `(fun ($raw:ident : Complexity.Language.Env $params) =>
      Complexity.Language.Env.head $rawRest)
    equalities := equalities.push (← `(Function.Embedding.injective $embedding
      (congrArg $projection $same:ident)))
    rawRest ← `(Complexity.Language.Env.tail $rawRest)
  let mut injectivity ← `(Subsingleton.elim $left:ident $right:ident)
  for (equality, index) in equalities.zipIdx.reverse do
    injectivity ← if index + 1 == equalities.size then pure equality
      else `(Prod.ext $equality $injectivity)
  let inputDeclaration ← `(command|
    /-- Canonical proof-side encoding of this function's native arguments.
    It does not insert an uncharged runtime conversion. -/
    def $inputName:ident : $inputType ↪ Complexity.Language.Env $params where
      toFun $input:ident := $rawArguments
      inj' $left:ident $right:ident $same:ident := $injectivity)
  let resultEmbedding := view.resultEmbedding
  let output ← `(fun (_ : $inputType) => $resultEmbedding)
  let model ← `(fun ($input:ident : $inputType) => $nativeValue)
  let representationDeclaration ← `(command|
    /-- Native mathematical arguments and results of this actual source function. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $inputType (fun _ => $(view.resultType))
        { params := $params, result := $result } :=
      Complexity.Language.FunctionRepresentation.ofEmbedding $inputName:ident $output)
  let refinementDeclaration ← `(command|
    /-- The generated ordinary native function describes this same source body. -/
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $id:ident $representation:ident (fun _ => True) $model := by
      change Complexity.Language.RepresentedFunction.Refines $program:ident $id:ident
        (Complexity.Language.FunctionRepresentation.ofEmbedding $inputName:ident $output)
        (fun _ => True) $model
      apply Complexity.Language.RepresentedFunction.Refines.of_encoded_eq_pure
        (program := $program:ident) (fn := $id:ident) (pre := fun _ => True)
        $inputName:ident $output $model
      intro $input:ident _
      change Complexity.Language.Program.eval $program:ident $id:ident $rawArguments =
        pure $encodedValue
      rw [$observed:ident]
      exact $(Lean.Syntax.mkApp ⟨correspondence.raw⟩ fields))
  return #[inputDeclaration.raw, representationDeclaration.raw, refinementDeclaration.raw]

end Core

end Complexity.Language.Syntax
