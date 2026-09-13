/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented
import Complexity.Program.Packing
import Lean.Elab.Tactic.Basic

/-!
# Selecting native source functions at a fixed program boundary

`program% Family.function` uses an expected `Complexity.Program α β` to select
a registered native source function with one mathematical argument of type `α`
and result type `β`. Separate fixed input parameters are assembled by actual
`Packing.pair` primitives before a real source call. No input instance is
required when the native declaration itself is registered.

The elaborator checks the mathematical input observation after packing and the
fixed output representation, not merely their core types. Existing native
metadata and checked input instances supply those connections; no additional
record registry or host-side conversion is installed. The added entry and call
have real costs that remain outside this source-correctness interface.

`program_correct Family.function using mathematics` reuses the registered
refinement for this same packed program. The supplied mathematical proof must
establish the caller's actual postcondition; it is never used as an evaluator.

`program_packing% program` exposes the packing already stored in an elaborated
`ofPacking` program for compiler/resource consumers. It does not reconstruct a
second packing or execute the mathematical input convention.
-/

namespace Complexity.Program.Syntax

open Lean Meta Elab Term
open Language
open Language.Syntax.Represented

private inductive PackingTree where
  | input (index : Nat) (type : Ty)
  | pair (left right : PackingTree)

private def PackingTree.type : PackingTree → Ty
  | .input _ type => type
  | .pair left right => .prod left.type right.type

private structure PackingReference where
  index : Nat
  type : Ty
  temporary : Bool := false

private structure PackingStep where
  left : PackingReference
  right : PackingReference

private partial def parameterTypes (types : Expr) : MetaM (Array Expr) := do
  let types ← whnf types
  if types.isAppOfArity ``List.nil 1 then return #[]
  if types.isAppOfArity ``List.cons 3 then
    let arguments := types.getAppArgs
    return #[arguments[1]!] ++ (← parameterTypes arguments[2]!)
  throwError "program% requires a fully resolved fixed input parameter layout"

private partial def packingTree (type : Ty) (parameters : Array Expr) (index : Nat) :
    MetaM (PackingTree × Nat) := do
  if let some parameter := parameters[index]? then
    if ← isDefEq parameter (Language.Syntax.coreTypeExpr type) then
      return (.input index type, index + 1)
  match type with
  | .prod left right =>
      let (left, index) ← packingTree left parameters index
      let (right, index) ← packingTree right parameters index
      return (.pair left right, index)
  | _ =>
      throwError "the fixed input layout cannot assemble native source argument \
        {Language.Syntax.coreTypeExpr type} at parameter {index}"

-- Emit the right subtree first. Every reference below is later translated to
-- its actual lexical variable after the preceding pair bindings.
private def packingSteps : PackingTree → Array PackingStep → PackingReference × Array PackingStep
  | .input index type, steps => (⟨index, type, false⟩, steps)
  | .pair left right, steps =>
      let (rightValue, steps) := packingSteps right steps
      let (leftValue, steps) := packingSteps left steps
      (⟨steps.size, .prod left.type right.type, true⟩,
        steps.push ⟨leftValue, rightValue⟩)

private partial def variableAt (context : List Expr) (index : Nat) : MetaM Expr := do
  match context, index with
  | [], _ => throwError "internal program packing reference is outside its lexical context"
  | head :: tail, 0 =>
      let tailType ← mkListLit (Lean.mkConst ``Language.Ty) tail
      mkAppOptM ``Language.Var.here
        #[some tailType, some head]
  | head :: tail, index + 1 =>
      let sourceVar ← variableAt tail index
      let type := (← inferType sourceVar).getAppArgs[1]!
      let tailType ← mkListLit (Lean.mkConst ``Language.Ty) tail
      mkAppOptM ``Language.Var.there
        #[some tailType, some type, some head, some sourceVar]

private def packingAtom (reference : PackingReference) (position : Nat)
    (context : List Expr) : MetaM Expr := do
  let index := if reference.temporary then position - 1 - reference.index
    else position + reference.index
  let sourceVar ← variableAt context index
  let atom ← mkAppM ``Language.Atom.var #[sourceVar]
  let contextType ← mkListLit (Lean.mkConst ``Language.Ty) context
  let expected ← mkAppM ``Language.Atom
    #[contextType, Language.Syntax.coreTypeExpr reference.type]
  unless ← isDefEq (← inferType atom) expected do
    throwError "internal program packing reference has the wrong source type"
  return atom

private partial def packingTerm (steps : Array PackingStep) (result : PackingReference)
    (position : Nat) (context : List Expr) : MetaM Expr := do
  if let some step := steps[position]? then
    let left ← packingAtom step.left position context
    let right ← packingAtom step.right position context
    let rest ← packingTerm steps result (position + 1)
      (Language.Syntax.coreTypeExpr (.prod step.left.type step.right.type) :: context)
    mkAppM ``Packing.pair #[left, right, rest]
  else
    mkAppM ``Packing.done #[← packingAtom result position context]

private def nativeFunction (name : TSyntax `ident) : TermElabM NativeFunctionInfo := do
  let resolved ← resolveGlobalConstNoOverload name
  let program := resolved.getPrefix ++ `program
  let some functions := getNativeProgramInfo? (← getEnv) program
    | throwErrorAt name "program% requires a registered native source function"
  let some function := functions.find? (fun function => function.nativeName == resolved)
    | throwErrorAt name "no native source metadata is registered for '{resolved}'"
  unless function.parameters.size == 1 do
    throwErrorAt name "program% currently requires one mathematical native input parameter"
  return function

private structure PreparedProgram where
  program : Expr
  source : Expr
  fn : Expr
  same : Expr
  packing : Expr
  inputRepresentation : Expr
  inputProof : Expr
  native : NativeFunctionInfo

private def prepareProgram (name : TSyntax `ident) (expected : Expr) :
    TermElabM PreparedProgram := withRef name do
  let expected ← whnf expected
  unless expected.isAppOfArity ``Complexity.Program 4 do
    throwError "program% requires an expected type Complexity.Program α β"
  let arguments := expected.getAppArgs
  let α := arguments[0]!
  let β := arguments[1]!
  let input := arguments[2]!
  let output := arguments[3]!
  let native ← nativeFunction name
  let some (_, inputType) := native.parameters[0]?
    | throwError "program% requires one mathematical native input parameter"
  unless ← isDefEq α inputType.nativeType do
    throwError "the native input type {inputType.nativeType} does not match {α}"
  unless ← isDefEq β native.result.nativeType do
    throwError "the native result type {native.result.nativeType} does not match {β}"
  synthesizeSyntheticMVarsNoPostponing
  let outputRepresentation ← mkAppOptM ``Output.representation #[some β, some output]
  unless ← isDefEq outputRepresentation native.result.representation do
    throwError "the native result representation does not match the fixed Program.Output \
      observation; matching source types alone do not establish compatibility"
  let parameters ← mkAppOptM ``Input.params #[some α, some input]
  let types ← parameterTypes parameters
  let (tree, consumed) ← packingTree inputType.coreTy types 0
  unless consumed == types.size do
    throwError "the native argument does not consume every fixed input parameter"
  let (result, steps) := packingSteps tree #[]
  let packing ← packingTerm steps result 0 types.toList
  let source := Lean.mkConst (native.sourceFamily ++ `program)
  let fn := Lean.mkConst (native.sourceFamily ++ native.sourceName.appendAfter "Id")
  let outputType ← mkAppOptM ``Output.type #[some β, some output]
  let sourceParameters ← mkListLit (Lean.mkConst ``Language.Ty)
    [Language.Syntax.coreTypeExpr inputType.coreTy]
  let signature ← mkAppM ``Language.Signature.mk
    #[sourceParameters, outputType]
  let same ← mkEqRefl signature
  let program ← mkAppOptM ``ofPacking
    #[some α, some β, some input, some output, none,
      some (Language.Syntax.coreTypeExpr inputType.coreTy), some source, some fn,
      some same, some packing]
  unless ← isDefEq (← inferType program) expected do
    throwError "the packed source entry does not have the requested program interface"
  let inputRepresentation := inputType.representation
  let inputProof ← withLocalDeclD `input α fun x => do
    let args ← mkAppOptM ``Input.args #[some α, some input, some x]
    let heap ← mkAppOptM ``Input.heap #[some α, some input, some x]
    let packed ← mkAppM ``Packing.eval #[packing, args]
    let required ← mkAppM ``Language.Representation.Rel #[inputRepresentation, x, packed, heap]
    let represented ← mkAppOptM ``Input.represented #[some α, some input, some x]
    let proof ← if ← isDefEq (← inferType represented) required then pure represented
      else
        try withoutErrToSorry <| elabTermAndSynthesize (← `(by rfl)) (some required)
        catch _ =>
          throwError "the fixed preloaded input does not establish the native argument \
            representation after executable packing"
    mkLambdaFVars #[x] proof
  return {
    program := ← instantiateMVars program
    source, fn, same, packing, inputRepresentation, inputProof, native }

/-- Select a registered native source function through an actual packing entry
at the expected fixed mathematical program interface. -/
syntax (name := programTerm) "program% " ident : term

@[term_elab programTerm]
def elaborateProgram : TermElab := fun stx expected? => do
  let `(program% $name:ident) := stx | throwUnsupportedSyntax
  let some expected := expected?
    | throwErrorAt stx "program% requires an expected type Complexity.Program α β"
  return (← prepareProgram name expected).program

/-- Read the actual packing artifact from an existing `ofPacking` program.
Non-packed programs are rejected; no source or input transformation is run. -/
syntax (name := programPackingTerm) "program_packing% " term:max : term

@[term_elab programPackingTerm]
def elaborateProgramPacking : TermElab := fun stx expected? => do
  let `(program_packing% $program:term) := stx | throwUnsupportedSyntax
  let program ← elabTermAndSynthesize program none
  let programType ← whnf (← inferType program)
  unless programType.isAppOfArity ``Complexity.Program 4 do
    throwErrorAt stx "program_packing% requires a typed Complexity.Program value"
  let some packed ← whnfUntil program ``ofPacking
    | throwErrorAt stx "program_packing% requires a program defined through Program.ofPacking"
  unless packed.isAppOfArity ``ofPacking 10 do
    throwErrorAt stx "program_packing% could not expose the complete Program.ofPacking application"
  let packing := packed.getAppArgs[9]!
  if let some expected := expected? then
    unless ← isDefEq (← inferType packing) expected do
      throwErrorAt stx "the stored packing does not have the requested type"
  return packing

/-- Prove the mathematical contract of the same packed native source function
using its registered refinement and a caller-supplied mathematical proof. -/
syntax (name := programCorrect) "program_correct " ident " using " term : tactic

elab_rules : tactic
  | `(tactic| program_correct $name:ident using $mathematics:term) =>
      Lean.Elab.Tactic.withMainContext do
        let goal ← Lean.Elab.Tactic.getMainGoal
        let some target ← whnfUntil (← instantiateMVars (← goal.getType)) ``Correct
          | throwError "program_correct expects a Program.Correct goal"
        unless target.isAppOfArity ``Correct 7 do
          throwError "program_correct expects a Program.Correct goal"
        let program := target.getAppArgs[4]!
        let prepared ← prepareProgram name (← inferType program)
        unless ← isDefEq program prepared.program do
          throwError "the goal does not refer to the selected native function's same packing entry"
        let source ← exprToSyntax prepared.source
        let fn ← exprToSyntax prepared.fn
        let same ← exprToSyntax prepared.same
        let packing ← exprToSyntax prepared.packing
        let representation ← exprToSyntax prepared.inputRepresentation
        let inputProof ← exprToSyntax prepared.inputProof
        let function ← exprToSyntax (Lean.mkConst prepared.native.nativeName)
        let valid ← exprToSyntax target.getAppArgs[5]!
        let post ← exprToSyntax target.getAppArgs[6]!
        let refinement := mkCIdent prepared.native.refinement
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          apply Complexity.Program.Correct.of_packing_refines
            $source $fn $same $packing $representation
            (valid := $valid) (post := $post) (function := $function)))
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| exact fun input _ => $refinement input True.intro))
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| exact fun input _ => ($inputProof:term) input))
        let saved ← Lean.Elab.Tactic.saveState
        try
          withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
            Lean.Elab.Tactic.evalTactic (← `(tactic| exact $mathematics:term))
        catch _ =>
          saved.restore
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| exact fun input _ => ($mathematics:term) input))

end Complexity.Program.Syntax
