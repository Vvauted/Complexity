/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Program.Packing
import Lean.Elab.Tactic.Basic

/-!
# Selecting source functions at a fixed program boundary

`program% Family.function` uses an expected `Complexity.Program α β` to select
a registered source function at that fixed mathematical interface. Selection
does not require correctness or a total mathematical model. A declaration whose
original parameters match the fixed input is selected directly, using the original
function index and complete program table. Without a mathematical model, the
fixed input and output instances supply the observations of that raw entry,
even when its header also records mathematical types. The supplied source
contract must establish those fixed observations when correctness is proved.

A represented native function with one structured argument retains the existing
packing path: separate fixed input parameters are assembled by actual
`Packing.pair` primitives before a real source call. No input instance is required
when the native declaration itself is registered.

The elaborator checks the mathematical input observation after packing and the
fixed output representation, not merely their core types. Shared mathematical
headers and checked input instances supply those connections; no additional
record registry or host-side conversion is installed. The added entry and call
have real costs that remain outside this source-correctness interface.

`program_correct Family.function using mathematics` separately reuses the existing pure
total contract or native refinement for the same selected entry. A direct pure
selection creates neither a wrapper nor additional named correspondence theorems.
The mathematical proof must establish the caller's actual postcondition; it is
never used as an evaluator. Curried pure equations can be supplied directly.

When the selected header has no mathematical model, `using` instead supplies an
explicit `RepresentedFunction.Total` contract for the same actual source entry,
domain and postcondition. Direct entries use the fixed function representation;
packed entries use the registered single-argument observation and fixed output
representation. The existing packing bridge transports this contract, including
its actual final heap, without requiring a pure function or a new ABI proof.

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

private structure PreparedPacking where
  source : Expr
  fn : Expr
  same : Expr
  packing : Expr
  inputRepresentation : Expr
  inputProof : Expr
  information : Language.Syntax.FunctionInfo

private structure PreparedDirect where
  information : Language.Syntax.FunctionInfo

private structure PreparedPureCorrect where
  function : Expr
  returns : Expr
  argumentCount : Nat

-- These are actual different source entries, not alternative interpretations
-- of one cost: the direct entry is unchanged; packing installs real source code.
private inductive PreparedEntry where
  | direct (information : PreparedDirect)
  | packed (information : PreparedPacking)

private structure PreparedProgram where
  program : Expr
  entry : PreparedEntry

private def preparePacking (name : TSyntax `ident) (expected : Expr)
    (information : Language.Syntax.FunctionInfo)
    (mathematical : Language.Syntax.MathematicalFunctionInfo) :
    TermElabM PreparedProgram := withRef name do
  let expected ← whnf expected
  unless expected.isAppOfArity ``Complexity.Program 4 do
    throwError "program% requires an expected type Complexity.Program α β"
  let arguments := expected.getAppArgs
  let α := arguments[0]!
  let β := arguments[1]!
  let input := arguments[2]!
  let output := arguments[3]!
  unless mathematical.params.size == 1 do
    throwError "the native packing entry currently requires one mathematical input parameter"
  let some (_, inputType) := mathematical.params[0]?
    | throwError "program% requires one mathematical native input parameter"
  unless ← isDefEq α inputType.nativeType do
    throwError "the native input type {inputType.nativeType} does not match {α}"
  unless ← isDefEq β mathematical.result.nativeType do
    throwError "the native result type {mathematical.result.nativeType} does not match {β}"
  synthesizeSyntheticMVarsNoPostponing
  let outputRepresentation ← mkAppOptM ``Output.representation #[some β, some output]
  unless ← isDefEq outputRepresentation mathematical.result.representation do
    throwError "the native result representation does not match the fixed Program.Output \
      observation; matching source types alone do not establish compatibility"
  let parameters ← mkAppOptM ``Input.params #[some α, some input]
  let types ← parameterTypes parameters
  let (tree, consumed) ← packingTree inputType.coreTy types 0
  unless consumed == types.size do
    throwError "the native argument does not consume every fixed input parameter"
  let (result, steps) := packingSteps tree #[]
  let packing ← packingTerm steps result 0 types.toList
  let some sourceInformation := information.source?
    | throwError "the selected function has no registered source identity"
  let source := Lean.mkConst (sourceInformation.family ++ `program)
  let fn := Lean.mkConst ((sourceInformation.family ++ sourceInformation.name).appendAfter "Id")
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
    entry := .packed { source, fn, same, packing, inputRepresentation, inputProof, information } }

private def mathematicalInputType : List Expr → MetaM Expr
  | [] => pure (Lean.mkConst ``Unit)
  | [type] => pure type
  | type :: rest => do mkAppM ``Prod #[type, ← mathematicalInputType rest]

private def mathematicalInputFields (count : Nat) (input : Expr) : MetaM (Array Expr) := do
  let mut fields := #[]
  let mut rest := input
  for index in [:count] do
    if index + 1 == count then fields := fields.push rest
    else
      fields := fields.push (← mkAppM ``Prod.fst #[rest])
      rest ← mkAppM ``Prod.snd #[rest]
  return fields

private def directLayoutMatches (expected : Expr)
    (information : Language.Syntax.FunctionInfo) : TermElabM Bool := do
  let expected ← whnf expected
  unless expected.isAppOfArity ``Complexity.Program 4 do
    throwError "program% requires an expected type Complexity.Program α β"
  let arguments := expected.getAppArgs
  let inputParameters ← mkAppOptM ``Input.params #[some arguments[0]!, some arguments[2]!]
  let sourceParameters ← mkListLit (Lean.mkConst ``Language.Ty)
    (information.params.map (fun (_, type) => Language.Syntax.coreTypeExpr type)).toList
  unless ← isDefEq inputParameters sourceParameters do return false
  let outputType ← mkAppOptM ``Output.type #[some arguments[1]!, some arguments[3]!]
  isDefEq outputType (Language.Syntax.coreTypeExpr information.result)

private def prepareDirect (name : TSyntax `ident) (expected : Expr)
    (information : Language.Syntax.FunctionInfo) :
    TermElabM PreparedProgram := withRef name do
  let expected ← whnf expected
  unless expected.isAppOfArity ``Complexity.Program 4 do
    throwError "program% requires an expected type Complexity.Program α β"
  let arguments := expected.getAppArgs
  let α := arguments[0]!
  let β := arguments[1]!
  let input := arguments[2]!
  let output := arguments[3]!
  let inputParameters ← mkAppOptM ``Input.params #[some α, some input]
  let sourceParameters ← mkListLit (Lean.mkConst ``Language.Ty)
    (information.params.map (fun (_, type) => Language.Syntax.coreTypeExpr type)).toList
  unless ← isDefEq inputParameters sourceParameters do
    throwError "direct selection requires the original source parameters to match \
      the fixed Program.Input layout"
  let outputType ← mkAppOptM ``Output.type #[some β, some output]
  unless ← isDefEq outputType (Language.Syntax.coreTypeExpr information.result) do
    throwError "the original source result does not match the fixed Program.Output layout"
  if information.model?.isSome then
    if let some mathematical := information.mathematical? then
      let mathematicalInput ← mathematicalInputType (mathematical.params.map (·.2.nativeType)).toList
      unless ← isDefEq α mathematicalInput do
        throwError "the registered mathematical input {mathematicalInput} does not match {α}"
      unless ← isDefEq β mathematical.result.nativeType do
        throwError "the registered mathematical result {mathematical.result.nativeType} does not match {β}"
      let outputRepresentation ← mkAppOptM ``Output.representation #[some β, some output]
      unless ← isDefEq outputRepresentation mathematical.result.representation do
        throwError "the registered result observation does not match the fixed Program.Output"
  let some sourceInformation := information.source?
    | throwError "the selected function has no registered source identity"
  let source := Lean.mkConst (sourceInformation.family ++ `program)
  let fn := Lean.mkConst ((sourceInformation.family ++ sourceInformation.name).appendAfter "Id")
  let signature ← mkAppM ``Language.Signature.mk #[inputParameters, outputType]
  let same ← mkEqRefl signature
  let program ← mkAppOptM ``ofProgram
    #[some α, some β, some input, some output, none, some source, some fn, some same]
  unless ← isDefEq (← inferType program) expected do
    throwError "the original source entry does not have the requested fixed interface"
  return { program := ← instantiateMVars program, entry := .direct { information } }

private def preparePureCorrect (name : TSyntax `ident) (program : Expr)
    (information : Language.Syntax.FunctionInfo) :
    TermElabM PreparedPureCorrect := withRef name do
  let expected ← whnf (← inferType program)
  let arguments := expected.getAppArgs
  let α := arguments[0]!
  let some sourceInformation := information.source?
    | throwError "the selected function has no registered source identity"
  let some model := information.model?
    | throwError "program_correct requires a checked model or a source contract; \
        use Program.Correct.of_functionTotal for an explicit source contract"
  let pureParameters ← match information.nativeHeader with
    | some header => pure (header.params.map (·.type))
    | none => information.params.mapM fun (_, type) => do
        let rawType := mkApp (Lean.mkConst ``Language.Value) (Language.Syntax.coreTypeExpr type)
        pure (← Language.Syntax.resolvePureType rawType)
  let nativeName := model.name
  let sourceName := sourceInformation.family ++ sourceInformation.name
  let function ← withLocalDeclD `input α fun x => do
    let fields ← mathematicalInputFields pureParameters.size x
    let encodedFields := (pureParameters.zip fields).map fun (parameter, field) =>
      mkApp parameter.encoding field
    let encodedArguments := mkAppN (Lean.mkConst (sourceName.appendAfter "_args")) encodedFields
    let actualArguments ← mkAppM ``args #[program, x]
    unless ← isDefEq actualArguments encodedArguments do
      throwError "the fixed input arguments do not supply the pure function's checked \
        mathematical parameter encodings"
    mkLambdaFVars #[x] (mkAppN (Lean.mkConst nativeName) fields)
  let returnsType ← withLocalDeclD `input α fun x => do
    mkForallFVars #[x] (← mkAppM ``Returns #[program, x, mkApp function x])
  let selected ← exprToSyntax program
  let inputName := mkIdent (← mkFreshUserName `input)
  let value := mkIdent (← mkFreshUserName `value)
  let heap := mkIdent (← mkFreshUserName `heap)
  let executed := mkIdent (← mkFreshUserName `executed)
  let related := mkIdent (← mkFreshUserName `related)
  let proof ← if information.nativeHeader.isSome then do
      let some refinementName := model.refinement
        | throwError "program_correct requires the registered pure refinement"
      let refinement := mkCIdent refinementName
      `(by
        intro $inputName:ident
        obtain ⟨$value:ident, $heap:ident, $executed:ident, $related:ident⟩ :=
          Complexity.Language.FunctionTotal.iff_eval.mp
            ($refinement:ident $inputName:ident True.intro)
            (Complexity.Program.args $selected $inputName:ident)
            (Complexity.Program.Input.heap $inputName:ident) (by rfl)
        exact ⟨$value:ident, $heap:ident, $executed:ident, $related:ident⟩)
    else do
      let some totalName := model.total
        | throwError "program_correct requires the registered pure total contract"
      let total := mkCIdent totalName
      `(by
        intro $inputName:ident
        obtain ⟨$value:ident, $heap:ident, $executed:ident, $related:ident⟩ :=
          Complexity.Language.FunctionTotal.iff_eval.mp $total:ident
            (Complexity.Program.args $selected $inputName:ident)
            (Complexity.Program.Input.heap $inputName:ident) True.intro
        exact ⟨$value:ident, $heap:ident, $executed:ident, (And.left $related:ident).symm⟩)
  let returns ← withoutErrToSorry <| elabTermAndSynthesize proof (some returnsType)
  return {
    function := ← instantiateMVars function
    returns := ← instantiateMVars returns
    argumentCount := pureParameters.size }

private def prepareProgram (name : TSyntax `ident) (expected : Expr) :
    TermElabM PreparedProgram := withRef name do
  let resolved ← resolveGlobalConstNoOverload name
  let family := resolved.getPrefix
  let program := family ++ `program
  if let some functions := Language.Syntax.getProgramInfo? (← getEnv) program then
    if let some function := functions.find? (fun function =>
        family ++ function.name == resolved || function.model?.any (·.name == resolved) ||
          function.source?.any (·.action == resolved)) then
      if function.model?.isNone then
        if ← directLayoutMatches expected function then
          return ← prepareDirect name expected function
      if !function.pure then
        if let some mathematical := function.mathematical? then
          if mathematical.params.size == 1 then
            return ← preparePacking name expected function mathematical
      return ← prepareDirect name expected function
  throwError "no source function metadata is registered for '{resolved}'"

/-- Select source code at the expected fixed interface, without asserting
correctness. Original matching entries and real record packing remain distinct. -/
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

/-- Prove the selected source function's contract. With a registered model,
`using` supplies mathematics for its existing correspondence; without a model,
it supplies a represented total contract for the same entry and observations. -/
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
          throwError "the goal does not refer to the same selected source entry"
        let valid ← exprToSyntax target.getAppArgs[5]!
        let post ← exprToSyntax target.getAppArgs[6]!
        let information := match prepared.entry with
          | .direct entry => entry.information
          | .packed entry => entry.information
        if information.model?.isNone then
          match prepared.entry with
          | .direct _ =>
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                exact Complexity.Program.Correct.of_total ($mathematics:term)))
          | .packed entry => do
              let source ← exprToSyntax entry.source
              let fn ← exprToSyntax entry.fn
              let same ← exprToSyntax entry.same
              let packing ← exprToSyntax entry.packing
              let representation ← exprToSyntax entry.inputRepresentation
              let inputProof ← exprToSyntax entry.inputProof
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                apply Complexity.Program.Correct.of_packing_total
                  $source $fn $same $packing $representation
                  (valid := $valid) (post := $post)))
              Lean.Elab.Tactic.evalTactic (← `(tactic| exact $mathematics:term))
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                exact fun input _ => ($inputProof:term) input))
          return ()
        let argumentCount ← match prepared.entry with
          | .packed information => do
              let some model := information.information.model?
                | throwError "program_correct requires a checked model or a source contract; \
                    use Program.Correct.of_functionTotal for an explicit source contract"
              let some refinementName := model.refinement
                | throwError "program_correct requires an existing represented refinement"
              let source ← exprToSyntax information.source
              let fn ← exprToSyntax information.fn
              let same ← exprToSyntax information.same
              let packing ← exprToSyntax information.packing
              let representation ← exprToSyntax information.inputRepresentation
              let inputProof ← exprToSyntax information.inputProof
              let function ← exprToSyntax (Lean.mkConst model.name)
              let refinement := mkCIdent refinementName
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                apply Complexity.Program.Correct.of_packing_refines
                  $source $fn $same $packing $representation
                  (valid := $valid) (post := $post) (function := $function)))
              Lean.Elab.Tactic.evalTactic
                (← `(tactic| exact fun input _ => $refinement input True.intro))
              Lean.Elab.Tactic.evalTactic
                (← `(tactic| exact fun input _ => ($inputProof:term) input))
              pure 1
          | .direct information => do
              unless information.information.pure do
                throwError "program_correct has no automatic mathematical proof view for this \
                  direct source entry; use Program.Correct.of_functionTotal with its actual source contract"
              let information ← preparePureCorrect name prepared.program information.information
              let selected ← exprToSyntax prepared.program
              let function ← exprToSyntax information.function
              let returns ← exprToSyntax information.returns
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                apply (fun (mathematics : ∀ input,
                    $valid input → $post input (($function:term) input)) =>
                  (show Complexity.Program.Correct $selected $valid $post from
                    fun input legal =>
                      ⟨($function:term) input, ($returns:term) input, mathematics input legal⟩))))
              pure information.argumentCount
        let saved ← Lean.Elab.Tactic.saveState
        try
          withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
            Lean.Elab.Tactic.evalTactic (← `(tactic| exact $mathematics:term))
        catch _ =>
          saved.restore
          let input := mkIdent (← mkFreshUserName `input)
          let mut rest : TSyntax `term := ⟨input.raw⟩
          let mut fields : Array (TSyntax `term) := #[]
          for index in [:argumentCount] do
            if index + 1 == argumentCount then fields := fields.push rest
            else
              fields := fields.push (← `(Prod.fst $rest))
              rest ← `(Prod.snd $rest)
          let applied := Lean.Syntax.mkApp mathematics fields
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| exact fun $input:ident _ => ($applied:term)))

end Complexity.Program.Syntax
