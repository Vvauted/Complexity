/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Wrapper
import Complexity.Computability.Ram.Compiler.Language.Program.Packing
import Complexity.Computability.Ram.Compiler.Language.Program.Uncurry
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Language.Linking.Extension

/-!
# Composing generated source wrappers from operation certificates

`program_wrapper_measured [certificate, ...]` follows the actual typed source
body through structural bindings and calls, reusing supplied measured operation
certificates. `program_wrapper_cost [certificate, ...]` separately combines
function cost certificates. Both retain real call boundaries and their depth.
Existing `Program.extend` and `Program.link` constructions supply checked table
embeddings; function names, record fields and argument counts are not special
cased. Unsupported loops remain proof obligations.

A cost index may be supplied with `at`. Without it, only the actual source
environment or its ordinary right-associated value tuple is reconstructed and
checked against the certificate's argument function. Mathematical data are not
decoded from pointers, and arbitrary resource indices are not guessed.

The passes reuse the existing arena proof rules and compiler costs. They do not
add an interpreter, synthesize mathematical invariants, or infer resource facts
from the desired answer. Input ranges, current-heap preconditions and numerical
comparisons remain genuine proof obligations when existing facts do not close them.
-/

namespace Complexity.Program.WrapperTactic

open Lean Meta Elab Tactic
open Language Ram.LanguageCompiler

private structure Embedding where
  proof : Lean.Expr
  path : Array Lean.Expr

private partial def findEmbedding? (source target : Lean.Expr) : MetaM (Option Embedding) := do
  if ← withNewMCtxDepth <| isDefEq source target then
    return some ⟨← mkAppM ``Language.Program.Embeds.refl #[source], #[]⟩
  if let some extended ← whnfUntil target ``Language.Program.extend then
    let fields := extended.getAppArgs
    let imported := fields[1]!
    if let some earlier ← findEmbedding? source imported then
      let next ← mkAppM ``Language.Program.embeds_extend
        #[imported, fields[2]!, fields[3]!]
      let proof ← mkAppM ``Language.Program.Embeds.trans #[earlier.proof, next]
      return some ⟨proof, earlier.path.push proof⟩
  if let some linked ← whnfUntil target ``Language.Program.link then
    let fields := linked.getAppArgs
    for side in #[true, false] do
      let imported := fields[if side then 2 else 3]!
      if let some earlier ← findEmbedding? source imported then
        let next ← mkAppM (if side then ``Language.Program.embeds_link_left
          else ``Language.Program.embeds_link_right) #[fields[2]!, fields[3]!]
        let proof ← mkAppM ``Language.Program.Embeds.trans #[earlier.proof, next]
        return some ⟨proof, earlier.path.push proof⟩
  return none

private def bodyFunction? (body : Lean.Expr) : Option Lean.Expr := Id.run do
  let body := body.consumeMData.headBeta.consumeMData
  if body.isAppOf ``Language.Program.body then return some body.getAppArgs[2]!
  if let .proj ``Language.Program 0 _ := body.getAppFn then
    return some body.getAppArgs[0]!
  return none

private def embeddingMap (proof : Lean.Expr) : MetaM Lean.Expr := do
  let type ← instantiateMVars (← inferType proof)
  return type.getAppArgs[3]!

private def matchesFunction (embedding : Lean.Expr) (sourceFn targetFn : Lean.Expr) : MetaM Bool := do
  let mapped ← mkAppM ``Language.SignatureMap.toFun #[← embeddingMap embedding, sourceFn]
  withNewMCtxDepth <| isDefEq mapped targetFn

private partial def environmentValues (types env : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let types ← whnf types
  if types.isAppOf ``List.nil then return #[]
  unless types.isAppOf ``List.cons do
    throwError "the source argument types are not a resolved finite context"
  let head ← mkAppM ``Language.Env.head #[env]
  let tail ← mkAppM ``Language.Env.tail #[env]
  return #[head] ++ (← environmentValues types.getAppArgs[2]! tail)

private def valueTuple : List Lean.Expr → MetaM Lean.Expr
  | [] => pure (mkConst ``Unit.unit)
  | [value] => pure value
  | value :: rest => do mkAppM ``Prod.mk #[value, ← valueTuple rest]

private def rawIndex (type argumentFunction actualArgs : Lean.Expr) : MetaM Lean.Expr := do
  if ← withNewMCtxDepth <| isDefEq type (← inferType actualArgs) then
    if ← withNewMCtxDepth <| isDefEq (mkApp argumentFunction actualArgs) actualArgs then
      return actualArgs
  let envType ← inferType actualArgs
  let values ← environmentValues envType.getAppArgs[0]! actualArgs
  let tuple ← valueTuple values.toList
  unless ← withNewMCtxDepth <| isDefEq type (← inferType tuple) do
    throwError "supply this cost certificate's mathematical resource index with `at`"
  unless ← withNewMCtxDepth <| isDefEq (mkApp argumentFunction tuple) actualArgs do
    throwError "the structural source tuple does not reproduce the certificate arguments; use `at`"
  return tuple

private partial def sourceVariables (types : Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let types ← whnf types
  if types.isAppOf ``List.nil then return #[]
  unless types.isAppOf ``List.cons do return #[]
  let head := types.getAppArgs[1]!
  let tail := types.getAppArgs[2]!
  let here ← mkAppOptM ``Language.Var.here #[some tail, some head]
  let mut values := #[(head, here)]
  for (type, index) in ← sourceVariables tail do
    let lifted ← mkAppOptM ``Language.Var.there
      #[some tail, some type, some head, some index]
    values := values.push (type, lifted)
  return values

/-- Expose range observations already proved for each actual input variable. -/
private def inputRanges : TacticM Unit := withMainContext do
  let locals ← getLCtx
  for declaration in locals do
    let type := declaration.type.consumeMData.headBeta.consumeMData
    unless type.isAppOf ``Ram.LanguageCompiler.EnvFits do continue
    let arguments := type.getAppArgs
    for (type, index) in ← sourceVariables arguments[0]! do
      let proof := mkAppN (mkFVar declaration.fvarId) #[type, index]
      let proof ← Term.exprToSyntax proof
      let name := mkIdent (← mkFreshUserName `inputRange)
      evalTactic (← `(tactic| have $name:ident := $proof))

private def finishLeaves : TacticM Unit := do
  unless (← getGoals).isEmpty do
    Ram.LanguageCompiler.Tactic.normalizeSourceCoordinates
      #[``cast_eq, ``and_true, ``true_and]
    evalTactic (← `(tactic| all_goals try first | assumption | rfl | trivial))

private def recordCosts (embedding : Embedding) (fn : Lean.Expr) : TacticM Unit := do
  for proof in embedding.path do
    let equation ← mkAppM ``Ram.LanguageCompiler.callCost_embeds #[proof, fn]
    let equation ← Term.exprToSyntax equation
    let name := mkIdent (← mkFreshUserName `wrapperCallCost)
    evalTactic (← `(tactic| have $name:ident := $equation))

private def measuredCertificate? (certificates : Array (TSyntax `term))
    (targetProgram fn args continuation entry : Lean.Expr) : TacticM Bool := do
  for certificate in certificates do
    let saved ← saveState
    try
      let proof ← Term.elabTerm certificate none
      let type := (← instantiateMVars (← inferType proof)).consumeMData.headBeta.consumeMData
      unless type.isAppOf ``Ram.LanguageCompiler.ArenaMeasured do
        throwErrorAt certificate "expected an existing measured operation certificate"
      let some sourceFn := bodyFunction? type.getAppArgs[7]!
        | throwErrorAt certificate "the measured operation must select an actual source function body"
      let some embedding ← findEmbedding? type.getAppArgs[1]! targetProgram | continue
      unless ← matchesFunction embedding.proof sourceFn fn do continue
      let embedding ← Term.exprToSyntax embedding.proof
      let sourceFn ← Term.exprToSyntax sourceFn
      let args ← Term.exprToSyntax args
      let continuation ← Term.exprToSyntax continuation
      let entry ← Term.exprToSyntax entry
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_measured_imported
          $embedding (fn := $sourceFn) rfl
          (args := $args) (continuation := $continuation) (entry := $entry)
          ?_ $certificate ?_))
      return true
    catch _ => saved.restore
  return false

private partial def measured (certificates : Array (TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      if target.isForall then
        evalTactic (← `(tactic| intro))
        measured certificates
      else if target.isAppOf ``Ram.LanguageCompiler.ArenaMeasured then
        let statement ← Ram.LanguageCompiler.Tactic.exposeStatement 7
        if statement.isAppOf ``Language.Stmt.call then
          let fields := statement.getAppArgs
          unless ← measuredCertificate? certificates target.getAppArgs[1]!
              fields[3]! fields[4]! fields[5]! target.getAppArgs[9]! do
            evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.call_body))
          Ram.LanguageCompiler.Tactic.onGoals (measured certificates)
        else if #[``Language.Stmt.letPrim, ``Language.Stmt.ret, ``Language.Stmt.skip,
            ``Language.Stmt.assign, ``Language.Stmt.seq, ``Language.Stmt.ite,
            ``Language.Stmt.matchOption].any statement.isAppOf then
          evalTactic (← `(tactic| ram_source_arena_step))
          Ram.LanguageCompiler.Tactic.onGoals (measured certificates)
      else if target.isAppOf ``Exists then
        Tactic.tryCatchRestore (do
          evalTactic (← `(tactic| first | exact ⟨_, rfl⟩ | refine ⟨_, rfl, ?_⟩))
          measured certificates) fun _ => finishLeaves
      else if target.isAppOf ``And then
        evalTactic (← `(tactic| constructor))
        Ram.LanguageCompiler.Tactic.onGoals (measured certificates)
      else
        evalTactic (← `(tactic|
          simp (config := { failIfUnchanged := false }) only [cast_eq]))
        unless (← getGoals).isEmpty do
          evalTactic (← `(tactic| ram_source_arena_step))
        finishLeaves

private structure CostCertificate where
  proof : TSyntax `term
  index : Option (TSyntax `term) := none

private def applyCostRule (rule : TSyntax `term) : TacticM Unit :=
  evalApplyLikeTactic (fun goal proof => do
    let generated ← goal.apply proof
    generated.filterM fun pending => pending.withContext do
      return !(← whnf (← pending.getType)).isConstOf ``Nat) rule.raw

private def costCertificate? (certificates : Array CostCertificate)
    (targetProgram fn args entry : Lean.Expr) : TacticM Bool := do
  for certificate in certificates do
    let saved ← saveState
    let mut matched := false
    try
      let proof ← Term.elabTerm certificate.proof none
      let type := (← instantiateMVars (← inferType proof)).consumeMData.headBeta.consumeMData
      unless type.isAppOf ``Ram.LanguageCompiler.FunctionArenaCostBound do
        throwErrorAt certificate.proof "expected an existing function cost certificate"
      let fields := type.getAppArgs
      let some sourceFn := bodyFunction? fields[5]!
        | throwErrorAt certificate.proof "the cost certificate must select an actual source body"
      let some embedding ← findEmbedding? fields[2]! targetProgram | continue
      unless ← matchesFunction embedding.proof sourceFn fn do continue
      matched := true
      let index ← match certificate.index with
        | some supplied => Term.elabTerm supplied (some fields[0]!)
        | none => do
            let locals ← mkAppM ``Language.State.locals #[entry]
            let actualArgs ← mkAppM ``Language.Args.eval #[args, locals]
            rawIndex fields[0]! fields[6]! actualArgs
      let proof := certificate.proof
      let embedding ← Term.exprToSyntax embedding.proof
      let sourceFn ← Term.exprToSyntax sourceFn
      let index ← Term.exprToSyntax index
      applyCostRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_imported
        $embedding (fn := $sourceFn) $proof $index))
      return true
    catch error =>
      saved.restore
      if matched then throw error
  return false

/-- Treat a call price as an atom except for its nested body budget. In
particular, traversing a numerical goal never inspects a program's bodies. -/
private partial def costAtoms (expression : Lean.Expr) : Array Lean.Expr :=
  let expression := expression.consumeMData
  if expression.isAppOf ``Ram.LanguageCompiler.callCost then
    #[expression] ++ costAtoms expression.getAppArgs[3]!
  else match expression with
    | .app function argument => costAtoms function ++ costAtoms argument
    | .letE _ _ value body _ => costAtoms (body.instantiate1 value)
    | _ => #[]

/-- Specialize existing transport equations to the exact call atoms appearing
in this goal. Finite indices and table lengths select the possible identity
before its program aliases are checked. The resulting simp rules need no
default-transparency search through an entire numerical expression. -/
private def transportCosts (equations : Array Lean.Expr) : TacticM Unit :=
  withMainContext do
    let atoms := costAtoms (← instantiateMVars (← getMainTarget))
    let mut rules := #[]
    for atom in atoms do
      let fields := atom.getAppArgs
      let index ← mkAppM ``Fin.val #[fields[2]!]
      let size ← mkAppM ``List.length #[fields[0]!]
      for equation in equations do
        let proof := mkApp equation fields[3]!
        let type := (← instantiateMVars (← inferType proof)).headBeta
        let some (_, lhs, rhs) := type.eq? | continue
        unless lhs.isAppOf ``Ram.LanguageCompiler.callCost do continue
        let expected := lhs.getAppArgs
        let expectedIndex ← mkAppM ``Fin.val #[expected[2]!]
        let expectedSize ← mkAppM ``List.length #[expected[0]!]
        unless ← withNewMCtxDepth <| isDefEq index expectedIndex do continue
        unless ← withNewMCtxDepth <| isDefEq size expectedSize do continue
        unless ← withNewMCtxDepth <| isDefEq fields[1]! expected[1]! do continue
        let type ← mkEq atom rhs
        let type ← Term.exprToSyntax type
        let proof ← Term.exprToSyntax proof
        let name := mkIdent (← mkFreshUserName `wrapperExactCallCost)
        evalTactic (← `(tactic| have $name:ident : $type := $proof))
        rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $name:ident))
        break
    unless rules.isEmpty do
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [$rules,*]))

/-- Normalize only finite entry indices and source field widths. The lowered
function and its program remain opaque; no instruction list is evaluated. -/
private def normalizeCostMetadata : TacticM Unit := liftMetaTactic fun goal =>
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let target ← Meta.transform target (pre := fun expression => do
      if expression.isAppOf ``Ram.LanguageCompiler.fieldCount then
        return .done (← reduce expression)
      if expression.isAppOf ``Ram.LanguageCompiler.lowerFunc then
        let arguments := expression.getAppArgs
        let fn := arguments[2]!
        let value ← reduce (← mkAppM ``Fin.val #[fn])
        let bound ← reduce (← whnf (← inferType fn)).getAppArgs[0]!
        let fits ← mkAppM ``Fin.isLt #[fn]
        let fn ← mkAppOptM ``Fin.mk #[some bound, some value, some fits]
        return .done (mkAppN expression.getAppFn (arguments.set! 2 fn))
      return .continue)
    return [← goal.replaceTargetDefEq target]

private def finishCosts : TacticM Unit := do
  let numerical ← withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
    pure (target.isAppOf ``LE.le && target.getAppArgs[0]!.isConstOf ``Nat)
  unless numerical do finishLeaves
  unless (← getGoals).isEmpty do
    let (rules, equations) ← withMainContext do
      let mut rules := #[]
      let mut equations := #[]
      for declaration in ← getLCtx do
        if declaration.userName.toString.startsWith "wrapperCallCost" then
          let equation := mkFVar declaration.fvarId
          equations := equations.push equation
          let proof ← Term.exprToSyntax equation
          rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $proof:term))
      pure (rules, equations)
    evalTactic (← `(tactic|
      simp (config := { failIfUnchanged := false }) only
        [Complexity.Program.Packing.callBound, Complexity.Program.Packing.cost,
          Complexity.Program.Uncurry.callBound, Complexity.Program.Uncurry.projectionCost,
          Ram.LanguageCompiler.primCodeSize, $rules,*]))
    Ram.LanguageCompiler.Tactic.onGoals (transportCosts equations)
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false }) only
          [Ram.LanguageCompiler.callCost, Ram.LocalCompiler.Function.callSteps_eq,
            Nat.add_assoc]))
    Ram.LanguageCompiler.Tactic.onGoals normalizeCostMetadata
    evalTactic (← `(tactic| all_goals try omega))

private partial def cost (certificates : Array CostCertificate) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      if target.isForall then
        evalTactic (← `(tactic| intro))
        cost certificates
      else if target.isAppOf ``Ram.LanguageCompiler.StmtArenaCostBound then
        let statement ← Ram.LanguageCompiler.Tactic.exposeStatement 7
        if statement.isAppOf ``Language.Stmt.call then
          let fields := statement.getAppArgs
          unless ← costCertificate? certificates target.getAppArgs[1]!
              fields[3]! fields[4]! target.getAppArgs[8]! do
            applyCostRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_body))
          Ram.LanguageCompiler.Tactic.onGoals (cost certificates)
        else if #[``Language.Stmt.letPrim, ``Language.Stmt.ret, ``Language.Stmt.skip,
            ``Language.Stmt.assign, ``Language.Stmt.seq, ``Language.Stmt.ite,
            ``Language.Stmt.matchOption].any statement.isAppOf then
          evalTactic (← `(tactic| ram_source_arena_cost))
          Ram.LanguageCompiler.Tactic.onGoals (cost certificates)
      else
        finishCosts

/-- Compose actual wrapper bodies with supplied measured operations. Input
range hypotheses are projected once; genuine mathematical leaves remain goals. -/
syntax "program_wrapper_measured" "[" term,* "]" : tactic

declare_syntax_cat wrapperCostCertificate
syntax term (&"at" term)? : wrapperCostCertificate

/-- Compose actual wrapper costs, retaining every call boundary. An optional
`at` supplies a mathematical index that cannot be read from source arguments. -/
syntax "program_wrapper_cost" "[" wrapperCostCertificate,* "]" : tactic

elab_rules : tactic
  | `(tactic| program_wrapper_measured [$certificates:term,*]) => focus do
      inputRanges
      measured certificates.getElems
  | `(tactic| program_wrapper_cost [$certificates:wrapperCostCertificate,*]) => focus do
      let parsed ← certificates.getElems.mapM fun certificate => do
        match certificate with
        | `(wrapperCostCertificate| $proof:term at $index:term) =>
            pure ({ proof, index := some index } : CostCertificate)
        | `(wrapperCostCertificate| $proof:term) => pure ({ proof } : CostCertificate)
        | _ => throwUnsupportedSyntax
      withMainContext do
        let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
        unless target.isAppOf ``Ram.LanguageCompiler.StmtArenaCostBound do
          throwError "program_wrapper_cost expects a statement cost goal"
        for certificate in parsed do
          let proof ← Term.elabTerm certificate.proof none
          let type ← instantiateMVars (← inferType proof)
          if type.isAppOf ``Ram.LanguageCompiler.FunctionArenaCostBound then
            if let some fn := bodyFunction? type.getAppArgs[5]! then
              if let some embedding ← findEmbedding? type.getAppArgs[2]! target.getAppArgs[1]! then
                recordCosts embedding fn
      applyCostRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.mono))
      Ram.LanguageCompiler.Tactic.onGoals (cost parsed)

end Complexity.Program.WrapperTactic
