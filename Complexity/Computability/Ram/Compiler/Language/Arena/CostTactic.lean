/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Inferring structural arena cost bounds

`ram_source_arena_cost [certificate via embedding, ...]` composes the proved
`StmtArenaCostBound` rules for an actual source body. A certificate is an existing
`FunctionArenaCostBound`; `certificate at index` selects a mathematical input
for a dependent bound and leaves its argument equality and precondition as proof
obligations. Without an index the certificate is uniform. An optional embedding
identifies an imported source program. Calls retain their real target entry and
frame overhead; mathematical indices are not guessed from runtime handles.
`certificate at index using specification` also supplies an existing
`FunctionTotal` proof. Its postcondition describes the actual returned value and
heap in the continuation; correctness and cost preconditions remain separate.

The tactic also introduces a bound in a goal of the form
`{ bound : Nat // ∀ entry, StmtArenaCostBound program w heapLimit depth body entry bound }`.
That metavariable is determined by the structural proofs, not by numerical
search or a second instruction-price interpreter. Conditional and option branches
use the existing maximum rules. Loops and unsupported statements remain goals;
this pass establishes neither termination nor arena readiness.
-/

namespace Ram.LanguageCompiler.Arena.CostTactic

open Lean Meta Elab Tactic

private structure Certificate where
  proof : TSyntax `term
  index : Option (TSyntax `term) := none
  specification : Option (TSyntax `term) := none
  embedding : Option (TSyntax `term) := none

/-- Introduce only the requested bound witness. Its value is determined by
the later statement rules, and is not exposed as an ordinary proof goal. -/
private def inferBound : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  let arguments := target.getAppArgs
  unless target.isAppOf ``Subtype && arguments[0]!.isConstOf ``Nat do
    throwError "expected a subtype of natural-number cost bounds"
  let bound ← mkFreshExprMVar (some arguments[0]!)
  let property ← mkFreshExprMVar (some (mkApp arguments[1]! bound))
  (← getMainGoal).assign (← mkAppOptM ``Subtype.mk
    #[some arguments[0]!, some arguments[1]!, some bound, some property])
  replaceMainGoal [property.mvarId!]

/-- Keep natural bound parameters as inference variables, while preserving all
propositional obligations and unrelated goals. No local Nat is selected by search. -/
private def applyRule (rule : TSyntax `term) : TacticM Unit :=
  evalApplyLikeTactic (fun goal proof => do
    let generated ← goal.apply proof
    generated.filterM fun pending => pending.withContext do
      return !(← whnf (← pending.getType)).isConstOf ``Nat) rule.raw

/-- Read a function entry directly from the supplied certificate's actual body.
This is a metadata fallback for imported indices, not a scan of implementations. -/
private def certificateFunction (certificate : TSyntax `term) : TacticM (TSyntax `term) :=
  withMainContext do
    let proof ← Term.elabTerm certificate none
    let type := (← instantiateMVars (← inferType proof)).consumeMData.headBeta.consumeMData
    unless type.isAppOf ``Ram.LanguageCompiler.FunctionArenaCostBound do
      throwErrorAt certificate "expected a FunctionArenaCostBound certificate"
    let body := type.getAppArgs[5]!.consumeMData.headBeta.consumeMData
    if body.isAppOf ``Complexity.Language.Program.body then
      return ← Term.exprToSyntax body.getAppArgs[2]!
    if let .proj ``Complexity.Language.Program 0 _ := body.getAppFn then
      return ← Term.exprToSyntax body.getAppArgs[0]!
    throwErrorAt certificate "cannot infer the imported entry from this cost certificate"

/-- Try supplied certificates against this actual call, restoring all inference
variables after a mismatch. The chosen certificate remains opaque. -/
private partial def applyCallee (statement : Lean.Expr)
    (certificates : List Certificate) : TacticM Unit := do
  match certificates with
  | [] => throwError "no supplied arena cost certificate applies to this call"
  | certificate :: remaining =>
      Tactic.tryCatchRestore (do
        let bounded := certificate.proof
        match certificate.embedding with
        | none =>
            let fn ← Term.exprToSyntax statement.getAppArgs[3]!
            match certificate.index with
            | none =>
                applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_uniform
                  (fn := $fn) $bounded))
            | some index =>
                match certificate.specification with
                | none =>
                    applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at
                      (fn := $fn) $bounded $index))
                | some specification =>
                    applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_of_spec
                      (fn := $fn) $bounded $specification $index))
        | some embedding =>
            match certificate.index with
            | none =>
                Tactic.tryCatchRestore
                  (applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_uniform_imported
                    $embedding $bounded))) fun _ => do
                      let fn ← certificateFunction bounded
                      applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_uniform_imported
                        $embedding (fn := $fn) $bounded))
            | some index =>
                match certificate.specification with
                | none =>
                    Tactic.tryCatchRestore
                      (applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_imported
                        $embedding $bounded $index))) fun _ => do
                          let fn ← certificateFunction bounded
                          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_imported
                            $embedding (fn := $fn) $bounded $index))
                | some specification =>
                    Tactic.tryCatchRestore
                      (applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_of_spec_imported
                        $embedding $bounded $specification $index))) fun _ => do
                          let fn ← certificateFunction bounded
                          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.call_at_of_spec_imported
                            $embedding (fn := $fn) $bounded $specification $index))) fun error => do
          if remaining.isEmpty then throw error
          applyCallee statement remaining

/-- Traverse only the actual caller syntax. Bounds arise from public theorems;
callee bodies, loop invariants and mathematical conditions are not synthesized. -/
private partial def cost (certificates : List Certificate) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      unless ← isProp target do return
      if target.isForall then
        evalTactic (← `(tactic| intro))
        cost certificates
      else if target.isAppOf ``Ram.LanguageCompiler.StmtArenaCostBound then
        let statement ← Ram.LanguageCompiler.Tactic.exposeStatement 7
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.skip))
        else if statement.isAppOf ``Complexity.Language.Stmt.assign then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.assign))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.ret))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.letPrim))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.seq))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.ite_max))
        else if statement.isAppOf ``Complexity.Language.Stmt.matchOption then
          applyRule (← `(Ram.LanguageCompiler.StmtArenaCostBound.match_max))
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          if certificates.isEmpty then return
          applyCallee statement certificates
        else
          return
        Ram.LanguageCompiler.Tactic.onGoals (cost certificates)
      else
        Ram.LanguageCompiler.Tactic.normalizeSourceCoordinates #[``and_true, ``true_and]
        evalTactic (← `(tactic| all_goals try first | rfl | assumption))

private def start (certificates : List Certificate) : TacticM Unit := focus do
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
    if target.isAppOf ``Subtype then inferBound
  cost certificates

declare_syntax_cat arenaCostCertificate
syntax term:max (&"at" term:max (&"using" term:max)?)? (&"via" term:max)? : arenaCostCertificate

/-- Infer a structural bound using existing arena function certificates.
An optional `at` selects an input-dependent bound; `using` supplies an existing
source specification whose postcondition is available in the continuation.
`via` supplies the actual program embedding for an imported call. -/
syntax "ram_source_arena_cost" ("[" arenaCostCertificate,* "]")? : tactic

private def parseCertificate (stx : TSyntax `arenaCostCertificate) :
    TacticM Certificate := do
  match stx with
  | `(arenaCostCertificate| $proof:term at $index:term using $specification:term
      via $embedding:term) =>
      return {
        proof, index := some index, specification := some specification, embedding := some embedding }
  | `(arenaCostCertificate| $proof:term at $index:term using $specification:term) =>
      return { proof, index := some index, specification := some specification }
  | `(arenaCostCertificate| $proof:term at $index:term via $embedding:term) =>
      return { proof, index := some index, embedding := some embedding }
  | `(arenaCostCertificate| $proof:term at $index:term) =>
      return { proof, index := some index }
  | `(arenaCostCertificate| $proof:term via $embedding:term) =>
      return { proof, embedding := some embedding }
  | `(arenaCostCertificate| $proof:term) => return { proof }
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| ram_source_arena_cost) => start []
  | `(tactic| ram_source_arena_cost [$certificates:arenaCostCertificate,*]) => do
      let parsed ← certificates.getElems.toList.mapM parseCertificate
      start parsed

end Ram.LanguageCompiler.Arena.CostTactic
