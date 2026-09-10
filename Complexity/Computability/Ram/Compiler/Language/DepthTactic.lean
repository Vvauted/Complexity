/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.DepthBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Structural proofs of source call-depth bounds

`ram_source_depth_intro (args)` introduces ordinary parameters of a
`FunctionDepthBound` goal. It leaves the actual heap, mathematical precondition
and source statement to the author. Function initialization adds no call frame.

`ram_source_depth_step using [recursiveBound, helperBound]` composes the checked
statement rules. Sequential statements and branches use a maximum; a callee
adds one level, while its continuation reuses that capacity. Reads retain their
successful current-heap equations. A known guard selects its actual branch;
otherwise both branches are bounded uniformly. Callee implementations remain
opaque, and their mathematical preconditions remain goals.

The pass infers the structural bound. Use `StmtDepthBound.mono` first when the
requested capacity needs a separate mathematical comparison. Loops and calls
without supplied contracts remain statement goals. State-dependent continuation
bounds can use `StmtDepthBound.call` and `StmtDepthBound.seq_of_post` directly;
the uniform pass does not infer callee postconditions or loop invariants.
-/

namespace Ram.LanguageCompiler.DepthTactic

open Lean Meta Elab Tactic
open Ram.LanguageCompiler.Tactic

/-- Keep natural-number bounds available for inference by subsequent rules,
without exposing them as proof goals that an unrelated local number can fill. -/
private def applyDepthRule (rule : TSyntax `term) : TacticM Unit :=
  evalApplyLikeTactic (fun goal proof => do
    let generated ← goal.apply proof
    generated.filterM fun pending => pending.withContext do
      let type ← whnf (← pending.getType)
      return !type.isConstOf ``Nat) rule.raw

/-- A branch is selected only after its guard is proved; a failed attempt
restores the original goal before trying the other branch or a uniform bound. -/
private def depthBranch : TacticM Unit := do
  let known (rule : Name) : TacticM Unit := do
    applyDepthRule ⟨(mkIdent rule).raw⟩
    focusAndDone do
      normalizeValues
      evalTactic (← `(tactic| all_goals simp_all only [Except.ok.injEq]))
      evalTactic (← `(tactic| all_goals first | assumption | (norm_num; done) | omega))
  Tactic.tryCatchRestore (known ``Ram.LanguageCompiler.StmtDepthBound.ite_true) fun _ => do
    Tactic.tryCatchRestore (known ``Ram.LanguageCompiler.StmtDepthBound.ite_false) fun _ => do
      applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.ite_max))

private def depthCertificates (certificate : TSyntax `term) : List (TSyntax `term) :=
  match certificate with
  | `(term| [$certificates,*]) => certificates.getElems.toList
  | _ => [certificate]

/-- Match named contracts against the actual selected callee. Failed candidates
retain neither speculative preconditions nor metavariable assignments. -/
private partial def applyCalleeDepths (statement : Lean.Expr)
    (certificates : List (TSyntax `term)) : TacticM Unit := do
  match certificates with
  | [] => throwError "no supplied depth certificate applies to this call"
  | certificate :: remaining =>
      Tactic.tryCatchRestore
        (Tactic.tryCatchRestore
          (applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.call_uniform $certificate)))
          fun _ => do
            let fn ← Term.exprToSyntax statement.getAppArgs[3]!
            applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.call_uniform
              (fn := $fn) $certificate)))
        fun error => do
          if remaining.isEmpty then throw error
          applyCalleeDepths statement remaining

private partial def depth (callees : List (TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      unless ← isProp target do
        return
      if target.isForall then
        evalTactic (← `(tactic| intro))
        depth callees
      else if target.isAppOf ``Ram.LanguageCompiler.StmtDepthBound then
        let statement ← exposeStatement 4
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.skip))
        else if statement.isAppOf ``Complexity.Language.Stmt.assign then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.assign))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.ret))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.letPrim))
        else if statement.isAppOf ``Complexity.Language.Stmt.read then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.read_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.write then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.write))
        else if statement.isAppOf ``Complexity.Language.Stmt.slice then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.slice_uniform))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          applyDepthRule (← `(Ram.LanguageCompiler.StmtDepthBound.seq))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          depthBranch
        else if statement.isAppOf ``Complexity.Language.Stmt.while then
          return
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          if callees.isEmpty then
            normalizeValues
            return
          applyCalleeDepths statement callees
        else
          throwError "unsupported source statement in depth proof"
        onGoals (depth callees)
      else
        normalizeValues

private def startDepthIntro (names : Array (TSyntax `ident)) : TacticM Unit := focus do
  let tag ← (← getMainGoal).getTag
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionDepthBound.of_stmt))
  introduceArguments names.toList
  (← getMainGoal).setTag tag

end Ram.LanguageCompiler.DepthTactic

open Lean Elab Tactic

/-- Introduce ordinary parameters for a function's internal call-depth bound.
The actual heap, source precondition and body proof remain goals. -/
syntax (name := ramSourceDepthIntro) "ram_source_depth_intro" (" (" ident* ")")? : tactic

elab_rules : tactic
  | `(tactic| ram_source_depth_intro $[($names:ident*)]?) =>
      Ram.LanguageCompiler.DepthTactic.startDepthIntro (names.getD #[])

/-- Compose existing statement call-depth rules, optionally selecting among
named callee bounds. The same successful source reads remain available, while
mathematical preconditions and loop contracts remain explicit proof goals. -/
syntax (name := ramSourceDepthStep) "ram_source_depth_step" (" using " term:max)? : tactic

elab_rules : tactic
  | `(tactic| ram_source_depth_step) => focus do
      Ram.LanguageCompiler.DepthTactic.depth []
  | `(tactic| ram_source_depth_step using $certificate) => focus do
      Ram.LanguageCompiler.DepthTactic.depth
        (Ram.LanguageCompiler.DepthTactic.depthCertificates certificate)
