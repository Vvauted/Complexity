/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Call
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Structural arena resource proofs

`ram_source_arena_step` composes the existing `ArenaMeasured` rules for primitive
bindings, assignment, sequencing, conditionals, option matches and returns,
stopping at calls.
It reads the actual source statement; clients do not reconstruct argument
environments or continuation states. A known Boolean selects its actual branch;
an unknown Boolean gives two proof obligations, each charging only its own path.
Option matches likewise inspect the actual source value and bind its stored
payload, retaining ranges obtained from the actual callee's readiness proof.

`ram_source_arena_call exact using cost` consumes an actual callee cost witness.
Its optional `via embedded` transports a witness from the original source program.
`ram_source_arena_call measured using certificate` directly composes an existing
returning `ArenaMeasured`, retaining its observations without witness unpacking.
The same optional embedding supports imported measured bodies.
`ram_source_arena_call (index := x) using total, resources, bounded` instead uses
independent source correctness, arena resource and cost contracts. Add
`via embedded` to use contracts for an imported source program. All forms resume
structural reasoning after the call, stopping at the next call.

The contract form exposes the real returned value, heap, cursor and core count,
including the proved bound on that count. Mathematical preconditions, capacity
and final cost comparisons remain ordinary goals. No continuation budget is
guessed, and no callee implementation or instruction-price table is unfolded.
-/

namespace Ram.LanguageCompiler.Arena.Tactic

open Lean Meta Elab Tactic

/-- Project only conjunctions already present in a proof. No auxiliary
proposition or backward search tree is invented to obtain a range fact. -/
private partial def conjunctProof? (target proof : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let type := (← instantiateMVars (← inferType proof)).consumeMData.headBeta.consumeMData
  unless type.isAppOf ``And do return none
  for projection in #[``And.left, ``And.right] do
    let observed ← mkAppM projection #[proof]
    if ← withNewMCtxDepth <| isDefEq (← inferType observed) target then
      return some observed
    if let some found ← conjunctProof? target observed then
      return some found
  return none

/-- Close a leaf by projecting an actual local conjunction, without unfolding
execution certificates or searching for new conjuncts. -/
private def closeConjunct : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  for declaration in ← getLCtx do
    if let some proof ← conjunctProof? target (mkFVar declaration.fvarId) then
      (← getMainGoal).assign proof
      replaceMainGoal []
      return

/-- Simplify source coordinates before unfolding fits predicates. In particular,
an optional node is bounded by its tag, not by an assumed bound on its object id. -/
private def normalizeLeaves : TacticM Unit := do
  evalTactic (← `(tactic|
    simp (config := { failIfUnchanged := false }) (disch := assumption) only
      [Complexity.Language.Atom.eval, Complexity.Language.Args.eval,
        Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there,
        Complexity.Language.Env.head_cons, Complexity.Language.Env.tail_cons,
        Complexity.Language.Env.get_tail,
        Complexity.Language.State.locals_enter, Complexity.Language.State.heap_enter,
        Complexity.Language.State.locals_restore, Complexity.Language.State.heap_restore,
        Complexity.Language.State.locals_cons, Complexity.Language.State.heap_cons,
        Complexity.Language.State.locals_tail, Complexity.Language.State.heap_tail,
        Complexity.Language.State.tail_cons,
        Ram.LanguageCompiler.EnvFits.cons_iff, Ram.LanguageCompiler.EnvFits.empty,
        Ram.LanguageCompiler.ValueFits.option_node, and_true, true_and] at * <;>
      try assumption))
  unless (← getGoals).isEmpty do
    Ram.LanguageCompiler.Tactic.normalizeValues
    evalTactic (← `(tactic|
      all_goals
        (simp (config := { failIfUnchanged := false }) (disch := assumption) only
          [Ram.LanguageCompiler.ValueFits.option_node, and_true, true_and] at * <;>
          try exact Nat.one_lt_two_pow (Nat.ne_of_gt (by assumption)))))
    Ram.LanguageCompiler.Tactic.onGoals closeConjunct
    Ram.LanguageCompiler.Tactic.onGoals do
      Tactic.tryCatchRestore (focusAndDone do
        evalTactic (← `(tactic|
          (repeat' apply And.intro) <;>
            first
            | assumption
            | exact Nat.two_pow_pos _
            | exact Nat.one_lt_two_pow (Nat.ne_of_gt (by assumption))
            | rfl
            | skip))
        Ram.LanguageCompiler.Tactic.onGoals closeConjunct) fun _ => pure ()

/-- Select a branch from its actual condition when reflexivity or a local proof
determines it. Otherwise introduce the two selected-path obligations. -/
private def conditional (statement target : Lean.Expr) : TacticM Unit := do
  let condition ← Term.exprToSyntax statement.getAppArgs[3]!
  let entry ← Term.exprToSyntax target.getAppArgs[9]!
  evalTactic (← `(tactic|
    first
    | refine Ram.LanguageCompiler.ArenaMeasured.iteTrue
        (condition := $condition) (entry := $entry)
        (by first | rfl | assumption) ?_
    | refine Ram.LanguageCompiler.ArenaMeasured.iteFalse
        (condition := $condition) (entry := $entry)
        (by first | rfl | assumption) ?_
    | apply Ram.LanguageCompiler.ArenaMeasured.ite))

/-- Match the actual source option. A known constructor selects one branch;
otherwise cases retain the actual payload and its already-proved word ranges. -/
private def optionMatch (statement target : Lean.Expr) : TacticM Unit := do
  let valueExpr := statement.getAppArgs[4]!
  let entryExpr := target.getAppArgs[9]!
  let value ← Term.exprToSyntax valueExpr
  let entry ← Term.exprToSyntax entryExpr
  let locals ← mkAppM ``Complexity.Language.State.locals #[entryExpr]
  let actual ← Term.exprToSyntax (← whnf
    (← mkAppM ``Complexity.Language.Atom.eval #[valueExpr, locals]))
  evalTactic (← `(tactic|
    first
    | refine Ram.LanguageCompiler.ArenaMeasured.matchNone
        (value := $value) (entry := $entry)
        (by first | rfl | assumption) ?_
    | refine Ram.LanguageCompiler.ArenaMeasured.matchSome
        (value := $value) (entry := $entry)
        (by first | rfl | assumption) ?_ ?_
    | (cases selected : $actual <;>
        simp (config := { failIfUnchanged := false }) only [selected] at * <;>
        first
        | refine Ram.LanguageCompiler.ArenaMeasured.matchNone
            (by first | rfl | assumption) ?_
        | refine Ram.LanguageCompiler.ArenaMeasured.matchSome
            (by first | rfl | assumption) ?_ ?_)))

/-- Apply only structural measured-execution rules, leaving calls and mathematical
observations intact. Non-propositional metavariables are never filled by search. -/
private partial def step : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      unless ← isProp target do return
      if target.isForall then
        evalTactic (← `(tactic| intro))
        step
      else if target.isAppOf ``Ram.LanguageCompiler.ArenaMeasured then
        let statement ← Ram.LanguageCompiler.Tactic.exposeStatement 7
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.skip))
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.assign then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.assign))
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.ret))
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.letPrim))
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.ArenaMeasured.seq))
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          conditional statement target
          Ram.LanguageCompiler.Tactic.onGoals step
        else if statement.isAppOf ``Complexity.Language.Stmt.matchOption then
          optionMatch statement target
          Ram.LanguageCompiler.Tactic.onGoals step
      else
        normalizeLeaves
        -- Normal completion can expose a sequential continuation after reducing
        -- its control match. Re-enter only structural goals, not unchanged math.
        Ram.LanguageCompiler.Tactic.onGoals do
          withMainContext do
            let next := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
            if next.isForall || next.isAppOf ``Ram.LanguageCompiler.ArenaMeasured then
              step

/-- Keep the elaborated source terms themselves when applying the public call
rules. `exprToSyntax` uses typed metavariables, not lossy pretty-printed binders. -/
private def callTerms : TacticM
    (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
    unless target.isAppOf ``Ram.LanguageCompiler.ArenaMeasured do
      throwError "expected an ArenaMeasured goal for an actual source call"
    let statement ← Ram.LanguageCompiler.Tactic.exposeStatement 7
    unless statement.isAppOf ``Complexity.Language.Stmt.call do
      throwError "expected a source call; use ram_source_arena_step for preceding bindings"
    let fn ← Term.exprToSyntax statement.getAppArgs[3]!
    let args ← Term.exprToSyntax statement.getAppArgs[4]!
    let continuation ← Term.exprToSyntax statement.getAppArgs[5]!
    let entry ← Term.exprToSyntax target.getAppArgs[9]!
    return (fn, args, continuation, entry)

/-- Recover an imported function's identity from the actual call and the supplied
table map. Finite-table lookup reduces only signatures and indices, never bodies. -/
private def importedFunction (targetFn embedding : TSyntax `term) : TacticM (TSyntax `term) :=
  withMainContext do
    let proof ← Term.elabTerm embedding none
    let proofType := (← instantiateMVars (← inferType proof)).consumeMData.headBeta.consumeMData
    unless proofType.isAppOf ``Complexity.Language.Program.Embeds do
      throwErrorAt embedding "expected a source-program embedding"
    let source := proofType.getAppArgs[0]!
    let map := proofType.getAppArgs[3]!
    let actual := (← instantiateMVars (← Term.elabTerm targetFn none)).consumeMData
    if actual.isAppOf ``Complexity.Language.SignatureMap.toFun then
      if ← withNewMCtxDepth <| isDefEq actual.getAppArgs[2]! map then
        return ← Term.exprToSyntax actual.getAppArgs[3]!
    let size ← mkAppM ``List.length #[source]
    let some count ← getNatValue? (← whnf size) |
      throwErrorAt embedding "cannot determine the imported source table's finite size"
    for ordinal in [:count] do
      let value := mkNatLit ordinal
      let inBounds ← mkDecideProof (← mkLT value size)
      let candidate ← mkAppOptM ``Fin.mk #[some size, some value, some inBounds]
      let mapped ← mkAppM ``Complexity.Language.SignatureMap.toFun #[map, candidate]
      if ← withNewMCtxDepth <| isDefEq mapped actual then
        return ← Term.exprToSyntax candidate
    throwErrorAt embedding "the current call is not in the supplied source-program embedding"

private def exactCall (cost : TSyntax `term)
    (embedded : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let (fn, args, continuation, entry) ← callTerms
  let costProof ← Term.elabTerm cost none
  let costType := (← instantiateMVars (← inferType costProof)).consumeMData.headBeta.consumeMData
  unless costType.isAppOf ``Ram.LanguageCompiler.ArenaExecutionCost do
    throwErrorAt cost "expected an actual ArenaExecutionCost witness"
  let costArguments := costType.getAppArgs
  let ready := costArguments[costArguments.size - 2]!
  let returnedFits ← Term.exprToSyntax
    (← mkAppM ``Ram.LanguageCompiler.ArenaReady.outcome_fits #[ready])
  evalTactic (← `(tactic|
    (have returnedFits := $returnedFits
     simp only [Ram.LanguageCompiler.ControlFits] at returnedFits)))
  match embedded with
  | none =>
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_exact
          (fn := $fn) (args := $args) (continuation := $continuation) (entry := $entry)
          rfl ?_ $cost ?_))
  | some embedding =>
      let sourceFn ← importedFunction fn embedding
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_exact_imported
          $embedding (fn := $sourceFn) rfl
          (args := $args) (continuation := $continuation) (entry := $entry)
          ?_ $cost ?_))
  Ram.LanguageCompiler.Tactic.onGoals step

private def contractCall (index total resources bounded : TSyntax `term)
    (embedded : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let (fn, args, continuation, entry) ← callTerms
  match embedded with
  | none =>
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_of_contract
          (fn := $fn) rfl $total $resources $bounded
          (args := $args) (continuation := $continuation) (entry := $entry)
          $index ?_ ?_ ?_ ?_ ?_ ?_))
  | some embedding =>
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_of_contract_imported
          $embedding rfl $total $resources $bounded
          (args := $args) (continuation := $continuation) (entry := $entry)
          $index ?_ ?_ ?_ ?_ ?_ ?_))
  Ram.LanguageCompiler.Tactic.onGoals step

private def measuredCall (measured : TSyntax `term)
    (embedded : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let (fn, args, continuation, entry) ← callTerms
  match embedded with
  | none =>
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_measured
          (fn := $fn) (args := $args) (continuation := $continuation) (entry := $entry)
          rfl ?_ $measured ?_))
  | some embedding =>
      let sourceFn ← importedFunction fn embedding
      evalTactic (← `(tactic|
        refine Ram.LanguageCompiler.ArenaMeasured.call_measured_imported
          $embedding (fn := $sourceFn) rfl
          (args := $args) (continuation := $continuation) (entry := $entry)
          ?_ $measured ?_))
  Ram.LanguageCompiler.Tactic.onGoals step

/-- Compose non-loop structural statements in a measured arena execution, leaving
the next call and mathematical obligations for explicit proofs. Conditionals
and option matches preserve the selected path's actual heap, cursor and count. -/
syntax "ram_source_arena_step" : tactic

/-- Compose the current actual source call with an exact callee cost witness,
then process structural statements in its actual continuation. -/
syntax "ram_source_arena_call" "exact" "using" term:max (&"via" term)? : tactic

/-- Compose an existing measured body, retaining its observations at the actual
returned heap, value, cursor and count. An embedding supports imported bodies. -/
syntax "ram_source_arena_call" &"measured" "using" term:max (&"via" term)? : tactic

/-- Compose the current source call using independent correctness, resources and
cost contracts. An optional embedding transports original imported contracts. -/
syntax "ram_source_arena_call" "(" &"index" ":=" term ")" "using"
  term "," term "," term:max (&"via" term)? : tactic

elab_rules : tactic
  | `(tactic| ram_source_arena_step) => step
  | `(tactic| ram_source_arena_call exact using $cost) => exactCall cost none
  | `(tactic| ram_source_arena_call exact using $cost via $embedded) =>
      exactCall cost (some embedded)
  | `(tactic| ram_source_arena_call measured using $certificate) => measuredCall certificate none
  | `(tactic| ram_source_arena_call measured using $certificate via $embedded) =>
      measuredCall certificate (some embedded)
  | `(tactic| ram_source_arena_call (index := $resourceIndex:term) using
      $total, $resources, $bounded) =>
      contractCall resourceIndex total resources bounded none
  | `(tactic| ram_source_arena_call (index := $resourceIndex:term) using
      $total, $resources, $bounded via $embedded) =>
      contractCall resourceIndex total resources bounded (some embedded)

end Ram.LanguageCompiler.Arena.Tactic
