/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Lean.Elab.Tactic
import Lean.Meta.Transform
import Mathlib.Tactic.NormNum

/-!
# Structural scalar realization and cost proofs

`ram_source_realize (n limit) using feasible, specification` introduces ordinary
arguments of a `FunctionRealizable` goal and composes the existing realization
rules. The supplied callee contracts stay opaque. The parameter names and the
`using` clause may be omitted. Mathematical ranges, callee preconditions and
call-depth inequalities remain ordinary proof goals.
The initial shared heap is quantified independently of the ordinary arguments;
scopes and calls retain their actual heaps through the existing state rules.

`ram_source_cost (n limit) using calleeBound` composes the existing cost rules,
then compares the derived returning-body bound with the requested bound. It
uses a maximum for branches and uniform continuation bounds at calls, so it
does not require a correctness proof when the bound does not depend on returned
contents. For result-dependent bounds use `StmtCostBound.call` directly.

These tactics only construct proofs with public rules. They do not introduce
an execution semantics, unfold callee bodies or maintain an instruction-price
table. The source frontend does not import this backend module.
-/

namespace Ram.LanguageCompiler.Tactic

open Lean Meta Elab Tactic

/-- Run a structural pass on each current goal, retaining its mathematical leaves. -/
private def onGoals (action : TacticM Unit) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let mut remaining := []
  for goal in goals do
    unless ← goal.isAssigned do
      setGoals [goal]
      action
      remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining

/-- Expose only the selected statement, not recursive callee implementations. -/
private def exposeStatement (position : Nat) : TacticM Lean.Expr := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let arguments := target.getAppArgs
  let statement ← whnf arguments[position]!
  let exposed := mkAppN target.getAppFn (arguments.set! position statement)
  liftMetaTactic fun goal => do
    return [← goal.replaceTargetDefEq exposed]
  return statement

/-- Replace a concrete typed argument environment by ordinary curried values. -/
private partial def introduceArguments (names : List (TSyntax `ident)) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    match target with
    | .forallE _ domain _ _ =>
        if domain.isAppOf ``Complexity.Language.Env then
          let context ← whnf domain.getAppArgs[0]!
          if context.isAppOf ``List.cons then
            evalTactic (← `(tactic|
              refine (Complexity.Language.Env.forall_cons _).mpr ?_))
            match names with
            | name :: rest =>
                evalTactic (← `(tactic| intro $name:ident))
                introduceArguments rest
            | [] =>
                evalTactic (← `(tactic| intro arg))
                introduceArguments []
          else if context.isAppOf ``List.nil then
            unless names.isEmpty do
              throwError "more argument names than source parameters"
            evalTactic (← `(tactic|
              refine (Complexity.Language.Env.forall_nil _).mpr ?_))
        else
          unless names.isEmpty do
            throwError "more argument names than source parameters"
    | _ =>
        unless names.isEmpty do
          throwError "expected a source argument environment"

/-- Reduce only source type indices and signature metadata. In particular, an
opaque callee observation or its implementation is never unfolded here. -/
private def normalizeTypeIndices (expression : Lean.Expr) : MetaM Lean.Expr := do
  let expression ← instantiateMVars expression
  Meta.transform expression (pre := fun expression => do
    if expression.isAppOf ``Complexity.Language.Signature.result then
      return .done (← whnf expression)
    if let .proj ``Complexity.Language.Signature _ _ := expression then
      return .done (← whnf expression)
    if expression.isAppOf ``Complexity.Language.Value ||
        expression.isAppOf ``Ram.LanguageCompiler.valueToNat ||
        expression.isAppOf ``Ram.LanguageCompiler.valueField ||
        expression.isAppOf ``Ram.LanguageCompiler.fieldCount then
      let arguments := expression.getAppArgs
      unless arguments.isEmpty do
        let index ← whnf arguments[0]!
        return .continue (some (mkAppN expression.getAppFn (arguments.set! 0 index)))
    return .continue)

/-- Preserve every local fact while making its source-type indices explicit.
Only definitionally equal expressions produced by weak-head reduction replace
the existing types; this does not use a new semantic or representation theorem. -/
private def normalizeTypeIndicesGoal : TacticM Unit := do
  liftMetaTactic fun initial => do
    let mut goal := initial
    let context ← goal.withContext getLCtx
    for declaration in context do
      let type ← goal.withContext (normalizeTypeIndices declaration.type)
      goal ← goal.replaceLocalDeclDefEq declaration.fvarId type
    let target ← goal.withContext do
      normalizeTypeIndices (← goal.getType)
    return [← goal.replaceTargetDefEq target]

/-- Normalize source values and representation predicates, without unfolding
source correctness contracts or machine execution. -/
private def normalizeValues : TacticM Unit := do
  normalizeTypeIndicesGoal
  evalTactic (← `(tactic|
    (dsimp (config := { failIfUnchanged := false }) only [Complexity.Language.Value] at * <;>
     simp (config := { failIfUnchanged := false }) only
      [Ram.LanguageCompiler.PrimFits, Complexity.Language.Prim.eval,
        Complexity.Language.Atom.eval, Complexity.Language.Args.eval,
        Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there,
        Complexity.Language.Env.head_cons, Complexity.Language.Env.tail_cons,
        Complexity.Language.Env.get_tail,
        Complexity.Language.State.locals_enter, Complexity.Language.State.heap_enter,
        Complexity.Language.State.locals_restore, Complexity.Language.State.heap_restore,
        Complexity.Language.State.locals_cons, Complexity.Language.State.heap_cons,
        Complexity.Language.State.locals_tail, Complexity.Language.State.heap_tail,
        Complexity.Language.State.tail_cons,
        Complexity.Language.Value, Ram.LanguageCompiler.valueToNat,
        Ram.LanguageCompiler.valueField_nat, Ram.LanguageCompiler.valueField_bool,
        Ram.LanguageCompiler.EnvFits.cons_nat_iff,
        Ram.LanguageCompiler.EnvFits.cons_bool_iff,
        Ram.LanguageCompiler.EnvFits.cons_unit_iff,
        Ram.LanguageCompiler.EnvFits.empty,
        decide_eq_true_eq, and_true, true_and] at * <;> try assumption)))

private partial def realize
    (callee : Option (TSyntax `term × TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      if target.isForall then
        evalTactic (← `(tactic| intro))
        realize callee
      else if target.isAppOf ``Ram.LanguageCompiler.RealizationWP then
        let statement ← exposeStatement 6
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.skip_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.ret_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.letPrim_iff]; constructor)))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.seq_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.ite_iff]; split)))
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          match callee with
          | some (feasible, specification) =>
              evalTactic (← `(tactic|
                apply Ram.LanguageCompiler.RealizationWP.call $feasible $specification))
          | none =>
              throwError "supply the callee's realizability and correctness contracts with 'using'"
        else
          throwError "unsupported source statement in realization proof"
        onGoals (realize callee)
      else
        normalizeValues

/-- Introduce a locally inferred bound. Its witness is fixed by subsequent
applications of the existing cost rules, not by a new cost interpreter. -/
private def inferLocalBound : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let arguments := target.getAppArgs
  let bound ← mkFreshExprMVar (some arguments[0]!)
  let proof ← mkFreshExprMVar (some (mkApp arguments[1]! bound))
  goal.assign (← mkAppOptM ``Exists.intro
    #[some arguments[0]!, some arguments[1]!, some bound, some proof])
  replaceMainGoal [proof.mvarId!]
  evalTactic (← `(tactic| constructor))

private partial def cost (callee : Option (TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      if target.isForall then
        evalTactic (← `(tactic| intro))
        cost callee
      else if target.isAppOf ``Exists then
        inferLocalBound
        onGoals (cost callee)
      else if target.isAppOf ``Ram.LanguageCompiler.StmtCostBound then
        let statement ← exposeStatement 4
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.StmtCostBound.skip))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.StmtCostBound.ret))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.StmtCostBound.letPrim))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.StmtCostBound.seq))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.StmtCostBound.ite_max))
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          match callee with
          | some certificate =>
              evalTactic (← `(tactic|
                apply Ram.LanguageCompiler.StmtCostBound.call_uniform $certificate))
          | none =>
              throwError "supply the callee's cost bound with 'using'"
        else
          throwError "unsupported source statement in cost proof"
        onGoals (cost callee)
      else
        normalizeValues
        evalTactic (← `(tactic|
          all_goals
            try norm_num only [Ram.LanguageCompiler.primCodeSize,
              Ram.LanguageCompiler.fieldCount]))

private def startRealization (names : Array (TSyntax `ident))
    (callee : Option (TSyntax `term × TSyntax `term)) : TacticM Unit := focus do
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionRealizable.of_wp))
  introduceArguments names.toList
  realize callee

private def startCost (names : Array (TSyntax `ident))
    (callee : Option (TSyntax `term)) : TacticM Unit := focus do
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionCostBound.of_pointwise))
  introduceArguments names.toList
  cost callee

end Ram.LanguageCompiler.Tactic

open Lean Elab Tactic

/-- Compose scalar realization rules, retaining mathematical range and nesting
goals. Optional names introduce ordinary source parameters; the two supplied
callee facts are its realizability theorem and its source correctness contract. -/
syntax (name := ramSourceRealize) "ram_source_realize" (" (" ident* ")")?
  (" using " term:max ", " term:max)? : tactic

macro_rules
  | `(tactic| ram_source_realize) => `(tactic| ram_source_realize ())
  | `(tactic| ram_source_realize using $feasible, $specification) =>
      `(tactic| ram_source_realize () using $feasible, $specification)

elab_rules : tactic
  | `(tactic| ram_source_realize ($names:ident*)) =>
      Ram.LanguageCompiler.Tactic.startRealization names none
  | `(tactic| ram_source_realize ($names:ident*) using $feasible, $specification) =>
      Ram.LanguageCompiler.Tactic.startRealization names (some (feasible, specification))

/-- Derive a scalar structural cost bound from proved instruction charges and
an optional callee bound, leaving its comparison with the requested budget.
Branch and call-continuation bounds are uniform; no result theorem is required. -/
syntax (name := ramSourceCost) "ram_source_cost" (" (" ident* ")")?
  (" using " term:max)? : tactic

macro_rules
  | `(tactic| ram_source_cost) => `(tactic| ram_source_cost ())
  | `(tactic| ram_source_cost using $certificate) =>
      `(tactic| ram_source_cost () using $certificate)

elab_rules : tactic
  | `(tactic| ram_source_cost ($names:ident*)) =>
      Ram.LanguageCompiler.Tactic.startCost names none
  | `(tactic| ram_source_cost ($names:ident*) using $certificate) =>
      Ram.LanguageCompiler.Tactic.startCost names (some certificate)
