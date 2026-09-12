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
# Structural realization and cost proofs

`ram_source_realize (n limit) using feasible, specification` introduces ordinary
arguments of a `FunctionRealizable` goal and composes the existing realization
rules. The supplied callee contracts stay opaque. The parameter names and the
`using` clause may be omitted. Mathematical ranges, callee preconditions and
call-depth inequalities remain ordinary proof goals.
The initial shared heap is quantified independently of the ordinary arguments;
scopes and calls retain their actual heaps through the existing state rules.
Buffer reads and writes expose successful current-heap operations and the actual
read values or updated heaps. Slices expose their relative extent. These are
mathematical proof obligations, not inferred validity or alias assumptions.

`ram_source_cost (n limit) using calleeBound` composes the existing cost rules,
then compares the derived returning-body bound with the requested bound. It
selects a branch when its condition follows from source values and local facts,
and otherwise uses a maximum for both branches. A call can omit its source
contract only when the continuation needs no facts about the callee's result
or final heap. Even a uniform numeric bound may need those facts to justify a
later call's precondition. An explicit `next` function on `ram_source_call`
also supports a result-dependent numerical bound.
Reads retain their actual successful read equations, so mathematical contents
can identify values used in a branch or a later callee's precondition.
`using [recursiveBound, helperBound]` supplies several named cost certificates;
the pass selects one for the actual callee and keeps its own precondition.
It does not construct a dependent function table or assume that precondition.

`ram_source_cost_intro (n limit)` only introduces ordinary source parameters
and the existing function-body cost rule. It leaves the heap, mathematical
precondition and statement proof to the author, without unpacking `Env` by hand.
The requested bound must have the rule's `core + 2` shape; the full
`ram_source_cost` pass also supports an arbitrary budget via a comparison goal.

`ram_source_realize_step` and `ram_source_cost_step` run the same structural
passes on statement-level goals, without introducing a function contract or
unpacking function arguments. They accept the same optional callee facts.
Loop contracts remain goals for explicit invariant and potential rules; neither
pass unfolds a loop or a recursive callee implementation.

Without `using`, the passes stop at calls. `ram_source_call using resource,
specification` applies the supplied contracts to just the current call, then
resumes structural reasoning until the next call. For realization, `resource`
is the callee's realizability contract; for costs it is the callee's cost bound.
The source specification carries actual return values and final-heap facts to
the continuation. A standalone call followed by another statement stays intact
until these facts are available, instead of taking a uniform sequence bound.

These tactics only construct proofs with public rules. They do not introduce
an execution semantics, unfold callee bodies or maintain an instruction-price
table. The source frontend does not import this backend module.

`ram_source_call (next := fun value heap => remainingBound) using cost, total`
uses a genuinely value- and heap-dependent continuation bound. It leaves the
continuation proof and final bound comparison under the same supplied
postcondition, with actual returned values and heaps introduced. Use the usual
statement pass after selecting any mathematical cases needed by that bound.
-/

namespace Ram.LanguageCompiler.Tactic

open Lean Meta Elab Tactic

/-- Run a structural pass on each current goal, retaining its mathematical leaves. -/
def onGoals (action : TacticM Unit) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let mut remaining := []
  for goal in goals do
    unless ← goal.isAssigned do
      setGoals [goal]
      action
      remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining

/-- Expose only the selected statement, not recursive callee implementations. -/
def exposeStatement (position : Nat) : TacticM Lean.Expr := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  let arguments := target.getAppArgs
  let statement ← whnf arguments[position]!
  let exposed := mkAppN target.getAppFn (arguments.set! position statement)
  liftMetaTactic fun goal => do
    return [← goal.replaceTargetDefEq exposed]
  return statement

/-- Recognize the existing standalone-call syntax without unfolding a callee's
implementation. Its following statement must retain the actual returned heap. -/
private def isStandaloneCallSeq (statement : Lean.Expr) : MetaM Bool := do
  unless statement.isAppOf ``Complexity.Language.Stmt.seq do
    return false
  let first ← whnf statement.getAppArgs[3]!
  unless first.isAppOf ``Complexity.Language.Stmt.call do
    return false
  let continuation ← whnf first.getAppArgs[5]!
  return continuation.isAppOf ``Complexity.Language.Stmt.skip

/-- Replace a concrete typed argument environment by ordinary curried values. -/
partial def introduceArguments (names : List (TSyntax `ident)) : TacticM Unit :=
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
        expression.isAppOf ``Complexity.Language.CellValue ||
        expression.isAppOf ``Ram.LanguageCompiler.fieldCount then
      let arguments := expression.getAppArgs
      unless arguments.isEmpty do
        let index ← whnf arguments[0]!
        return .continue (some (mkAppN expression.getAppFn (arguments.set! 0 index)))
    if expression.isAppOf ``Ram.LanguageCompiler.ValueFits then
      let arguments := expression.getAppArgs
      if arguments.size > 1 then
        let index ← whnf arguments[1]!
        return .continue (some (mkAppN expression.getAppFn (arguments.set! 1 index)))
    return .continue)

/-- Preserve every local fact while making its source-type indices explicit.
Only definitionally equal expressions produced by weak-head reduction replace
the existing types; this does not use a new semantic or representation theorem. -/
private def normalizeTypeIndicesGoal : TacticM Unit := do
  liftMetaTactic fun initial => do
    let mut goal := initial
    let context ← goal.withContext getLCtx
    for declaration in context do
      let type ← goal.withContext do
        -- Expose reducible argument transports such as generated `f_onArgs`,
        -- without opening source predicates or execution contracts.
        normalizeTypeIndices (← withReducible (whnf declaration.type))
      goal ← goal.replaceLocalDeclDefEq declaration.fvarId type
    let target ← goal.withContext do
      normalizeTypeIndices (← withReducible (whnf (← goal.getType)))
    return [← goal.replaceTargetDefEq target]

/-- Shared source-coordinate reductions. These do not unfold range predicates,
source contracts, compiled code or native equivalence records. -/
def sourceCoordinateRules : Array Name := #[
  ``Complexity.Language.Prim.eval, ``Complexity.Language.Atom.eval,
  ``Complexity.Language.Args.eval,
  ``Complexity.Language.Env.cons_here, ``Complexity.Language.Env.cons_there,
  ``Complexity.Language.Env.head_cons, ``Complexity.Language.Env.tail_cons,
  ``Complexity.Language.Env.get_tail, ``Complexity.Language.Env.set_here,
  ``Complexity.Language.Env.set_there,
  ``Complexity.Language.State.locals_enter, ``Complexity.Language.State.heap_enter,
  ``Complexity.Language.State.locals_restore, ``Complexity.Language.State.heap_restore,
  ``Complexity.Language.State.locals_cons, ``Complexity.Language.State.heap_cons,
  ``Complexity.Language.State.locals_tail, ``Complexity.Language.State.heap_tail,
  ``Complexity.Language.State.locals_set, ``Complexity.Language.State.heap_set,
  ``Complexity.Language.State.tail_cons,
  ``Complexity.Language.Value, ``Complexity.Language.CellValue,
  ``Complexity.Language.CellTy.toValue, ``Complexity.Language.CellTy.ofValue,
  ``Complexity.Language.CellTy.toTy]

private def coordinateSimpArgs (rules : Array Name) :
    TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  rules.mapM fun rule => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent rule):ident)

/-- Normalize only source coordinates at the requested ordinary Lean location.
Additional rules must be checked coordinate declarations selected by the caller.
No local context traversal or assumption/range solver is performed. -/
def normalizeSourceCoordinates (additional : Array Name := #[])
    (location : Option (TSyntax ``Lean.Parser.Tactic.location) := none) : TacticM Unit := do
  let rules ← coordinateSimpArgs (sourceCoordinateRules ++ additional)
  evalTactic (← `(tactic|
    simp (config := { failIfUnchanged := false }) only [$rules,*] $[$location]?))

/-- Normalize source values and representation predicates, without unfolding
source correctness contracts or machine execution. -/
def normalizeValues : TacticM Unit := do
  normalizeTypeIndicesGoal
  let rules ← coordinateSimpArgs (#[``Ram.LanguageCompiler.PrimFits] ++
    sourceCoordinateRules ++ #[``Ram.LanguageCompiler.ValueFits,
      ``Ram.LanguageCompiler.EnvFits.cons_nat_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_bool_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_unit_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_buffer_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_prod_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_none_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_some_iff,
      ``Ram.LanguageCompiler.EnvFits.cons_iff,
      ``Ram.LanguageCompiler.EnvFits.empty,
      ``decide_eq_true_eq, ``and_true, ``true_and])
  evalTactic (← `(tactic|
    (dsimp (config := { failIfUnchanged := false }) only
       [Complexity.Language.Value, Complexity.Language.CellValue] at * <;>
     simp (config := { failIfUnchanged := false }) only [$rules,*] at * <;> try assumption)))

private partial def realize
    (callee : Option (TSyntax `term × TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      if target.isForall then
        evalTactic (← `(tactic| intro))
        realize callee
      else if target.isAppOf ``Ram.LanguageCompiler.RealizationWP then
        let statement ← exposeStatement 6
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.skip_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.assign then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.assign_iff]; constructor)))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.ret_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.letPrim_iff]; constructor)))
        else if statement.isAppOf ``Complexity.Language.Stmt.read then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.RealizationWP.read_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.readNode then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.RealizationWP.readNode_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.write then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.RealizationWP.write_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.slice then
          evalTactic (← `(tactic| apply Ram.LanguageCompiler.RealizationWP.slice_of_bound))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          evalTactic (← `(tactic| rw [Ram.LanguageCompiler.RealizationWP.seq_iff]))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.ite_iff]; split)))
        else if statement.isAppOf ``Complexity.Language.Stmt.matchOption then
          evalTactic (← `(tactic|
            (rw [Ram.LanguageCompiler.RealizationWP.matchOption_iff]
             split <;> try apply And.intro)))
        else if statement.isAppOf ``Complexity.Language.Stmt.while then
          return
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          match callee with
          | some (feasible, specification) =>
              evalTactic (← `(tactic|
                apply Ram.LanguageCompiler.RealizationWP.call $feasible $specification))
          | none =>
              normalizeValues
              return
        else
          throwError "unsupported source statement in realization proof"
        onGoals (realize callee)
      else
        normalizeValues

/-- Introduce a locally inferred bound. Its witness is fixed by subsequent
applications of the existing cost rules, not by a new cost interpreter. -/
private def inferLocalBound : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  let arguments := target.getAppArgs
  let bound ← mkFreshExprMVar (some arguments[0]!)
  let proof ← mkFreshExprMVar (some (mkApp arguments[1]! bound))
  goal.assign (← mkAppOptM ``Exists.intro
    #[some arguments[0]!, some arguments[1]!, some bound, some proof])
  replaceMainGoal [proof.mvarId!]
  evalTactic (← `(tactic| constructor))

/-- Apply a structural cost rule, retaining its natural bound parameters for
inference by the continuation proof. These parameters are not ordinary goals
that an unrelated local natural number may solve. All proposition obligations,
other data goals and pre-existing sibling goals remain visible. -/
private def applyCostRule (rule : TSyntax `term) (normalizeCallBound := false) : TacticM Unit :=
  evalApplyLikeTactic (fun goal proof => do
    let proof ← if normalizeCallBound then do
      -- A selected cost family can be constant in the actual arguments even
      -- when its unreduced application mentions values introduced by a read.
      -- This fallback removes that artificial dependency only after ordinary
      -- application fails, preserving existing certificates' presentation.
      let type ← Meta.transform (← inferType proof) (pre := fun expression => do
        if expression.isAppOfArity ``Ram.LanguageCompiler.callCost 4 then
          let arguments := expression.getAppArgs
          let reduced ← whnf arguments[3]!
          let reduced := match reduced.rawNatLit? with
            | some value => mkNatLit value
            | none => reduced
          let bodyBound ← Meta.transform reduced (post := fun expression => do
            -- Keep the standard addition presentation (`Nat.add_eq`) expected
            -- by arithmetic tactics and existing cost consumers.
            if expression.isAppOfArity ``Nat.add 2 then
              return .done (← mkAppM ``HAdd.hAdd expression.getAppArgs)
            return .done expression)
          return .done (mkAppN expression.getAppFn (arguments.set! 3 bodyBound))
        return .continue)
      mkExpectedTypeHint proof type
    else pure proof
    let generated ← goal.apply proof
    generated.filterM fun pending => pending.withContext do
      let type ← whnf (← pending.getType)
      return !type.isConstOf ``Nat) rule.raw

/-- Select a known branch only after its guard proof is complete. An unresolved
condition leaves the original uniform rule available, with no speculative
branch choice or proof obligation retained from the failed attempt. -/
private def costBranch (optionMatch := false) : TacticM Unit := do
  let known (rule : Name) : TacticM Unit := do
    applyCostRule ⟨(mkIdent rule).raw⟩
    focusAndDone do
      normalizeValues
      evalTactic (← `(tactic| all_goals simp_all only [Except.ok.injEq, Option.some.injEq]))
      evalTactic (← `(tactic| all_goals first | assumption | (norm_num; done) | omega))
  let first := if optionMatch then ``Ram.LanguageCompiler.StmtCostBound.match_none
    else ``Ram.LanguageCompiler.StmtCostBound.ite_true
  let second := if optionMatch then ``Ram.LanguageCompiler.StmtCostBound.match_some
    else ``Ram.LanguageCompiler.StmtCostBound.ite_false
  let fallback := if optionMatch then ``Ram.LanguageCompiler.StmtCostBound.match_max
    else ``Ram.LanguageCompiler.StmtCostBound.ite_max
  Tactic.tryCatchRestore (known first) fun _ => do
    Tactic.tryCatchRestore (known second) fun _ => do
      applyCostRule ⟨(mkIdent fallback).raw⟩

private def costCertificates (certificate : TSyntax `term) : List (TSyntax `term) :=
  match certificate with
  | `(term| [$certificates,*]) => certificates.getElems.toList
  | _ => [certificate]

/-- Select a supplied contract by the actual call, retaining its mathematical
precondition and bound. Failed candidates leave no metavariable assignments. -/
private partial def applyCalleeCosts (statement : Lean.Expr)
    (certificates : List (TSyntax `term)) : TacticM Unit := do
  match certificates with
  | [] => throwError "no supplied cost certificate applies to this call"
  | certificate :: remaining =>
      Tactic.tryCatchRestore
        (Tactic.tryCatchRestore
          (applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.call_uniform $certificate)))
          fun _ => do
            let fn ← Term.exprToSyntax statement.getAppArgs[3]!
            applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.call_uniform
              (fn := $fn) $certificate)) (normalizeCallBound := true))
        fun error => do
          if remaining.isEmpty then throw error
          applyCalleeCosts statement remaining

private partial def cost (callees : List (TSyntax `term)) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      -- Unresolved bound parameters are data, not proof obligations. Leave them
      -- for cost certificates to infer instead of choosing a local Nat by assumption.
      unless ← isProp target do
        return
      if target.isForall then
        evalTactic (← `(tactic| intro))
        cost callees
      else if target.isAppOf ``Exists then
        inferLocalBound
        onGoals (cost callees)
      else if target.isAppOf ``Ram.LanguageCompiler.StmtCostBound then
        let statement ← exposeStatement 4
        if statement.isAppOf ``Complexity.Language.Stmt.skip then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.skip))
        else if statement.isAppOf ``Complexity.Language.Stmt.assign then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.assign))
        else if statement.isAppOf ``Complexity.Language.Stmt.ret then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.ret))
        else if statement.isAppOf ``Complexity.Language.Stmt.letPrim then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.letPrim))
        else if statement.isAppOf ``Complexity.Language.Stmt.read then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.read_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.readNode then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.readNode_of_success))
        else if statement.isAppOf ``Complexity.Language.Stmt.write then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.write))
        else if statement.isAppOf ``Complexity.Language.Stmt.slice then
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.slice_uniform))
        else if statement.isAppOf ``Complexity.Language.Stmt.seq then
          if callees.isEmpty && (← isStandaloneCallSeq statement) then
            normalizeValues
            return
          applyCostRule (← `(Ram.LanguageCompiler.StmtCostBound.seq))
        else if statement.isAppOf ``Complexity.Language.Stmt.ite then
          costBranch
        else if statement.isAppOf ``Complexity.Language.Stmt.matchOption then
          costBranch (optionMatch := true)
        else if statement.isAppOf ``Complexity.Language.Stmt.while then
          return
        else if statement.isAppOf ``Complexity.Language.Stmt.call then
          if callees.isEmpty then
            normalizeValues
            return
          applyCalleeCosts statement callees
        else
          throwError "unsupported source statement in cost proof"
        onGoals (cost callees)
      else
        normalizeValues
        evalTactic (← `(tactic|
          all_goals
            try norm_num only [Ram.LanguageCompiler.primCodeSize,
              Ram.LanguageCompiler.readCodeSize, Ram.LanguageCompiler.writeCodeSize,
              Ram.LanguageCompiler.readNodeCodeSize,
              Ram.LanguageCompiler.sliceCodeSize,
              Ram.LanguageCompiler.fieldCount]))

/-- Introduce the actual outcome and its postcondition without traversing a
continuation whose supplied numerical bound may require mathematical cases. -/
private partial def prepareCostLeaf : TacticM Unit := do
  unless (← getGoals).isEmpty do
    withMainContext do
      let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
      if target.isForall then
        evalTactic (← `(tactic| intro))
        prepareCostLeaf
      else
        normalizeValues

/-- Consume one explicitly selected pair of contracts. Subsequent calls are
left for their own contracts, even when they name the same source function. -/
private def sourceCall (resource specification : TSyntax `term)
    (nextBound : Option (TSyntax `term) := none) : TacticM Unit := focus do
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
    if target.isAppOf ``Ram.LanguageCompiler.RealizationWP then
      unless nextBound.isNone do
        throwError "a numerical continuation bound requires a source cost goal"
      let statement ← exposeStatement 6
      unless statement.isAppOf ``Complexity.Language.Stmt.call do
        throwError "expected a source call; use 'ram_source_realize_step' to reach the next call"
      evalTactic (← `(tactic|
        apply Ram.LanguageCompiler.RealizationWP.call $resource $specification))
      onGoals (realize none)
    else if target.isAppOf ``Ram.LanguageCompiler.StmtCostBound then
      let statement ← exposeStatement 4
      if ← isStandaloneCallSeq statement then
        match nextBound with
        | none => applyCostRule (← `(
            Ram.LanguageCompiler.StmtCostBound.call_seq_uniform $resource $specification))
        | some next => applyCostRule (← `(
            Ram.LanguageCompiler.StmtCostBound.call_seq
              (nextBound := $next) $resource $specification))
      else if statement.isAppOf ``Complexity.Language.Stmt.call then
        match nextBound with
        | none => applyCostRule (← `(
            Ram.LanguageCompiler.StmtCostBound.call_of_spec $resource $specification))
        | some next => applyCostRule (← `(
            Ram.LanguageCompiler.StmtCostBound.call_of_spec_le
              (nextBound := $next) $resource $specification))
      else
        throwError "expected a source call; use 'ram_source_cost_step' to reach the next call"
      if nextBound.isSome then onGoals prepareCostLeaf else onGoals (cost [])
    else
      throwError "expected a RealizationWP or StmtCostBound goal at a source call"

private def startRealization (names : Array (TSyntax `ident))
    (callee : Option (TSyntax `term × TSyntax `term)) : TacticM Unit := focus do
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionRealizable.of_wp))
  introduceArguments names.toList
  realize callee

private def startCost (names : Array (TSyntax `ident))
    (callees : List (TSyntax `term)) : TacticM Unit := focus do
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionCostBound.of_pointwise))
  introduceArguments names.toList
  cost callees

private def startCostIntro (names : Array (TSyntax `ident)) : TacticM Unit := focus do
  let tag ← (← getMainGoal).getTag
  evalTactic (← `(tactic| apply Ram.LanguageCompiler.FunctionCostBound.of_stmt))
  introduceArguments names.toList
  normalizeTypeIndicesGoal
  -- Do not leak the helper's `body` case into a following `have ... := by`.
  (← getMainGoal).setTag tag

end Ram.LanguageCompiler.Tactic

open Lean Elab Tactic

/-- Compose realization rules, retaining mathematical heap, range and nesting
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

/-- Derive a structural cost bound from proved instruction charges and
an optional callee bound, leaving its comparison with the requested budget.
Known branch conditions select their actual path; otherwise branch bounds are
uniform. A call needs no source contract only when its continuation uses no
facts about the callee's result or final heap. -/
syntax (name := ramSourceCost) "ram_source_cost" (" (" ident* ")")?
  (" using " term:max)? : tactic

macro_rules
  | `(tactic| ram_source_cost) => `(tactic| ram_source_cost ())
  | `(tactic| ram_source_cost using $certificate) =>
      `(tactic| ram_source_cost () using $certificate)

elab_rules : tactic
  | `(tactic| ram_source_cost ($names:ident*)) =>
      Ram.LanguageCompiler.Tactic.startCost names []
  | `(tactic| ram_source_cost ($names:ident*) using $certificate) =>
      Ram.LanguageCompiler.Tactic.startCost names
        (Ram.LanguageCompiler.Tactic.costCertificates certificate)

/-- Introduce ordinary source parameters for the function-body cost rule,
without traversing the program or unfolding the statement contract. The goal
retains its actual heap and mathematical precondition; initialization costs two
instructions, so the requested bound has the shape `core + 2`. -/
syntax (name := ramSourceCostIntro) "ram_source_cost_intro" (" (" ident* ")")? : tactic

elab_rules : tactic
  | `(tactic| ram_source_cost_intro $[($names:ident*)]?) =>
      Ram.LanguageCompiler.Tactic.startCostIntro (names.getD #[])

/-- Compose the existing realization rules at a statement-level goal. Optional
callee facts supply realizability and source correctness. Mathematical leaves
and loop contracts remain goals, without introducing a function wrapper. -/
syntax (name := ramSourceRealizeStep) "ram_source_realize_step"
  (" using " term:max ", " term:max)? : tactic

elab_rules : tactic
  | `(tactic| ram_source_realize_step) => focus do
      Ram.LanguageCompiler.Tactic.realize none
  | `(tactic| ram_source_realize_step using $feasible, $specification) => focus do
      Ram.LanguageCompiler.Tactic.realize (some (feasible, specification))

/-- Compose the existing cost rules at a statement-level goal, optionally using
a callee bound. This does not add a function-body wrapper charge. Loop contracts
remain goals for a separate potential argument. -/
syntax (name := ramSourceCostStep) "ram_source_cost_step"
  (" using " term:max)? : tactic

elab_rules : tactic
  | `(tactic| ram_source_cost_step) => focus do
      Ram.LanguageCompiler.Tactic.cost []
  | `(tactic| ram_source_cost_step using $certificate) => focus do
      Ram.LanguageCompiler.Tactic.cost
        (Ram.LanguageCompiler.Tactic.costCertificates certificate)

/-- Apply one callee's resource and source contracts to the current call, then
continue structurally until the next call. Its actual result and heap remain
available there; the supplied contracts are not reused for that later call.
An explicit `next` function instead leaves its continuation and comparison
proofs under the actual returned-value/heap postcondition. Other existing goals
are preserved. -/
syntax (name := ramSourceCall) "ram_source_call" (" (" &"next" " := " term ")")?
  " using " term:max ", " term:max : tactic

elab_rules : tactic
  | `(tactic| ram_source_call using $resource, $specification) =>
      Ram.LanguageCompiler.Tactic.sourceCall resource specification
  | `(tactic| ram_source_call (next := $nextBound) using $resource, $specification) =>
      Ram.LanguageCompiler.Tactic.sourceCall resource specification (some nextBound)
