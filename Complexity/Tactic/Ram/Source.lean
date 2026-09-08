/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Tactic.Ram.Total
import Complexity.Tactic.Ram.Time
import Lean.Elab.Tactic.Conv

/-!
# Source-directed initialization proofs

`ram_total_start args entry pre` opens a function contract using its existing
`of_wp` rule, without advancing the body. `ram_time_start` similarly opens an
independent function time bound.

`ram_total_init function at current with bindings [facts]` starts at that
declared function's actual body. It consumes complete leading source statements
containing only assignments and skips, using the lexical positions retained by
the original lowering. Calls, control flow and other side effects stop it.
In particular, both assignments of an array initializer complete before its
new binding becomes visible. Read-safety obligations are retained unless the
supplied facts and ordinary RAM simplification solve them completely.

The remaining state is named `current`; its visible source values become typed
Lean lets such as `current.lo` and `current.xs`. Equations under `bindings`
connect those values to the actual registers. These are proof observations,
not another execution of the source program or function-level loop locals.

`ram_time_init` uses the same source prefix and bindings but the independent
measured rules, retaining every unresolved cost obligation. If the entire body
is an initialization, its final primitive bound finishes the code proof.

Only the actual goal's statement is inspected. Retained source and emitted
syntax are never re-elaborated; their fragment counts identify the boundaries
of the same lowering. This is an initialization driver, not a cursor that
tracks arbitrary subsequent tactics or enters nested lexical blocks.
-/

namespace Ram.Tactic.Source

open Lean Meta Elab Tactic Parser.Tactic

private abbrev SimpFacts :=
  TSyntaxArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]

private inductive InitMode where
  | total
  | time
  deriving BEq

private def goalView (goal : MVarId) (mode : InitMode) : MetaM Lean.Expr :=
  goal.withContext do
    let name := if mode == .total then ``Ram.Source.Verification.TotalWP
      else ``Ram.Source.TimeBound
    let some target ← whnfUntil (← instantiateMVars (← goal.getType)) name |
      throwError "Expected a {name} goal at the declared function body"
    return target

private def statementIndex (mode : InitMode) : Nat :=
  if mode == .total then 4 else 5

private def timeEntry (pre : Lean.Expr) : MetaM Lean.Expr := do
  lambdaTelescope (← whnfR pre) fun states body => do
    unless states.size == 1 do
      throwError "Expected a time precondition of the form fun s => s = entry"
    let some (_, lhs, rhs) := body.eq? |
      throwError "Expected a time precondition of the form fun s => s = entry"
    unless (← isDefEq lhs states[0]!) && !rhs.containsFVar states[0]!.fvarId! do
      throwError "Expected a time precondition of the form fun s => s = entry"
    return rhs

private structure InitializationPrefix where
  fragments : Array Lean.Expr
  scope : DSL.LocalScope
  remaining : Nat

/-- Inspect only the current fragment, not another source position with equal code. -/
private partial def isInitialization (code : Lean.Expr) : MetaM Bool := do
  let code ← whnf code
  if code.isAppOf ``Stmt.skip || code.isAppOf ``Stmt.assign then return true
  if let some (first, second) := code.app2? ``Stmt.seq then
    return (← isInitialization first) && (← isInitialization second)
  return false

private def initializationPrefix (code : Lean.Expr) (sites : Array DSL.ProofSite) :
    MetaM InitializationPrefix := do
  let some root := sites.find? (fun site => site.path.isEmpty) |
    throwError "The function has no root source-proof location"
  let children ← root.children.mapM fun path => do
    let some site := sites.find? (fun site => site.path == path) |
      throwError "Missing source-proof location {path}"
    pure site
  let mut remaining := children.foldl (fun n site => n + site.emitted.size) 0
  let mut rest := code
  let mut fragments := #[]
  let mut scope := root.beforeScope
  for site in children do
    if site.synthetic || site.source.isNone || !site.children.isEmpty then break
    let mut nextRest := rest
    let mut nextRemaining := remaining
    let mut emitted := #[]
    for _ in [:site.emitted.size] do
      if nextRemaining > 1 then
        let some (first, second) := (← whnf nextRest).app2? ``Stmt.seq |
          throwError "The actual statement does not match its source fragment boundaries"
        emitted := emitted.push first
        nextRest := second
      else
        emitted := emitted.push nextRest
      nextRemaining := nextRemaining - 1
    unless ← emitted.allM isInitialization do break
    fragments := fragments ++ emitted
    scope := site.afterScope
    rest := nextRest
    remaining := nextRemaining
  return ⟨fragments, scope, remaining⟩

private def applyOne (goal : MVarId) (tactic : TSyntax `tactic) : TacticM MVarId := do
  setGoals [goal]
  evalTactic tactic
  let [next] ← getUnsolvedGoals | throwError "Expected one code continuation"
  return next

private def trySafety (goal : MVarId) (facts : SimpFacts) :
    TacticM (List MVarId) := do
  setGoals [goal]
  evalTactic (← `(tactic| try (solve | (ram_simp [$facts,*] <;> assumption))))
  getUnsolvedGoals

private def tryBudget (goal : MVarId) (facts : SimpFacts) :
    TacticM (List MVarId) := do
  setGoals [goal]
  evalTactic (← `(tactic| try (solve | (intros; ram_bound [$facts,*]))))
  getUnsolvedGoals

private partial def totalFragment (goal : MVarId) (facts : SimpFacts) :
    TacticM (MVarId × Lean.Expr × List MVarId) := goal.withContext do
  let args := (← goalView goal .total).getAppArgs
  let code ← whnf args[4]!
  let state := args[6]!
  if code.isAppOf ``Stmt.skip then
    let next ← applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.skip_iff.mpr))
    return (next, state, [])
  if let some (dst, value) := code.app2? ``Stmt.assign then
    let nextState ← mkAppM ``Ram.Source.State.setReg
      #[state, dst, ← mkAppM ``Ram.Source.State.eval #[state, value]]
    let conjunction ← applyOne goal
      (← `(tactic| apply Ram.Source.Verification.TotalWP.assign_iff.mpr))
    setGoals [conjunction]
    evalTactic (← `(tactic| apply And.intro))
    let [reads, next] ← getUnsolvedGoals | throwError "Expected assignment safety and continuation"
    return (next, nextState, ← trySafety reads facts)
  if code.isAppOf ``Stmt.seq then
    let first ← applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.seq_iff.mpr))
    let (second, _, firstGoals) ← totalFragment first facts
    let (next, state, secondGoals) ← totalFragment second facts
    return (next, state, firstGoals ++ secondGoals)
  throwError "Expected an assignment or skip initialization fragment"

private partial def timeFragment (goal : MVarId) (fragment : Lean.Expr) (hasTail : Bool)
    (facts : SimpFacts) :
    TacticM (Option MVarId × Lean.Expr × List MVarId) := goal.withContext do
  let args := (← goalView goal .time).getAppArgs
  let state ← timeEntry args[6]!
  let fragment ← whnf fragment
  if let some (first, second) := fragment.app2? ``Stmt.seq then
    let goal ← if hasTail then
        applyOne goal (← `(tactic| apply Ram.Source.TimeBound.seq_assoc_iff.mpr))
      else pure goal
    let (some next, _, firstGoals) ← timeFragment goal first true facts |
      throwError "Expected the second initialization fragment"
    let (next, state, secondGoals) ← timeFragment next second hasTail facts
    return (next, state, firstGoals ++ secondGoals)
  if !hasTail then
    setGoals [goal]
    if fragment.isAppOf ``Stmt.skip then
      evalTactic (← `(tactic| apply (Ram.Source.TimeBound.skip _).mono_budget))
    else
      evalTactic (← `(tactic| apply Ram.Source.TimeBound.assign.mono_budget))
    let [budget] ← getUnsolvedGoals | throwError "Expected the final primitive's cost obligation"
    return (none, state, ← tryBudget budget facts)
  if fragment.isAppOf ``Stmt.skip then
    let next ← applyOne goal (← `(tactic| apply Ram.Source.TimeBound.skip_seq_iff.mpr))
    return (some next, state, [])
  let some (dst, value) := fragment.app2? ``Stmt.assign |
    throwError "Expected an assignment or skip initialization fragment"
  let nextState ← mkAppM ``Ram.Source.State.setReg
    #[state, dst, ← mkAppM ``Ram.Source.State.eval #[state, value]]
  setGoals [goal]
  evalTactic (← `(tactic| apply Ram.Source.TimeBound.assign_seq_at))
  let [budget, next] ← getUnsolvedGoals | throwError "Expected assignment cost and continuation"
  return (some next, nextState, ← tryBudget budget facts)

private def defineLocal (goal : MVarId) (name : Name) (value : Lean.Expr) :
    MetaM (Lean.Expr × MVarId) := goal.withContext do
  let next ← goal.define name (← inferType value) value
  let (id, next) ← next.intro1P
  return (mkFVar id, next)

private def normalizedRead (state : Lean.Expr) (slot : Nat)
    (facts : SimpFacts) : TacticM (Lean.Expr × Lean.Expr) := do
  let observed := mkApp (← mkAppM ``Ram.Source.State.regs #[state]) (mkNatLit slot)
  Conv.convert observed <| evalTactic (← `(conv|
    simp [ram_bindings, Ram.Source.State.eval, Ram.Expr.eval, Ram.BinOp.eval,
      Ram.Source.State.setReg, Ram.Source.State.enter_regs,
      Ram.Source.State.setRegs_nil, Ram.Source.State.setRegs_cons,
      Ram.ArrayRef.args, BitVec.ofNat_eq_ofNat, $facts,*]))

private def noteBinding (goal : MVarId) (name : Name) (state : Lean.Expr) (slot : Nat)
    (value proof : Lean.Expr) : MetaM MVarId := goal.withContext do
  let lhs := mkApp (← mkAppM ``Ram.Source.State.regs #[state]) (mkNatLit slot)
  let (_, next) ← goal.note name proof (some (← mkEq lhs value))
  return next

private def nameState (goal : MVarId) (state : Lean.Expr) (scope : DSL.LocalScope)
    (current bindings : TSyntax `ident) (facts : SimpFacts)
    (mode : InitMode) (post? : Option Lean.Expr) : TacticM MVarId := goal.withContext do
  let (named, goal) ← defineLocal goal current.getId state
  let mut goal ← goal.withContext do
    let target ← match post? with
      | some post => pure (mkApp post named)
      | none => do
          let target ← goalView goal mode
          let args := target.getAppArgs
          if mode == .total then
            pure (mkAppN target.getAppFn (args.set! 6 named))
          else
            let pre ← withLocalDeclD `s (← inferType named) fun s => do
              mkLambdaFVars #[s] (← mkEq s named)
            pure (mkAppN target.getAppFn (args.set! 6 pre))
    goal.change target
  for binding in scope do
    goal ← goal.withContext do
      let sourceName := binding.name.eraseMacroScopes
      let valueName := current.getId ++ sourceName
      let proofName := bindings.getId ++ sourceName
      match binding.kind with
      | .unit => pure goal
      | .word => do
          let (value, proof) ← normalizedRead state binding.register facts
          let (value, goal) ← defineLocal goal valueName value
          noteBinding goal proofName named binding.register value proof
      | .array => do
          let (base, baseProof) ← normalizedRead state binding.register facts
          let (length, lengthProof) ← normalizedRead state (binding.register + 1) facts
          let value ← mkAppM ``Ram.ArrayRef.mk #[base, length]
          let (value, goal) ← defineLocal goal valueName value
          let goal ← goal.withContext do
            noteBinding goal (proofName ++ `base) named binding.register
              (← mkAppM ``Ram.ArrayRef.base #[value]) baseProof
          goal.withContext do
            noteBinding goal (proofName ++ `length) named (binding.register + 1)
              (← mkAppM ``Ram.ArrayRef.length #[value]) lengthProof
  return goal

private def initializeSource (function : TSyntax `term) (current bindings : TSyntax `ident)
    (facts : SimpFacts) (mode : InitMode) : TacticM Unit :=
  Lean.Elab.Tactic.focus <| withMainContext do
    let function ← instantiateMVars (← elabTerm function (some (mkConst ``Ram.Func)))
    let .const name _ := function.getAppFn |
      throwError "Expected a function declared by ram_def"
    let some sites := (DSL.functionProofSites.getState (← getEnv)).find? name |
      throwError "No local source-proof metadata for {name}"
    let mut goal ← getMainGoal
    let args := (← goalView goal mode).getAppArgs
    let code := args[statementIndex mode]!
    unless ← isDefEq code (← mkAppM ``Ram.Func.body #[function]) do
      throwError "Initialization must start at this function's actual body"
    let initialization ← initializationPrefix code sites
    let mut remaining := initialization.fragments.size + initialization.remaining
    let entryState ← if mode == .total then pure args[6]! else timeEntry args[6]!
    let mut currentState : Lean.Expr := entryState
    let mut obligations := []
    for fragment in initialization.fragments do
      if mode == .total then
        if remaining > 1 then
          goal ← applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.seq_iff.mpr))
        let (next, nextState, pending) ← totalFragment goal facts
        goal := next
        currentState := nextState
        obligations := obligations ++ pending
      else
        let (next, nextState, pending) ← timeFragment goal fragment (remaining > 1) facts
        obligations := obligations ++ pending
        let some next := next | setGoals obligations; return
        goal := next
        currentState := nextState
      remaining := remaining - 1
    let post? := if mode == .total && remaining == 0 && !initialization.fragments.isEmpty then
        some args[5]! else none
    goal ← nameState goal currentState initialization.scope current bindings facts mode post?
    setGoals (obligations ++ [goal])

/-- Consume the declared function's leading source initializers using total WP rules. -/
syntax (name := ramTotalInit) "ram_total_init " term:max " at " ident " with " ident
  (" [" simpArg,* "]")? : tactic

/-- Consume the same source initializers with their independent compiled costs. -/
syntax (name := ramTimeInit) "ram_time_init " term:max " at " ident " with " ident
  (" [" simpArg,* "]")? : tactic

elab_rules : tactic
  | `(tactic| ram_total_init $function at $current:ident with $bindings:ident $[[$facts,*]]?) =>
      initializeSource function current bindings (facts.map (·.getElems) |>.getD #[]) .total
  | `(tactic| ram_time_init $function at $current:ident with $bindings:ident $[[$facts,*]]?) =>
      initializeSource function current bindings (facts.map (·.getElems) |>.getD #[]) .time

/-- Open a raw or typed function contract, leaving its body unexecuted. -/
syntax (name := ramTotalStart) "ram_total_start" ppSpace ident ppSpace ident ppSpace rcasesPat
  (" [" simpArg,* "]")? : tactic

elab_rules : tactic
  | `(tactic| ram_total_start $args:ident $entry:ident $pre:rcasesPat $[[$facts,*]]?) =>
      focus <| withMainContext do
        let facts := facts.map (·.getElems) |>.getD #[]
        let target ← getMainTarget
        let typed := (← whnfUntil target ``Ram.Source.TypedFunctionContract).isSome
        if typed then
          evalTactic (← `(tactic|
            refine Ram.Source.TypedFunctionContract.of_wp ?shape ?arity ?frame ?body))
        else
          unless (← whnfUntil target ``Ram.Source.FunctionContract).isSome do
            throwError "Expected a raw or typed FunctionContract"
          evalTactic (← `(tactic| refine Ram.Source.FunctionContract.of_wp ?arity ?frame ?body))
        for goal in ← getUnsolvedGoals do
          goal.setTag (← goal.getTag).eraseMacroScopes
        if typed then
          evalTactic (← `(tactic| case' shape => try (solve | ram_simp [DSL.ValueKind.width, $facts,*])))
        evalTactic (← `(tactic|
          case' frame => try (solve | decide | ram_simp [$facts,*])))
        evalTactic (← `(tactic|
          case' arity =>
            intro $args:ident $entry:ident
            rintro $pre:rcasesPat <;> try (solve | (ram_simp [$facts,*] <;> assumption))))
        evalTactic (← `(tactic|
          case' body =>
            intro $args:ident $entry:ident
            rintro $pre:rcasesPat))

/-- Open a separate function time bound without advancing its source body. -/
syntax (name := ramTimeStart) "ram_time_start" ppSpace ident ppSpace ident ppSpace rcasesPat : tactic

macro_rules
  | `(tactic| ram_time_start $args:ident $entry:ident $pre:rcasesPat) =>
      `(tactic|
        (apply Ram.Source.FunctionTimeBound.of_body_at
         intro $args:ident $entry:ident
         rintro $pre:rcasesPat))

end Ram.Tactic.Source
