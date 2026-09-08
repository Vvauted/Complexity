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
# Source-directed initialization and branch proofs

`ram_total_start args entry pre` opens a function contract using its existing
`of_wp` rule, without advancing the body. `ram_time_start` similarly opens an
independent function time bound.

`ram_total_init function at current with bindings [facts]` starts at that
declared function's actual body or a retained source continuation. It consumes leading statements
containing only assignments and skips, using the lexical positions retained by
the original lowering. Calls, control flow and other side effects stop initialization.
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

`ram_total_branch function then at current with bindings [facts]` enters the
next conditional's true branch and initializes its lexical locals; `else` selects
the false branch. Guard and read-safety obligations remain unless fully solved.
`ram_time_branch` charges the actual guard and jump, retaining affordability
instead of assuming safety or termination. Parent continuations remain part of
the same computation; after a child completes, the parent scope is restored.

Only code continuations retain a declaration, lexical path and next source position.
The actual statement is checked against that fixed position, not found by an AST
search. Retained source and emitted syntax are never re-elaborated. The cursor
connects these initialization and branch tactics, not arbitrary subsequent tactics,
function-call continuations or loop-invariant proofs. The typed lets remain ordinary
proof snapshots across calls; they neither update themselves nor preserve heap contents.
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

private structure Cursor where
  function : Name
  path : DSL.ProofPath := []
  nextChild : Nat := 0

private structure BlockFrame where
  site : DSL.ProofSite
  code : Lean.Expr
  nextChild : Nat := 0

private def siteAt (sites : Array DSL.ProofSite) (path : DSL.ProofPath) :
    MetaM DSL.ProofSite := do
  let some site := sites.find? (fun site => site.path == path) |
    throwError "Missing source-proof location {path}"
  return site

private def blockChildren (frame : BlockFrame) (sites : Array DSL.ProofSite) :
    MetaM (Array DSL.ProofSite) :=
  frame.site.children.mapM (siteAt sites)

private def blockRemainder (frame : BlockFrame) (sites : Array DSL.ProofSite) :
    MetaM (Option Lean.Expr) := do
  let children ← blockChildren frame sites
  if children.isEmpty then
    return if frame.nextChild == 0 then some frame.code else none
  if frame.nextChild >= children.size then return none
  let skipped := (children.extract 0 frame.nextChild).foldl
    (fun n site => n + site.emitted.size) 0
  let mut rest := frame.code
  for _ in [:skipped] do
    let some (_, next) := (← whnf rest).app2? ``Stmt.seq |
      throwError "The actual statement does not match its source fragment boundaries"
    rest := next
  return some rest

private def framesRemainder (frames : List BlockFrame) (sites : Array DSL.ProofSite) :
    MetaM (Option Lean.Expr) := do
  let mut rest := none
  for frame in frames.reverse do
    if let some code ← blockRemainder frame sites then
      rest ← match rest with
        | none => pure (some code)
        | some tail => do pure (some (← mkAppM ``Stmt.seq #[code, tail]))
  return rest

/-- Reconstruct only the explicitly recorded lexical path in the actual function. -/
private partial def cursorFrames (code : Lean.Expr) (sites : Array DSL.ProofSite)
    (path : DSL.ProofPath) (nextChild : Nat) : MetaM (List BlockFrame) := do
  let rec descend (code : Lean.Expr) (atPath remaining : DSL.ProofPath)
      (parents : List BlockFrame) : MetaM (List BlockFrame) := do
    let site ← siteAt sites atPath
    match remaining with
    | [] => return ⟨site, code, nextChild⟩ :: parents
    | index :: side :: rest =>
        let frame : BlockFrame := ⟨site, code, index⟩
        let some childPath := site.children[index]? |
          throwError "Missing source statement at {atPath}, position {index}"
        let child ← siteAt sites childPath
        unless child.emitted.size == 1 do
          throwError "Expected one conditional source statement"
        let some suffix ← blockRemainder frame sites |
          throwError "The source position has no statement"
        let statement ← if index + 1 < site.children.size then do
            let some (first, _) := (← whnf suffix).app2? ``Stmt.seq |
              throwError "Expected the conditional's source continuation"
            pure first
          else pure suffix
        let statement ← whnf statement
        unless statement.isAppOfArity ``Stmt.ite 3 && side < 2 do
          throwError "Expected an actual conditional at source position {childPath}"
        let childCode := statement.getAppArgs[side + 1]!
        descend childCode (childPath ++ [side]) rest
          ({ frame with nextChild := index + 1 } :: parents)
    | _ => throwError "Incomplete lexical block path"
  descend code [] path []

private def pathName (path : DSL.ProofPath) : Name :=
  path.foldl Name.num .anonymous

private def namePath : Name → DSL.ProofPath
  | .anonymous => []
  | .num parent index => namePath parent ++ [index]
  | .str _ _ => []

private def cursor? (target : Lean.Expr) : Option Cursor := do
  let .mdata data _ := target | none
  let .ofName function ← data.find `ram.source.function | none
  let .ofName path ← data.find `ram.source.path | none
  let .ofNat nextChild ← data.find `ram.source.next | none
  return ⟨function, namePath path, nextChild⟩

private def markCursor (goal : MVarId) (cursor : Cursor) : MetaM MVarId := goal.withContext do
  let data := KVMap.empty
    |>.insert `ram.source.function cursor.function
    |>.insert `ram.source.path (pathName cursor.path)
    |>.insert `ram.source.next cursor.nextChild
  goal.change (.mdata data (← goal.getType).consumeMData)

private structure InitializationPrefix where
  fragments : Array Lean.Expr
  scope : DSL.LocalScope
  remaining : Nat
  nextChild : Nat

/-- Inspect only the current fragment, not another source position with equal code. -/
private partial def isInitialization (code : Lean.Expr) : MetaM Bool := do
  let code ← whnf code
  if code.isAppOf ``Stmt.skip || code.isAppOf ``Stmt.assign then return true
  if let some (first, second) := code.app2? ``Stmt.seq then
    return (← isInitialization first) && (← isInitialization second)
  return false

private def initializationPrefix (code : Lean.Expr) (frame : BlockFrame)
    (sites : Array DSL.ProofSite) :
    MetaM InitializationPrefix := do
  let allChildren ← blockChildren frame sites
  if allChildren.isEmpty then
    unless (← whnf code).isAppOf ``Stmt.skip do
      throwError "Expected an empty source block's actual skip"
    return ⟨#[code], frame.site.beforeScope, 0, 1⟩
  let children := allChildren.extract frame.nextChild allChildren.size
  let mut remaining := children.foldl (fun n site => n + site.emitted.size) 0
  let mut rest := code
  let mut fragments := #[]
  let mut scope := if frame.nextChild == 0 then frame.site.beforeScope
    else allChildren[frame.nextChild - 1]!.afterScope
  let mut nextChild := frame.nextChild
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
    nextChild := nextChild + 1
  return ⟨fragments, scope, remaining, nextChild⟩

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

private def sourceLocation (function : TSyntax `term) (mode : InitMode) :
    TacticM (Name × Array DSL.ProofSite × List BlockFrame × MVarId) := withMainContext do
    let function ← instantiateMVars (← elabTerm function (some (mkConst ``Ram.Func)))
    let .const name _ := function.getAppFn |
      throwError "Expected a function declared by ram_def"
    let some sites := (DSL.functionProofSites.getState (← getEnv)).find? name |
      throwError "No local source-proof metadata for {name}"
    let mut goal ← getMainGoal
    let args := (← goalView goal mode).getAppArgs
    let code := args[statementIndex mode]!
    let position := (cursor? (← goal.getType)).getD ⟨name, [], 0⟩
    unless position.function == name do
      throwError "The source continuation belongs to a different declaration"
    let frames ← cursorFrames (← mkAppM ``Ram.Func.body #[function]) sites
      position.path position.nextChild
    let some expected ← framesRemainder frames sites |
      throwError "The recorded source block has already completed"
    unless ← isDefEq code expected do
      throwError "Expected the actual body or a continuation retained by a source tactic"
    goal ← goal.change (← goal.getType).consumeMData
    return (name, sites, frames, goal)

private def reassociate (goal : MVarId) (mode : InitMode) : TacticM MVarId := do
  if mode == .total then
    applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.seq_assoc_iff.mpr))
  else applyOne goal (← `(tactic| apply Ram.Source.TimeBound.seq_assoc_iff.mpr))

/-- Advance within a block, returning to the parent's scope only after its code ends. -/
private def advancePrefix (name : Name) (sites : Array DSL.ProofSite)
    (initialFrames : List BlockFrame) (initialGoal : MVarId)
    (current bindings : TSyntax `ident) (facts : SimpFacts) (mode : InitMode)
    (pending : List MVarId := []) : TacticM Unit := initialGoal.withContext do
  let args := (← goalView initialGoal mode).getAppArgs
  let mut goal := initialGoal
  let mut frames := initialFrames
  let entryState ← if mode == .total then pure args[6]! else timeEntry args[6]!
  let mut currentState := entryState
  let mut obligations := pending
  let mut scope := (← siteAt sites []).afterScope
  while !frames.isEmpty do
    let frame :: parents := frames | break
    let some code ← blockRemainder frame sites | frames := parents; continue
    let initialization ← initializationPrefix code frame sites
    let hasOuter := (← framesRemainder parents sites).isSome
    let mut remaining := initialization.fragments.size + initialization.remaining
    for fragment in initialization.fragments do
      if hasOuter && remaining > 1 then goal ← reassociate goal mode
      let hasTail := remaining > 1 || hasOuter
      if mode == .total then
        if hasTail then
          goal ← applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.seq_iff.mpr))
        let (next, nextState, more) ← totalFragment goal facts
        goal := next
        currentState := nextState
        obligations := obligations ++ more
      else
        let (next, nextState, more) ← timeFragment goal fragment hasTail facts
        obligations := obligations ++ more
        let some next := next | setGoals obligations; return
        goal := next
        currentState := nextState
      remaining := remaining - 1
    scope := initialization.scope
    if initialization.remaining > 0 then
      frames := { frame with nextChild := initialization.nextChild } :: parents
      break
    frames := parents
    scope := (← siteAt sites []).afterScope
  let post? := if mode == .total && frames.isEmpty then some args[5]! else none
  goal ← nameState goal currentState scope current bindings facts mode post?
  if let frame :: _ := frames then
    goal ← markCursor goal ⟨name, frame.site.path, frame.nextChild⟩
  setGoals (obligations ++ [goal])

private def initializeSource (function : TSyntax `term) (current bindings : TSyntax `ident)
    (facts : SimpFacts) (mode : InitMode) : TacticM Unit :=
  Lean.Elab.Tactic.focus <| withMainContext do
    let (name, sites, frames, goal) ← sourceLocation function mode
    advancePrefix name sites frames goal current bindings facts mode

private def enterBranch (function : TSyntax `term) (yes : Bool)
    (current bindings : TSyntax `ident) (facts : SimpFacts) (mode : InitMode) :
    TacticM Unit := Lean.Elab.Tactic.focus <| withMainContext do
  let (name, sites, frames, initialGoal) ← sourceLocation function mode
  let frame :: parents := frames | throwError "Expected a conditional source position"
  let children ← blockChildren frame sites
  let some site := children[frame.nextChild]? |
    throwError "Expected a conditional source statement"
  unless site.emitted.size == 1 do
    throwError "Expected one actual conditional at this source position"
  let count := (children.extract frame.nextChild children.size).foldl
    (fun n child => n + child.emitted.size) 0
  let hasOuter := (← framesRemainder parents sites).isSome
  let mut goal := initialGoal
  if hasOuter && count > 1 then goal ← reassociate goal mode
  let hasTail := count > 1 || hasOuter
  let code := (← goalView goal mode).getAppArgs[statementIndex mode]!
  let statement ← if hasTail then do
      let some (first, _) := (← whnf code).app2? ``Stmt.seq |
        throwError "Expected the actual conditional and its continuation"
      pure first
    else pure code
  let statement ← whnf statement
  unless statement.isAppOfArity ``Stmt.ite 3 do
    throwError "The next source statement is not a conditional"
  if hasTail then
    goal ← if mode == .total then
      applyOne goal (← `(tactic| apply Ram.Source.Verification.TotalWP.ite_seq_iff.mpr))
    else applyOne goal (← `(tactic| apply Ram.Source.TimeBound.ite_seq_iff.mpr))
  setGoals [goal]
  if mode == .total then
    if yes then
      evalTactic (← `(tactic| apply Ram.Source.Verification.TotalWP.ite_of_ne_zero))
    else evalTactic (← `(tactic| apply Ram.Source.Verification.TotalWP.ite_of_eq_zero))
  else
    if yes then evalTactic (← `(tactic| apply Ram.Source.TimeBound.ite_of_ne_zero_at))
    else evalTactic (← `(tactic| apply Ram.Source.TimeBound.ite_of_eq_zero_at))
  let [first, second, branch] ← getUnsolvedGoals |
    throwError "Expected the conditional obligations and selected code continuation"
  let firstGoals ← trySafety first facts
  let secondGoals ← if mode == .total then trySafety second facts else tryBudget second facts
  let pending := firstGoals ++ secondGoals
  let side := if yes then 0 else 1
  let childCode := statement.getAppArgs[side + 1]!
  let child ← if let some path := site.children[side]? then siteAt sites path else do
    unless !yes && (← whnf childCode).isAppOf ``Stmt.skip do
      throwError "Missing source metadata for the selected branch"
    pure { site with source := none, emitted := #[], children := #[] }
  let nextFrames := (⟨child, childCode, 0⟩ : BlockFrame) ::
    { frame with nextChild := frame.nextChild + 1 } :: parents
  advancePrefix name sites nextFrames branch current bindings facts mode pending

/-- Consume the declared function's leading source initializers using total WP rules. -/
syntax (name := ramTotalInit) "ram_total_init " term:max " at " ident " with " ident
  (" [" simpArg,* "]")? : tactic

/-- Consume the same source initializers with their independent compiled costs. -/
syntax (name := ramTimeInit) "ram_time_init " term:max " at " ident " with " ident
  (" [" simpArg,* "]")? : tactic

/-- Enter a selected source branch and expose its initialized lexical values. -/
syntax (name := ramTotalBranch) "ram_total_branch " term:max (" then" <|> " else")
  " at " ident " with " ident (" [" simpArg,* "]")? : tactic

/-- Charge a selected source branch and initialize its independent time continuation. -/
syntax (name := ramTimeBranch) "ram_time_branch " term:max (" then" <|> " else")
  " at " ident " with " ident (" [" simpArg,* "]")? : tactic

elab_rules : tactic
  | `(tactic| ram_total_init $function at $current:ident with $bindings:ident $[[$facts,*]]?) =>
      initializeSource function current bindings (facts.map (·.getElems) |>.getD #[]) .total
  | `(tactic| ram_time_init $function at $current:ident with $bindings:ident $[[$facts,*]]?) =>
      initializeSource function current bindings (facts.map (·.getElems) |>.getD #[]) .time
  | `(tactic| ram_total_branch $function then at $current:ident with $bindings:ident
      $[[$facts,*]]?) =>
      enterBranch function true current bindings (facts.map (·.getElems) |>.getD #[]) .total
  | `(tactic| ram_total_branch $function else at $current:ident with $bindings:ident
      $[[$facts,*]]?) =>
      enterBranch function false current bindings (facts.map (·.getElems) |>.getD #[]) .total
  | `(tactic| ram_time_branch $function then at $current:ident with $bindings:ident
      $[[$facts,*]]?) =>
      enterBranch function true current bindings (facts.map (·.getElems) |>.getD #[]) .time
  | `(tactic| ram_time_branch $function else at $current:ident with $bindings:ident
      $[[$facts,*]]?) =>
      enterBranch function false current bindings (facts.map (·.getElems) |>.getD #[]) .time

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
