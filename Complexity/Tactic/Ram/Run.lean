/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function.Total
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp

/-!
# Applying the executable function bridges

`ram_run_apply bridge [facts]` applies an existing function-runner theorem and
uses its compilation premise to select the standard compiled call trampoline.
It attempts only the static compilation, function lookup and code-length gates.
Stack capacity, source execution, contracts and mathematical premises remain
ordinary proof goals. Supplied facts are used only on those static gates.

For example, `ram_run_apply (LocalCompiler.Function.halts_of_contract
(contract := contract) (pre := pre)) [lookup]` reuses budget-free correctness.
Value, state and time proofs can instead select the corresponding existing
bridge, supplying its `execution` argument to infer the source function.

The tactic also works in `have result := by ...`, where the selected bridge
determines the result type. Supply a function index explicitly if neither the
goal nor a supplied argument determines it. Static proofs are attempted at the
use site: declaring a source function does not require compilation to succeed.
There is no new runner, unchecked compilation or automatically selected budget.
-/

namespace Ram.Tactic

open Lean Meta Elab Tactic Parser.Tactic

/-- Apply an existing executable-call theorem and discharge its decidable static
gates. Safety, source correctness and independent time obligations stay visible. -/
syntax (name := ramRunApply) "ram_run_apply " term:max (" [" simpArg,* "]")? : tactic

/-- Infer the standard code from an existing checked-compilation premise. -/
private def inferRunCode (goal : MVarId) : MetaM (Option (Lean.Expr × Lean.Expr)) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := target.eq? | return none
    let some (control, program, fn, arity) :=
      lhs.app4? ``LocalCompiler.Function.compile | return none
    let some (_, code) := rhs.app2? ``Option.some | return none
    let trampoline ← mkAppM ``LocalCompiler.Function.trampoline #[fn, arity]
    let compiled ← mkAppM ``LocalCompiler.rawLink #[control, program, trampoline]
    unless ← isDefEq code compiled do return none
    let lookup ← mkAppM ``GetElem?.getElem? #[program, fn]
    return some (compiled, lookup)

/-- Recognize only lookup and representability obligations for the inferred call. -/
private def isRunStaticGate (target code lookup : Lean.Expr) : MetaM Bool := do
  if let some (_, lhs, _) := target.eq? then
    if lhs.isAppOfArity ``LocalCompiler.Function.compile 4 then return true
    unless lhs.isAppOf ``GetElem?.getElem? do return false
    return ← isDefEq lhs lookup
  let lhs? := match target.app4? ``LT.lt with
    | some (_, _, lhs, _) => some lhs
    | none => (target.app2? ``Nat.lt).map Prod.fst
  let some lhs := lhs? | return false
  unless lhs.isAppOfArity ``List.length 2 do return false
  return ← isDefEq lhs.appArg! code

elab_rules : tactic
  | `(tactic| ram_run_apply $bridge $[[$facts,*]]?) => focus do
      evalTactic (← `(tactic| apply $bridge))
      let goals ← getUnsolvedGoals
      let mut call? := none
      for goal in goals do
        if let some call ← inferRunCode goal then
          call? := some call
          break
      let some (code, lookup) := call? | return
      let facts := facts.map (·.getElems) |>.getD #[]
      let mut remaining := []
      for goal in ← getUnsolvedGoals do
        let next ← goal.withContext do
          let target ← instantiateMVars (← goal.getType)
          if ← isRunStaticGate target code lookup then
            setGoals [goal]
            evalTactic (← `(tactic|
              try (set_option maxRecDepth 4096 in
                solve
                | simp only [$facts,*]
                | decide)))
            getUnsolvedGoals
          else
            pure [goal]
        remaining := remaining ++ next
      setGoals remaining

end Ram.Tactic
