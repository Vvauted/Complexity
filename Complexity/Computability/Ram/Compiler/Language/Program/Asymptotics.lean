/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Time
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Asymptotics of compiler-derived program bounds

`program_time_asymptotics [leaf, one, ...]` combines supplied mathlib `IsBigO`
proofs through natural-number addition, maxima, constant multiplication and
the compiler's actual call overhead. Constants use a supplied proof of
`(fun _ => (1 : ℝ)) =O[l] growth`; the growth function is not assumed linear.

Expose a chosen inferred budget with ordinary `unfold` first. The pass keeps
operation budgets and fixed compiler metadata opaque, and does not unfold
program bodies, assign instruction prices or infer loop recurrences. Missing
asymptotic leaves remain goals. Execution, capacity and termination proofs are
separate from this arithmetic composition.
-/

namespace Ram.LanguageCompiler

open Asymptotics

/-- Actual internal-call overhead preserves any asymptotic class that absorbs
constants. The callee's supplied body bound is not unfolded. -/
theorem isBigO_callCost {signatures : List Complexity.Language.Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {l : Filter Nat} {bound : Nat → Nat} {growth : Nat → ℝ}
    (bounded : IsBigO l (fun n => (bound n : ℝ)) growth)
    (one : IsBigO l (fun _ => (1 : ℝ)) growth) :
    IsBigO l (fun n => (callCost program fn (bound n) : ℝ)) growth := by
  have overhead : IsBigO l (fun _ => (callCost program fn 0 : ℝ)) growth := by
    simpa only [mul_one] using one.const_mul_left (callCost program fn 0 : ℝ)
  have equation : (fun n => (callCost program fn (bound n) : ℝ)) =
      (fun n => (bound n : ℝ) + (callCost program fn 0 : ℝ)) := by
    funext n
    rw [callCost_eq_add, Nat.cast_add]
  rw [equation]
  exact bounded.add overhead

end Ram.LanguageCompiler

namespace Complexity.Program

open Asymptotics

/-- Full-invocation overhead preserves any asymptotic class that absorbs
constants, without unfolding the program or its generated calling convention. -/
theorem isBigO_invocationBound {α β : Type*} [Input α] [Output β]
    (program : Complexity.Program α β)
    {l : Filter Nat} {bound : Nat → Nat} {growth : Nat → ℝ}
    (bounded : IsBigO l (fun n => (bound n : ℝ)) growth)
    (one : IsBigO l (fun _ => (1 : ℝ)) growth) :
    IsBigO l (fun n => (program.invocationBound (bound n) : ℝ)) growth := by
  have overhead : IsBigO l (fun _ => (program.invocationBound 0 : ℝ)) growth := by
    simpa only [mul_one] using one.const_mul_left (program.invocationBound 0 : ℝ)
  have equation : (fun n => (program.invocationBound (bound n) : ℝ)) =
      (fun n => (bound n : ℝ) + (program.invocationBound 0 : ℝ)) := by
    funext n
    rw [invocationBound_eq, Nat.cast_add]
  rw [equation]
  exact bounded.add overhead

namespace AsymptoticsTactic

open Lean Meta Elab Tactic

variable {l : Filter Nat} {growth : Nat → ℝ} {left right : Nat → Nat}

private theorem nat_add
    (hl : IsBigO l (fun n => (left n : ℝ)) growth)
    (hr : IsBigO l (fun n => (right n : ℝ)) growth) :
    IsBigO l (fun n => ((left n + right n : Nat) : ℝ)) growth := by
  simpa only [Nat.cast_add] using hl.add hr

private theorem nat_max
    (hl : IsBigO l (fun n => (left n : ℝ)) growth)
    (hr : IsBigO l (fun n => (right n : ℝ)) growth) :
    IsBigO l (fun n => ((max (left n) (right n) : Nat) : ℝ)) growth := by
  simpa only [Prod.norm_mk, Real.norm_natCast, Nat.cast_max]
    using (hl.prod_left hr).norm_left

private theorem nat_const (constant : Nat)
    (one : IsBigO l (fun _ => (1 : ℝ)) growth) :
    IsBigO l (fun _ => (constant : ℝ)) growth := by
  simpa only [mul_one] using one.const_mul_left (constant : ℝ)

private theorem nat_const_mul (constant : Nat)
    (bounded : IsBigO l (fun n => (left n : ℝ)) growth) :
    IsBigO l (fun n => ((constant * left n : Nat) : ℝ)) growth := by
  simpa only [Nat.cast_mul] using bounded.const_mul_left (constant : ℝ)

private theorem nat_mul_const (constant : Nat)
    (bounded : IsBigO l (fun n => (left n : ℝ)) growth) :
    IsBigO l (fun n => ((left n * constant : Nat) : ℝ)) growth := by
  simpa only [Nat.mul_comm] using nat_const_mul constant bounded

private theorem nat_succ
    (bounded : IsBigO l (fun n => (left n : ℝ)) growth)
    (one : IsBigO l (fun _ => (1 : ℝ)) growth) :
    IsBigO l (fun n => (Nat.succ (left n) : ℝ)) growth := by
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using bounded.add one

/-- Match supplied mathematical leaves before inspecting their budget terms. -/
private def certificate? (certificates : Array (Lean.Expr × Lean.Expr)) :
    TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for (proof, type) in certificates do
    if ← Tactic.tryCatchRestore
        (do
          unless ← withReducible <| isDefEq type target do
            throwError "cost certificate does not match"
          goal.assign proof
          replaceMainGoal []
          pure true)
        (fun _ => pure false) then
      return true
  return false

/-- Select an ordinary arithmetic rule without reducing compiler metadata or
operation budgets. Only dependence on the mathematical size is inspected. -/
private def structuralRule? : TacticM (Option (TSyntax `term)) := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  unless target.isAppOf ``Asymptotics.IsBigO do return none
  let arguments := target.getAppArgs
  let function := arguments[arguments.size - 2]!
  withLocalDeclD `size (mkConst ``Nat) fun size => do
    let cast := (mkApp function size).headBeta.consumeMData
    unless cast.isAppOf ``Nat.cast || cast.isAppOf ``NatCast.natCast do return none
    let bound := cast.getAppArgs.back!.consumeMData.headBeta.consumeMData
    unless bound.containsFVar size.fvarId! do
      return some (← `(nat_const))
    if bound.isAppOf ``Nat.add || bound.isAppOf ``HAdd.hAdd then
      return some (← `(nat_add))
    if bound.isAppOf ``Nat.max || bound.isAppOf ``Max.max then
      return some (← `(nat_max))
    if bound.isAppOf ``Nat.succ then
      return some (← `(nat_succ))
    if bound.isAppOf ``Nat.mul || bound.isAppOf ``HMul.hMul then
      let factors := bound.getAppArgs
      unless factors[factors.size - 2]!.containsFVar size.fvarId! do
        return some (← `(nat_const_mul))
      unless factors.back!.containsFVar size.fvarId! do
        return some (← `(nat_mul_const))
    if bound.isAppOf ``Ram.LanguageCompiler.callCost then
      return some (← `(Ram.LanguageCompiler.isBigO_callCost))
    if bound.isAppOf ``Complexity.Program.invocationBound then
      return some (← `(Complexity.Program.isBigO_invocationBound))
    return none

private partial def compose (certificates : Array (Lean.Expr × Lean.Expr)) : TacticM Unit := do
  if ← certificate? certificates then return
  if let some rule ← structuralRule? then
    evalTactic (← `(tactic| apply $rule))
    Ram.LanguageCompiler.Tactic.onGoals (compose certificates)

/-- Combine supplied `IsBigO` proofs through inferred natural-number budgets.
Constants require a supplied `1 =O growth` proof; unsupported leaves stay goals.
No source body, operation budget or fixed compiler price is unfolded. -/
syntax "program_time_asymptotics" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| program_time_asymptotics [$certificates:term,*]) => focus do
      let proofs ← withMainContext do
        let theorems := ({} : SimpTheorems).addDeclToUnfoldCore ``id
          |>.addDeclToUnfoldCore ``Function.comp
        let context ← Simp.mkContext (simpTheorems := #[theorems])
        certificates.getElems.mapM fun stx => do
          let proof ← elabTerm stx none
          let (type, _) ← Meta.dsimp (← inferType proof) context
          pure (proof, type)
      evalTactic (← `(tactic| dsimp only [id, Function.comp]))
      compose proofs

end AsymptoticsTactic
end Complexity.Program
