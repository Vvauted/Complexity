/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CodeSize
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Costs of realized scalar source executions

`ExecutionCost` observes the same source execution as `RealizedExec`. Its rules
count the operations emitted by scalar lowering, including the private return
flag and actual callee-frame work. The observation does not supply termination,
change source behavior, or ask a program author to assign instruction prices.

Counts here cover `lowerStmtCore`. A returning function body additionally runs
its flag initialization and final dispatch, for five transitions. The outer
invocation's calling convention and final halt are accounted for separately.
Internal calls already include their callee's complete body and call overhead.

The canonical reserved-register position in `callSteps 0` only fixes a length
expression; register placement does not change generated instruction counts.
The measured lowering theorem connects these rules to actual RAM transitions.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Complete internal-call charge for a source function and a bound on its
lowered body. Argument fields, frame operations and return reception come from
the actual compiler; clients do not supply register locations or ABI prices. -/
def callCost {signatures : List Signature} (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (bodySteps : Nat) : Nat :=
  LocalCompiler.Function.callSteps 0 (lowerFunc program fn) bodySteps

/-- A callee body bound transports through its compiler-derived call overhead. -/
theorem callCost_mono {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    Monotone (callCost program fn) := LocalCompiler.Function.callSteps_mono 0 _

/-- The backend-derived core count of the given successful source execution.
Range and call-nesting evidence belongs to that execution, not to a second
correctness proof. Each constructor adds only its emitted runtime work. -/
inductive ExecutionCost {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w : Nat} :
    {depth : Nat} → {Γ : List Ty} → {result : Ty} →
      {stmt : Complexity.Language.Stmt signatures Γ result} →
      {entry finish : Env Γ} → {control : Control result} →
      RealizedExec program w depth stmt entry finish control → Nat → Prop where
  | skip {Γ : List Ty} {result : Ty} {depth : Nat} (entry : Env Γ) :
      ExecutionCost (RealizedExec.skip (program := program) (w := w)
        (result := result) (depth := depth) entry) 0
  | letPrim {Γ : List Ty} {τ result : Ty} {depth : Nat} {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Env Γ} {finish : Env (τ :: Γ)} {control : Control result}
      {fits : PrimFits w entry value}
      {body : RealizedExec program w depth continuation
        (Env.cons (value.eval entry) entry) finish control} {steps : Nat}
      (tail : ExecutionCost body steps) :
      ExecutionCost (.letPrim fits body) (primCodeSize value + steps)
  | seqNormal {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Env Γ} {control : Control result}
      {head : RealizedExec program w depth first entry middle .normal}
      {tail : RealizedExec program w depth second middle finish control}
      {firstSteps secondSteps : Nat}
      (firstCost : ExecutionCost head firstSteps) (secondCost : ExecutionCost tail secondSteps) :
      ExecutionCost (.seqNormal head tail) (firstSteps + 2 + secondSteps)
  | seqReturn {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Env Γ} {value : Value result}
      {head : RealizedExec program w depth first entry finish (.returned value)} {steps : Nat}
      (cost : ExecutionCost head steps) :
      ExecutionCost (.seqReturn (second := second) head) (steps + 3)
  | iteTrue {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Env Γ} {control : Control result}
      {test : condition.eval entry = true}
      {body : RealizedExec program w depth yes entry finish control} {steps : Nat}
      (cost : ExecutionCost body steps) :
      ExecutionCost (.iteTrue (no := no) test body) (steps + 3)
  | iteFalse {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Env Γ} {control : Control result}
      {test : condition.eval entry = false}
      {body : RealizedExec program w depth no entry finish control} {steps : Nat}
      (cost : ExecutionCost body steps) :
      ExecutionCost (.iteFalse (yes := yes) test body) (steps + 2)
  | ret {Γ : List Ty} {result : Ty} {depth : Nat}
      (value : Atom Γ result) (entry : Env Γ)
      {fits : valueToNat (value.eval entry) < 2 ^ w} :
      ExecutionCost (RealizedExec.ret (program := program) (depth := depth) value entry fits)
        (2 * fieldCount result + 2)
  | callReturn {Γ : List Ty} {result : Ty} {depth : Nat} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Env Γ} {calleeFinish : Env signatures[fn].params}
      {value : Value signatures[fn].result} {finish : Env (signatures[fn].result :: Γ)}
      {control : Control result} {arguments : EnvFits w (args.eval entry)}
      {callee : RealizedExec program w depth (program.body fn)
        (args.eval entry) calleeFinish (.returned value)}
      {body : RealizedExec program w (depth + 1) continuation
        (Env.cons value entry) finish control} {calleeSteps bodySteps : Nat}
      (calleeCost : ExecutionCost callee calleeSteps) (bodyCost : ExecutionCost body bodySteps) :
      ExecutionCost (.callReturn arguments callee body)
        (callCost program fn (calleeSteps + 5) + bodySteps)

/-- A successful source execution determines a cost observation without any
proposed bound. This is a proposition about the existing execution, not an
attempt to compute a natural number by inspecting a proof. -/
theorem RealizedExec.exists_cost {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Env Γ} {control : Control result}
    (execution : RealizedExec program w depth stmt entry finish control) :
    ∃ steps, ExecutionCost execution steps := by
  induction execution with
  | skip entry => exact ⟨0, .skip entry⟩
  | letPrim fits body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .letPrim (fits := fits) cost⟩
  | seqNormal head tail ihHead ihTail =>
      obtain ⟨firstSteps, firstCost⟩ := ihHead
      obtain ⟨secondSteps, secondCost⟩ := ihTail
      exact ⟨_, .seqNormal firstCost secondCost⟩
  | seqReturn head ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .seqReturn cost⟩
  | iteTrue test body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .iteTrue (test := test) cost⟩
  | iteFalse test body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .iteFalse (test := test) cost⟩
  | ret value entry fits => exact ⟨_, .ret value entry (fits := fits)⟩
  | callReturn arguments callee body ihCallee ihBody =>
      obtain ⟨calleeSteps, calleeCost⟩ := ihCallee
      obtain ⟨bodySteps, bodyCost⟩ := ihBody
      exact ⟨_, .callReturn (arguments := arguments) calleeCost bodyCost⟩

/-- A conditional bound on the complete lowered function body. Correctness and
termination remain separate source contracts. The bound is uniform over word
width and call capacity whenever the source execution is realizable. -/
def FunctionCostBound {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (pre : Env signatures[fn].params → Prop) (bound : Env signatures[fn].params → Nat) : Prop :=
  ∀ args, pre args → ∀ {w depth finish value}
    (execution : RealizedExec program w depth (program.body fn) args finish (.returned value))
    {steps}, ExecutionCost execution steps → steps + 5 ≤ bound args

namespace FunctionCostBound

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {pre : Env signatures[fn].params → Prop}
variable {bound bound' : Env signatures[fn].params → Nat}

/-- Weaken a mathematical bound without changing the observed computation. -/
theorem mono_bound (h : FunctionCostBound program fn pre bound)
    (budget : ∀ args, pre args → bound args ≤ bound' args) :
    FunctionCostBound program fn pre bound' := by
  intro args hpre w depth finish value execution steps cost
  exact Nat.le_trans (h args hpre execution cost) (budget args hpre)

end FunctionCostBound

end Ram.LanguageCompiler
