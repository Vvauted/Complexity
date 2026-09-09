/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Structured bounds on source execution costs

`StmtCostBound` bounds the existing compiler-derived `ExecutionCost` observation
at an actual source environment. It does not define another execution or cost
interpreter, and it supplies neither correctness nor termination. Bounds are
uniform over word widths and call capacities whenever execution is realizable.

The composition rules keep primitive values, branch conditions and actual callee
returns in the source language. Callee bounds already include the callee's body
wrapper; `FunctionCostBound.of_stmt` adds the enclosing function's wrapper once.
Proposed bounds never enter the program or assign prices to its instructions.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A conditional upper bound on every realized execution of a source statement
from the given entry. Normal continuation and early return are both covered. -/
def StmtCostBound {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Complexity.Language.Program signatures)
    (stmt : Complexity.Language.Stmt signatures Γ result) (entry : Env Γ) (bound : Nat) : Prop :=
  ∀ {w depth finish control}
    (execution : RealizedExec program w depth stmt entry finish control)
    {steps}, ExecutionCost execution steps → steps ≤ bound

namespace StmtCostBound

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Complexity.Language.Program signatures}
variable {stmt : Complexity.Language.Stmt signatures Γ result} {entry : Env Γ}
variable {bound bound' : Nat}

/-- Weaken a bound on the same observed computation. -/
theorem mono (h : StmtCostBound program stmt entry bound) (budget : bound ≤ bound') :
    StmtCostBound program stmt entry bound' := by
  intro w depth finish control execution steps cost
  exact Nat.le_trans (h execution cost) budget

/-- An empty source statement emits no core instructions. -/
theorem skip (entry : Env Γ) :
    StmtCostBound program (.skip : Complexity.Language.Stmt signatures Γ result) entry 0 := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- Return accounting includes the actual result fields and private return flag. -/
theorem ret (value : Atom Γ result) (entry : Env Γ) :
    StmtCostBound program (.ret value) entry (2 * fieldCount result + 2) := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- A binding charges its compiled primitive and continues at its actual
mathematical value. No range or termination proof is required for this bound. -/
theorem letPrim {τ : Ty} (value : Prim Γ τ)
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (body : StmtCostBound program continuation (Env.cons (value.eval entry) entry) bound) :
    StmtCostBound program (.letPrim value continuation) entry (primCodeSize value + bound) := by
  intro w depth finish control execution steps cost
  cases cost with
  | letPrim tail => exact Nat.add_le_add_left (body _ tail) _

/-- A branch bound uses the actual guard decision. The true path includes the
extra jump past the unselected branch; neither path charges the other's body. -/
theorem ite {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesCost : condition.eval entry = true → StmtCostBound program yes entry yesBound)
    (noCost : condition.eval entry = false → StmtCostBound program no entry noBound) :
    StmtCostBound program (.ite condition yes no) entry
      (if condition.eval entry then yesBound + 3 else noBound + 2) := by
  intro w depth finish control execution steps cost
  cases cost with
  | @iteTrue Γ result depth condition yes no entry finish control test body steps bodyCost =>
      simpa only [test, ↓reduceIte] using Nat.add_le_add_right (yesCost test body bodyCost) 3
  | @iteFalse Γ result depth condition yes no entry finish control test body steps bodyCost =>
      simpa only [test, Bool.false_eq_true, ↓reduceIte] using
        Nat.add_le_add_right (noCost test body bodyCost) 2

/-- A uniformly bounded continuation composes without an intermediate
correctness proof. Normal continuation pays two guard instructions and executes
the tail; early return pays three guard/jump instructions and skips the tail. -/
theorem seq {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound secondBound : Nat}
    (head : StmtCostBound program first entry firstBound)
    (tail : ∀ middle, StmtCostBound program second middle secondBound) :
    StmtCostBound program (.seq first second) entry
      (firstBound + max (2 + secondBound) 3) := by
  intro w depth finish control execution steps cost
  cases cost with
  | seqNormal firstCost secondCost =>
      calc
        _ ≤ firstBound + 2 + secondBound :=
          Nat.add_le_add (Nat.add_le_add_right (head _ firstCost) 2) (tail _ _ secondCost)
        _ = firstBound + (2 + secondBound) := Nat.add_assoc _ _ _
        _ ≤ firstBound + max (2 + secondBound) 3 :=
          Nat.add_le_add_left (Nat.le_max_left _ _) _
  | seqReturn firstCost =>
      exact Nat.le_trans (Nat.add_le_add_right (head _ firstCost) 3)
        (Nat.add_le_add_left (Nat.le_max_right _ _) _)

/-- Compose a separate callee bound with its actual returned-value continuation.
The result premise concerns only completed source calls: use an existing
`FunctionTotal.postcondition`, or `True` when the bound needs no result property.
It does not require termination, expose a callee environment to the caller, or
charge the callee's body wrapper twice. -/
theorem call {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {pre : Env signatures[fn].params → Prop} {calleeBound : Env signatures[fn].params → Nat}
    {post : Value signatures[fn].result → Prop} {nextBound : Value signatures[fn].result → Nat}
    (callee : FunctionCostBound program fn pre calleeBound) (hpre : pre (args.eval entry))
    (returned : ∀ {finish value},
      Complexity.Language.Exec program (program.body fn) (args.eval entry) finish (.returned value) →
        post value)
    (body : ∀ value, post value →
      StmtCostBound program continuation (Env.cons value entry) (nextBound value))
    (combine : ∀ value, post value →
      callCost program fn (calleeBound (args.eval entry)) + nextBound value ≤ bound) :
    StmtCostBound program (.call fn args continuation) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments calleeExec bodyExec calleeSteps bodySteps calleeCost bodyCost =>
      have property := returned calleeExec.erase
      have calleeLe := callee _ hpre calleeExec calleeCost
      have bodyLe := body _ property bodyExec bodyCost
      exact Nat.le_trans
        (Nat.add_le_add (callCost_mono program fn calleeLe) bodyLe)
        (combine _ property)

end StmtCostBound

namespace FunctionCostBound

/-- A bound on the source body yields a bound on the complete lowered function
body, adding its initialization and returning dispatch exactly once. This is
still conditional on a realized returned execution, not a termination claim. -/
theorem of_stmt {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Prop} {coreBound : Env signatures[fn].params → Nat}
    (body : ∀ args, pre args →
      StmtCostBound program (program.body fn) args (coreBound args)) :
    FunctionCostBound program fn pre (fun args => coreBound args + 5) := by
  intro args hpre w depth finish value execution steps cost
  exact Nat.add_le_add_right (body args hpre execution cost) 5

end FunctionCostBound

end Ram.LanguageCompiler
