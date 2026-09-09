/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CodeSize
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Costs of realized source executions

`ExecutionCost` observes the same source execution as `RealizedExec`. Its rules
count the operations emitted by lowering, including actual buffer operations, the private return
flag and actual callee-frame work. The observation does not supply termination,
change source behavior, or ask a program author to assign instruction prices.

Counts here cover `lowerStmtCore`. A returning function body additionally runs
its flag initialization, for two transitions. Its specialized exit needs no
normal-continuation dispatch. The outer
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
      {entry finish : Complexity.Language.State Γ} → {control : Control result} →
      RealizedExec program w depth stmt entry finish control → Nat → Prop where
  | skip {Γ : List Ty} {result : Ty} {depth : Nat} (entry : Complexity.Language.State Γ) :
      ExecutionCost (RealizedExec.skip (program := program) (w := w)
        (result := result) (depth := depth) entry) 0
  | letPrim {Γ : List Ty} {τ result : Ty} {depth : Nat} {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
      {control : Control result} {fits : PrimFits w entry.locals value}
      {body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (value.eval entry.locals) entry) finish control}
      {steps : Nat}
      (tail : ExecutionCost body steps) :
      ExecutionCost (.letPrim fits body) (primCodeSize value + steps)
  | read {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (kind.toTy :: Γ)} {control : Control result}
      {value : CellValue kind} {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {indexFits : index.eval entry.locals < 2 ^ w}
      {loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value}
      {valueFits : ValueFits w (kind.toValue value)}
      {body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) finish control}
      {steps : Nat} (tail : ExecutionCost body steps) :
      ExecutionCost (.read bufferFits indexFits loaded valueFits body) (readCodeSize + steps)
  | write {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : Complexity.Language.State Γ} {heap : Heap}
      {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {indexFits : index.eval entry.locals < 2 ^ w}
      {valueFits : ValueFits w (value.eval entry.locals)}
      {written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap} :
      ExecutionCost (RealizedExec.write (program := program) (result := result) (depth := depth)
        bufferFits indexFits valueFits written) writeCodeSize
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)} {control : Control result}
      {view : Buffer kind} {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {offsetFits : offset.eval entry.locals < 2 ^ w}
      {lengthFits : length.eval entry.locals < 2 ^ w}
      {sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view}
      {viewFits : ValueFits w (τ := .buffer kind) view}
      {body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons view entry) finish control}
      {steps : Nat} (tail : ExecutionCost body steps) :
      ExecutionCost (.slice bufferFits offsetFits lengthFits sliced viewFits body)
        (sliceCodeSize + steps)
  | seqNormal {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Complexity.Language.State Γ} {control : Control result}
      {head : RealizedExec program w depth first entry middle .normal}
      {tail : RealizedExec program w depth second middle finish control}
      {firstSteps secondSteps : Nat}
      (firstCost : ExecutionCost head firstSteps) (secondCost : ExecutionCost tail secondSteps) :
      ExecutionCost (.seqNormal head tail) (firstSteps + 2 + secondSteps)
  | seqReturn {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {value : Value result}
      {head : RealizedExec program w depth first entry finish (.returned value)} {steps : Nat}
      (cost : ExecutionCost head steps) :
      ExecutionCost (.seqReturn (second := second) head) (steps + 3)
  | iteTrue {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = true}
      {body : RealizedExec program w depth yes entry finish control} {steps : Nat}
      (cost : ExecutionCost body steps) :
      ExecutionCost (.iteTrue (no := no) test body) (steps + 3)
  | iteFalse {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = false}
      {body : RealizedExec program w depth no entry finish control} {steps : Nat}
      (cost : ExecutionCost body steps) :
      ExecutionCost (.iteFalse (yes := yes) test body) (steps + 2)
  | ret {Γ : List Ty} {result : Ty} {depth : Nat}
      (value : Atom Γ result) (entry : Complexity.Language.State Γ)
      {fits : ValueFits w (value.eval entry.locals)} :
      ExecutionCost (RealizedExec.ret (program := program) (depth := depth) value entry fits)
        (2 * fieldCount result + 2)
  | callReturn {Γ : List Ty} {result : Ty} {depth : Nat} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {calleeFinish : Complexity.Language.State signatures[fn].params}
      {value : Value signatures[fn].result}
      {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
      {control : Control result} {arguments : EnvFits w (args.eval entry.locals)}
      {callee : RealizedExec program w depth (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
      {body : RealizedExec program w (depth + 1) continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
      {calleeSteps bodySteps : Nat}
      (calleeCost : ExecutionCost callee calleeSteps) (bodyCost : ExecutionCost body bodySteps) :
      ExecutionCost (.callReturn arguments callee body)
        (callCost program fn (calleeSteps + 2) + bodySteps)

/-- A successful source execution determines a cost observation without any
proposed bound. This is a proposition about the existing execution, not an
attempt to compute a natural number by inspecting a proof. -/
theorem RealizedExec.exists_cost {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : RealizedExec program w depth stmt entry finish control) :
    ∃ steps, ExecutionCost execution steps := by
  induction execution with
  | skip entry => exact ⟨0, .skip entry⟩
  | letPrim fits body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .letPrim (fits := fits) cost⟩
  | read bufferFits indexFits loaded valueFits body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .read (bufferFits := bufferFits) (indexFits := indexFits)
        (loaded := loaded) (valueFits := valueFits) cost⟩
  | write bufferFits indexFits valueFits written =>
      exact ⟨_, .write (bufferFits := bufferFits) (indexFits := indexFits)
        (valueFits := valueFits) (written := written)⟩
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .slice (bufferFits := bufferFits) (offsetFits := offsetFits)
        (lengthFits := lengthFits) (sliced := sliced) (viewFits := viewFits) cost⟩
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
    (pre : Env signatures[fn].params → Heap → Prop)
    (bound : Env signatures[fn].params → Heap → Nat) : Prop :=
  ∀ args heap, pre args heap → ∀ {w depth finish value}
    (execution : RealizedExec program w depth (program.body fn)
      ⟨args, heap⟩ finish (.returned value))
    {steps}, ExecutionCost execution steps → steps + 2 ≤ bound args heap

namespace FunctionCostBound

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {pre : Env signatures[fn].params → Heap → Prop}
variable {bound bound' : Env signatures[fn].params → Heap → Nat}

/-- Weaken a mathematical bound without changing the observed computation. -/
theorem mono_bound (h : FunctionCostBound program fn pre bound)
    (budget : ∀ args heap, pre args heap → bound args heap ≤ bound' args heap) :
    FunctionCostBound program fn pre bound' := by
  intro args heap hpre w depth finish value execution steps cost
  exact Nat.le_trans (h args heap hpre execution cost) (budget args heap hpre)

end FunctionCostBound

end Ram.LanguageCompiler
