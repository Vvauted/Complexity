/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.StraightLine

/-!
# Compositional exact instruction counts

`Ram.Source.TimeExact` is an equality about the existing measured execution,
not a new execution relation or a cost annotation. Like `TimeBound`, it is
conditional on completed execution and does not establish termination.

Straight-line code reuses its proved compiled length. Branches and calls add
the actual generated instructions, and a constant-cost continuation needs no
intermediate functional invariant. A safe execution can subsequently be given
the exact count without rebuilding its execution tree or proving its endpoint
again. Functional correctness and termination remain independent of the cost.

Heap and call-depth indices retain their original meaning. These conditional
equalities cannot be enlarged to other capacities merely by monotonicity: an
insufficient capacity may make the premise vacuous.
-/

namespace Ram.Source

/-- Every completed execution at the stated capacities has the given count.
The cost expression is a property to prove, never an input to the program. -/
def TimeExact (control : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P : State w → Prop) (cost : State w → Nat) : Prop :=
  ∀ s, P s → ∀ steps t,
    LocalMeasuredExec control program heapLimit depth stmt steps s t → steps = cost s

namespace TimeExact

variable {w control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P : State w → Prop} {cost cost' : State w → Nat}

/-- Rewrite the mathematical count without changing its execution or domain. -/
theorem congr_cost (h : TimeExact control program heapLimit depth stmt P cost)
    (equal : ∀ s, P s → cost s = cost' s) :
    TimeExact control program heapLimit depth stmt P cost' :=
  fun s hs steps t execution => (h s hs steps t execution).trans (equal s hs)

/-- An exact equation supplies the corresponding conditional upper bound. -/
theorem timeBound (h : TimeExact control program heapLimit depth stmt P cost) :
    TimeBound control program heapLimit depth stmt P cost :=
  fun s hs steps t execution => Nat.le_of_eq (h s hs steps t execution)

/-- Every completed straight-line block has its already proved compiled length.
Memory and input safety are supplied by the execution, not assumed away here. -/
theorem of_isStraightLine (straight : stmt.IsStraightLine) :
    TimeExact control program heapLimit depth stmt P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) stmt) :=
  fun _ _ _ _ execution => execution.steps_eq_stmtSize straight

/-- A state-independent continuation count needs no intermediate invariant or
new termination proof. Both counts refer to the actual component executions. -/
theorem seq_const {first second : Stmt} {firstCost : State w → Nat} {secondCost : Nat}
    (firstTime : TimeExact control program heapLimit depth first P firstCost)
    (secondTime : TimeExact (w := w) control program heapLimit depth second
      (fun _ => True) (fun _ => secondCost)) :
    TimeExact control program heapLimit depth (.seq first second) P
      (fun s => firstCost s + secondCost) := by
  intro s hs steps t execution
  cases execution with
  | seq first second =>
    dsimp only
    rw [firstTime s hs _ _ first, secondTime _ trivial _ _ second]

/-- A known zero guard charges its evaluation, conditional jump and false
branch, without asking for a cost proof of an unreachable true branch. -/
theorem ite_of_eq_zero {condition : Expr} {yes no : Stmt}
    (zero : ∀ s, P s → s.eval condition = 0)
    (branch : TimeExact control program heapLimit depth no P cost) :
    TimeExact control program heapLimit depth (.ite condition yes no) P
      (fun s => (condition.compile (ABI.scratch control)).length + 1 + cost s) := by
  intro s hs steps t execution
  cases execution with
  | iteTrue _ nonzero _ => exact False.elim (nonzero (zero s hs))
  | iteFalse _ _ body =>
    exact congrArg (fun n => (condition.compile (ABI.scratch control)).length + 1 + n)
      (branch s hs _ _ body)

/-- A known nonzero guard also charges the true branch's final jump past the
false branch. Only the branch selected by the mathematical precondition is used. -/
theorem ite_of_ne_zero {condition : Expr} {yes no : Stmt}
    (nonzero : ∀ s, P s → s.eval condition ≠ 0)
    (branch : TimeExact control program heapLimit depth yes P cost) :
    TimeExact control program heapLimit depth (.ite condition yes no) P
      (fun s => (condition.compile (ABI.scratch control)).length + 1 + cost s + 1) := by
  intro s hs steps t execution
  cases execution with
  | iteTrue _ _ body =>
    exact congrArg (fun n => (condition.compile (ABI.scratch control)).length + 1 + n + 1)
      (branch s hs _ _ body)
  | iteFalse _ zero _ => exact False.elim (nonzero s hs zero)

/-- A recursive or ordinary function call reuses the callee's body count at
its actual arguments. Setup, return and receipt costs are compiler-derived;
the rule handles the measured call tree and requires no callee endpoint. -/
theorem call {fn : Nat} {dsts : List Reg} {args : List Expr} {f : Func}
    {calleePre : State w → Prop} {bodyCost : State w → Nat}
    (lookup : program[fn]? = some f)
    (pre : ∀ s, P s → calleePre (s.enter (args.map s.eval)))
    (body : TimeExact control program heapLimit depth f.body calleePre bodyCost) :
    TimeExact control program heapLimit (depth + 1) (.call dsts fn args) P
      (fun s => (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bodyCost (s.enter (args.map s.eval)) +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length) := by
  intro s hs steps t execution
  cases execution with
  | call found _ _ _ _ callee _ =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have count := body _ (pre s hs) _ _ callee
    dsimp only
    rw [count]

end TimeExact

/-- Attach a separately proved count to the same safe execution and endpoint.
This uses existence of measurement, not a second functional or termination proof. -/
theorem SafeExec.measured_of_timeExact {control heapLimit depth : Nat} {program : Program}
    {stmt : Stmt} {s t : State w} {P : State w → Prop} {cost : State w → Nat}
    (execution : SafeExec program heapLimit depth stmt s t)
    (costProof : TimeExact control program heapLimit depth stmt P cost) (pre : P s) :
    LocalMeasuredExec control program heapLimit depth stmt (cost s) s t := by
  obtain ⟨steps, measured⟩ := execution.exists_localMeasured control
  exact costProof s pre steps t measured ▸ measured

end Ram.Source
