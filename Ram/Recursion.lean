/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification

/-!
# Recursive function contracts

A `Spec` describes one ordinary function using ghost arguments. Its relational
postcondition can preserve the complete entry state, while its depth and time
bounds are proof obligations, not annotations in the executed program.

`Spec.verify_wellFounded` verifies the body under already verified contracts
for smaller arguments. At a recursive call, `Spec.Correct.wp_call` turns one
such hypothesis into a caller-side weakest precondition: argument evaluation,
fresh locals, restoration, return-expression safety and the compiler's actual
call overhead are handled once here. Straight-line and branching code use the
ordinary `WP` rules. No program proof needs to assemble measured call trees.
-/

namespace Ram.Source.Recursion

/-- An argument-indexed specification for a fixed source function. -/
structure Spec (f : Func) (w : Nat) (Arg : Type) where
  pre : Arg → State w → Prop
  post : Arg → State w → State w → Prop
  depth : Arg → Nat
  budget : Arg → Nat

namespace Spec

variable {f : Func} {w n heapLimit : Nat} {Arg : Type} {program : Program}

/-- The function body terminates within its proposed bound, and its return
expression is safe to evaluate in the actual final callee state. -/
def Correct (spec : Spec f w Arg) (n : Nat) (program : Program)
    (heapLimit : Nat) (arg : Arg) : Prop :=
  RelContract n program heapLimit (spec.depth arg) f.body (spec.pre arg)
    (fun entry finish => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
      spec.post arg entry finish) (fun _ => spec.budget arg)

/-- Total invocation budget, read directly from generated setup and return
blocks plus the body bound. It includes both jumps and receipt of the result. -/
def callBudget (spec : Spec f w Arg) (n : Nat) (args : List Expr) (arg : Arg) : Nat :=
  (ABI.callPrefixLocals n f.locals args 0).length + 1 + spec.budget arg +
    (ABI.returnCodeLocals n f.locals f.result).length + 1

/-- Prove a recursive function by verifying its body once for a symbolic
argument. Recursive hypotheses are callable contracts, not execution trees.
The relation can be a natural measure, lexicographic order or any well-founded
relation appropriate to the mathematical algorithm. -/
theorem verify_wellFounded (spec : Spec f w Arg) {r : Arg → Arg → Prop}
    (wf : WellFounded r)
    (body : ∀ arg, (∀ smaller, r smaller arg → spec.Correct n program heapLimit smaller) →
      ∀ entry, spec.pre arg entry →
        Verification.WP n program heapLimit (spec.depth arg) f.body
          (fun finish _ => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
            spec.post arg entry finish) entry (spec.budget arg)) :
    ∀ arg, spec.Correct n program heapLimit arg := by
  intro arg
  induction arg using wf.induction with
  | h arg ih => exact Verification.verify_rel (body arg ih)

/-- Use a proved recursive hypothesis as an ordinary call inside a WP proof.
The continuation sees restored caller locals and the callee's shared-memory
and I/O effects through `State.leave`. Extra available nesting depth is safe;
unused time is threaded to the continuation, never reset. -/
theorem Correct.wp_call {spec : Spec f w Arg} {arg : Arg}
    (correct : spec.Correct n program heapLimit arg)
    {fn dst depth fuel : Nat} {args : List Expr} {caller : State w}
    {post : State w → Nat → Prop}
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit caller.regs caller.mem)
    (pre : spec.pre arg (caller.enter (args.map caller.eval)))
    (nesting : spec.depth arg + 1 ≤ depth)
    (budget : spec.callBudget n args arg ≤ fuel)
    (continuation : ∀ callee,
      spec.post arg (caller.enter (args.map caller.eval)) callee →
      ∀ remaining, fuel - spec.callBudget n args arg ≤ remaining →
        post (caller.leave callee dst f.result) remaining) :
    Verification.WP n program heapLimit depth (.call dst fn args) post caller fuel := by
  obtain ⟨steps, callee, execution, ⟨reads, result⟩, hsteps⟩ :=
    correct (caller.enter (args.map caller.eval)) pre
  change steps ≤ spec.budget arg at hsteps
  have call := LocalMeasuredExec.call (dst := dst) lookup arity frame arguments execution reads
    |>.mono nesting
  have bounded :
      (ABI.callPrefixLocals n f.locals args 0).length + 1 + steps +
        (ABI.returnCodeLocals n f.locals f.result).length + 1 ≤
          spec.callBudget n args arg := by
    unfold callBudget
    omega
  exact ⟨_, _, call, Nat.le_trans bounded budget,
    continuation callee result _ (by omega)⟩

end Spec

end Ram.Source.Recursion
