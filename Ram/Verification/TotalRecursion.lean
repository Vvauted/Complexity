/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Recursion
import Ram.Verification.Total

/-!
# Recursive function correctness without a time budget

`TotalSpec` separates a function's functional specification from a later time
analysis. Its proof still establishes termination, safe heap access and a
call-depth bound. These are the source semantics needed by the compiler; no
instruction count, reserved-register boundary or unused time appears in the
body proof or its recursive hypotheses.

`TotalSpec.Correct.wp_call` composes these specifications at actual calls.
Existing measured specifications can be reused through `Spec.toTotal` and
`Spec.Correct.total`, without changing the function or its execution.
-/

namespace Ram.Source.Recursion

/-- An argument-indexed total specification, independent of a time analysis. -/
structure TotalSpec (f : Func) (w : Nat) (Arg : Type) where
  pre : Arg → State w → Prop
  post : Arg → State w → State w → Prop
  depth : Arg → Nat

namespace TotalSpec

variable {f : Func} {w heapLimit : Nat} {Arg : Type} {program : Program}

/-- The body terminates safely and establishes its functional postcondition.
The final return expression is safe in that same callee state. -/
def Correct (spec : TotalSpec f w Arg) (program : Program)
    (heapLimit : Nat) (arg : Arg) : Prop :=
  TotalRelContract program heapLimit (spec.depth arg) f.body (spec.pre arg)
    (fun entry finish => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
      spec.post arg entry finish)

/-- Prove a recursive function using any well-founded mathematical relation.
The recursive hypotheses are callable total specifications, with no time
budget or measured execution tree to construct. -/
theorem verify_wellFounded (spec : TotalSpec f w Arg) {r : Arg → Arg → Prop}
    (wf : WellFounded r)
    (body : ∀ arg, (∀ smaller, r smaller arg → spec.Correct program heapLimit smaller) →
      ∀ entry, spec.pre arg entry →
        Verification.TotalWP program heapLimit (spec.depth arg) f.body
          (fun finish => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
            spec.post arg entry finish) entry) :
    ∀ arg, spec.Correct program heapLimit arg := by
  intro arg
  induction arg using wf.induction with
  | h arg ih => exact body arg ih

/-- Apply a verified function while retaining the caller's locals and the
callee's shared-memory and I/O effects. Only the argument precondition, safe
calling convention and the desired functional continuation remain to prove. -/
theorem Correct.wp_call {spec : TotalSpec f w Arg} {arg : Arg}
    (correct : spec.Correct program heapLimit arg)
    {fn dst depth : Nat} {args : List Expr} {caller : State w}
    {post : State w → Prop}
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit caller.regs caller.mem)
    (pre : spec.pre arg (caller.enter (args.map caller.eval)))
    (nesting : spec.depth arg + 1 ≤ depth)
    (continuation : ∀ callee,
      spec.post arg (caller.enter (args.map caller.eval)) callee →
        post (caller.leave callee dst f.result)) :
    Verification.TotalWP program heapLimit depth (.call dst fn args) post caller := by
  obtain ⟨callee, execution, reads, result⟩ :=
    correct (caller.enter (args.map caller.eval)) pre
  exact ⟨_, (SafeExec.call (dst := dst) lookup arity frame arguments execution reads).mono
    nesting, continuation callee result⟩

end TotalSpec

namespace Spec

variable {f : Func} {w n heapLimit : Nat} {Arg : Type} {program : Program}

/-- Forget a proposed time budget while retaining the same function contract. -/
def toTotal (spec : Spec f w Arg) : TotalSpec f w Arg where
  pre := spec.pre
  post := spec.post
  depth := spec.depth

/-- A measured function proof is also a budget-free total proof, for the same
entry and final states. This bridge does not re-run or alter the function. -/
theorem Correct.total {spec : Spec f w Arg} {arg : Arg}
    (correct : spec.Correct n program heapLimit arg) :
    spec.toTotal.Correct program heapLimit arg := by
  intro entry pre
  obtain ⟨steps, finish, execution, post, _⟩ := correct entry pre
  exact ⟨finish, execution.erase, post⟩

end Spec

end Ram.Source.Recursion
