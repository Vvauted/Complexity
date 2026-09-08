/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Time

/-!
# Calling a function with a separate time bound

`FunctionTimeBound.call` reuses a bound stated on arguments and caller state
at a source call. The caller need not reopen the callee's body or parameter
frame. Argument evaluation, frame setup, return and jumps retain their actual
compiler-derived counts. This conditional bound neither supplies termination
nor changes the independent functional contract.

`FunctionTimeBound.of_body_at` starts a function proof at its actual parameter
bindings. `call_at` applies a callee's separate bound there; `call_seq_at` also
uses its budget-free postcondition to expose the actual returned value and
shared state to the remainder's time proof. No intermediate register invariant
or callee implementation needs to be reconstructed at a call site.
-/

namespace Ram.Source.FunctionTimeBound

/-- Prove a function's body bound directly at its actual parameter bindings.
The entry state is retained as a logical parameter, without requiring a
separate representation predicate for the callee's local frame. -/
theorem of_body_at {w control heapLimit depth : Nat} {program : Program} {f : Func}
    {P : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (body : ∀ args entry, P args entry →
      TimeBound control program heapLimit depth f.body (fun s => s = entry.enter args)
        (fun _ => bound args entry)) :
    FunctionTimeBound control program heapLimit depth f P bound := by
  rintro args entry pre steps value finish ⟨_, _, callee, execution, _, _, _⟩
  exact body args entry pre _ rfl steps callee execution

/-- Apply a function's body-time bound to a call at its actual argument values.
The generated call blocks account for all work outside the callee's body. -/
theorem call {w control heapLimit depth : Nat} {program : Program} {f : Func}
    {P : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f P bound)
    {fn : Nat} {dsts : List Reg} {args : List Expr} {R : State w → Prop}
    (lookup : program[fn]? = some f)
    (pre : ∀ entry, R entry → P (args.map entry.eval) entry) :
    TimeBound control program heapLimit (depth + 1) (.call dsts fn args) R
      (fun entry => (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bound (args.map entry.eval) entry +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length) := by
  intro entry hp steps finish execution
  cases execution with
  | call found arity _ frame arguments body results =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have invocation := FunctionMeasuredExec.of_body
      (by simpa only [List.length_map] using arity) frame body results
    have bounded := time _ entry (pre entry hp) _ _ _ invocation
    dsimp only
    omega

/-- Apply a conditional callee bound at one caller state and compare its
actual call overhead and body bound with the desired total. No termination
or functional-correctness premise is needed for this conditional conclusion. -/
theorem call_at {w control heapLimit depth : Nat} {program : Program} {f : Func}
    {P : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f P bound)
    {fn : Nat} {dsts : List Reg} {args : List Expr} {entry : State w} {overall : Nat}
    (lookup : program[fn]? = some f) (pre : P (args.map entry.eval) entry)
    (budget : (ABI.callPrefixLocals control f.locals args 0).length + 1 +
      bound (args.map entry.eval) entry +
      (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length ≤ overall) :
    TimeBound control program heapLimit (depth + 1) (.call dsts fn args)
      (fun s => s = entry) (fun _ => overall) := by
  apply (time.call (R := fun s => s = entry) lookup (by rintro s rfl; exact pre)).mono_budget
  rintro s rfl
  exact budget

/-- Compose a call's independent correctness and time specifications with
the remainder of the actual caller. The continuation receives the returned
value, shared effects and restored caller locals. Its bound may depend on
those actual values; all call overhead remains charged by the compiler. -/
theorem call_seq_at {w control heapLimit depth : Nat} {program : Program} {f : Func}
    {P : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f P bound)
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    (correct : FunctionContract program heapLimit depth f P Q)
    {fn : Nat} {dsts : List Reg} {args : List Expr}
    {tail : Stmt} {entry : State w} {overall : Nat}
    (lookup : program[fn]? = some f)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (pre : P (args.map entry.eval) entry) (nextBound : List (Word w) → State w → Nat)
    (continuation : ∀ value finish, Q (args.map entry.eval) entry value finish →
      finish.regs = entry.regs →
      TimeBound control program heapLimit (depth + 1) tail
        (fun s => s = finish.setRegs dsts value) (fun _ => nextBound value finish))
    (budget : ∀ value finish, Q (args.map entry.eval) entry value finish →
      finish.regs = entry.regs →
      (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bound (args.map entry.eval) entry +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length +
        nextBound value finish ≤ overall) :
    TimeBound control program heapLimit (depth + 1) (.seq (.call dsts fn args) tail)
      (fun s => s = entry) (fun _ => overall) := by
  obtain ⟨value, finish, invocation, post⟩ := correct _ entry pre
  have firstTime := time.call (R := fun s => s = entry) (dsts := dsts) lookup
    (by rintro s rfl; exact pre)
  rintro s rfl steps last execution
  cases execution with
  | seq first second =>
      have resultCount : dsts.length = f.results.length := by
        cases first with
        | call found _ count _ _ _ _ =>
          have same : _ = f := Option.some.inj (found.symm.trans lookup)
          simpa only [same] using count
      have same :=
        (invocation.call lookup resultCount arguments).deterministic first.erase
      rw [← same] at second
      have firstBound := firstTime _ rfl _ _ first
      have secondBound := continuation value finish post invocation.regs_eq _ rfl _ _ second
      exact Nat.le_trans (Nat.add_le_add firstBound secondBound)
        (budget value finish post invocation.regs_eq)

end Ram.Source.FunctionTimeBound
