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
-/

namespace Ram.Source.FunctionTimeBound

/-- Apply a function's body-time bound to a call at its actual argument values.
The generated call blocks account for all work outside the callee's body. -/
theorem call {w control heapLimit depth : Nat} {program : Program} {f : Func}
    {P : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f P bound)
    {dst fn : Nat} {args : List Expr} {R : State w → Prop}
    (lookup : program[fn]? = some f)
    (pre : ∀ entry, R entry → P (args.map entry.eval) entry) :
    TimeBound control program heapLimit (depth + 1) (.call dst fn args) R
      (fun entry => (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bound (args.map entry.eval) entry +
        (ABI.returnCodeLocals control f.locals f.result).length + 1) := by
  intro entry hp steps finish execution
  cases execution with
  | call found arity frame arguments body result =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have invocation := FunctionMeasuredExec.of_body
      (by simpa only [List.length_map] using arity) frame body result
    have bounded := time _ entry (pre entry hp) _ _ _ invocation
    dsimp only
    omega

end Ram.Source.FunctionTimeBound
