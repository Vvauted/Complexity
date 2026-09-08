/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Eval
import Examples.Ram.Factorial

/-!
# Mathematical reasoning about the implemented factorial function

`eval` and `bodyTime` observe the one function defined in
`Ram.Examples.Factorial.functions`. They do not execute its optional stream
driver. The definitions mention neither mathematical factorial nor a proposed
cost; the equations below establish those properties of the implementation.

The initial state is hidden once, then `eval_eq_of_execution` proves that this
view agrees with the returned value at every actual caller state. The example
uses mathlib's `Part`: these are noncomputable proof views, not a new interpreter
or ordinary Lean code accepted by the RAM compiler. Word overflow remains
explicit, and the time observation excludes the enclosing call overhead.
-/

namespace Ram.Examples.FactorialFunction

open Factorial

/-- Observe the implemented function's decoded return value, without an I/O main. -/
noncomputable def eval (n : Word w) : Part Nat :=
  (functions.eval.factorial n 0 (Source.State.initial [])).map (fun result => result.1.toNat)

/-- Observe its actual body count, independently of any bound or specification. -/
noncomputable def bodyTime (n : Word w) : Part Nat :=
  functions.bodyTime.factorial n 0 (Source.State.initial [])

/-- Every word argument terminates with factorial modulo the word range. -/
theorem eval_eq (n : Word w) :
    eval n = Part.some (Nat.factorial n.toNat % 2 ^ w) := by
  have execution := function_runs 0 n.toNat n.isLt (Source.State.initial [])
  have result := execution.eval_eq_some
  simpa only [Word.ofNat_toNat_self, eval, Part.map_some, value_toNat, factorialNat] using
    congrArg (Part.map (fun result : Word w × Source.State w => result.1.toNat)) result

/-- When the result fits, an ordinary function-value equation states correctness. -/
theorem eval_eq_factorial (n : Word w) (hfit : Nat.factorial n.toNat < 2 ^ w) :
    eval n = Part.some (Nat.factorial n.toNat) := by
  rw [eval_eq, Nat.mod_eq_of_lt hfit]

/-- Mathematical properties of the observed value reuse mathlib directly. -/
theorem eval_pos (n : Word w) (hfit : Nat.factorial n.toNat < 2 ^ w)
    {result : Nat} (hresult : result ∈ eval n) : 0 < result := by
  rw [eval_eq_factorial n hfit, Part.mem_some_iff] at hresult
  rw [hresult]
  exact Nat.factorial_pos _

/-- Hiding the initial state did not change the function's meaning: the view
agrees with a call in any shared state, and that state is preserved on return. -/
theorem eval_eq_of_execution {heapLimit depth : Nat} {n result : Word w}
    {entry finish : Source.State w}
    (execution : Source.FunctionExec functions.program heapLimit depth factorial
      (functions.arguments.factorial n) entry result finish) :
    eval n = Part.some result.toNat ∧ finish = entry := by
  have canonical := function_runs heapLimit n.toNat n.isLt entry
  simp only [Word.ofNat_toNat_self] at canonical
  obtain ⟨rfl, rfl⟩ := execution.deterministic canonical
  exact ⟨by simpa only [value_toNat, factorialNat] using eval_eq n, rfl⟩

/-- The time equation is proved from the existing exact body execution,
separately from the function's result theorem. -/
theorem bodyTime_eq (n : Word w) : bodyTime n = Part.some (37 * n.toNat + 4) := by
  let entry : Source.State w := Source.State.initial []
  have measured := body_measured 0 n.toNat
    (entry.enter (functions.arguments.factorial n)) n.isLt
    (by simp [Source.State.enter, functions.arguments.factorial])
  have invocation := Source.FunctionMeasuredExec.of_body
    (f := factorial) (functions.arguments_length.factorial n) (by decide)
    measured (by trivial)
  exact invocation.bodyTime_eq_some

/-- The time observation agrees with every actual invocation, not just the
canonical initial state hidden by `bodyTime`. -/
theorem bodyTime_eq_of_execution {control heapLimit depth steps : Nat} {n result : Word w}
    {entry finish : Source.State w}
    (execution : Source.FunctionMeasuredExec control functions.program heapLimit depth factorial
      (functions.arguments.factorial n) steps entry result finish) :
    bodyTime n = Part.some steps := by
  have measured := body_measured heapLimit n.toNat
    (entry.enter (functions.arguments.factorial n)) n.isLt
    (by simp [Source.State.enter, functions.arguments.factorial])
  have invocation := Source.FunctionMeasuredExec.of_body
    (f := factorial) (functions.arguments_length.factorial n) (by decide)
    measured (by trivial)
  rw [bodyTime_eq, (execution.deterministic invocation).1]

end Ram.Examples.FactorialFunction
