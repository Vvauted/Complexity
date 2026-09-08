/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Basic

/-!
# Named RAM program examples
-/

namespace Ram.Named.Examples

/-- Forward and mutual references are resolved once. Local `even` has the same
spelling as a function, but reading it and calling it use separate tables. -/
def parity : Bundle := ram_program% {
  fn even(n) locals (answer) {
    if n {
      answer := call odd(n - 1);
    } else {
      answer := 1;
    }
    return answer;
  }
  fn odd(even) locals (answer) {
    if even {
      answer := call even(even - 1);
    } else {
      answer := 0;
    }
    return answer;
  }
  main locals (input, answer) {
    read input;
    answer := call even(input);
    write answer;
  }
}

/-- The forward call and the same-spelling call both have the intended static
targets; their arguments still read each function's parameter register. -/
theorem parity_expands : parity =
    { registers := 2
      declarations :=
        [("even", ⟨1, 2,
          .ite (.var 0) (.call [1] 1 [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.const 1)), [.var 1]⟩),
         ("odd", ⟨1, 2,
          .ite (.var 0) (.call [1] 0 [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.const 0)), [.var 1]⟩)]
      main := .seq (.read 0) (.seq (.call [1] 0 [.var 0]) (.write (.var 1))) } := rfl

theorem parity_valid : LocalCompiler.Valid parity.registers parity.program parity.main := by decide

theorem parity_compiles : parity.compile =
    some (LocalCompiler.rawLink parity.registers parity.program parity.main) :=
  (Bundle.compile_some_iff _ _).mpr ⟨parity_valid, rfl⟩

/-- The same recursive declaration can be written without maintaining a `self`
number; its own name is already present when the body is lowered. -/
def recursive : Bundle := ram_program% {
  fn factorial(n) locals (answer) {
    if n {
      answer := call factorial(n - 1);
      answer := n * answer;
    } else {
      answer := 1;
    }
    return answer;
  }
  main locals (n, answer) {
    read n;
    answer := call factorial(n);
    write answer;
  }
}

theorem recursive_body : (recursive.program[0]?).map Func.body =
    some (.ite (.var 0)
      (.seq (.call [1] 0 [.bin .sub (.var 0) (.const 1)])
        (.assign 1 (.bin .mul (.var 0) (.var 1))))
      (.assign 1 (.const 1))) := rfl

end Ram.Named.Examples
