/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Factorial
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiling the independently verified recursive factorial

The imported source function and factorial theorem are unchanged. Mathematical
induction establishes the extra value ranges and call nesting required by the
word backend. The recursive call's actual returned value comes from the existing
source contract, not a second proof of factorial correctness.

A separate induction composes the compiler-derived primitive and call charges
into a linear instruction bound. Its fixed coefficient retains the actual
generated function's call overhead, without copying constants from another
factorial implementation. The final theorem concerns the real halted runner,
subject to the generated code and stack fitting the chosen word width.
Linearity is in the numeric argument `n` and counts word-RAM instructions;
it is not linearity in the input's binary bit length or a claim about the
bit-operation cost of arbitrary-precision multiplication.

This pure implementation accesses no heap objects. The runner bridge therefore
uses an empty source-object representation and admits arbitrary RAM entry memory;
the actual invocation preserves its shared entry state. The source theorem itself
continues to hold for every initial source heap. No claim is made that arbitrary
natural factorials fit a fixed word width.
-/

namespace Complexity.Language.Examples.Factorial

open Ram.LanguageCompiler

private theorem program_noHeapWrites :
    ∀ fn, NoHeapWrites (Implementation.program.body fn) := by
  intro fn
  refine Fin.cases ?_ (fun i => Fin.elim0 i) fn
  change NoHeapWrites Implementation.factorialBody
  simp [Implementation.factorialBody, NoHeapWrites]

/-- Input `n` needs at most `n` nested source calls. Fitting `n!` also bounds
all smaller inputs, recursive results, multiplication results and constants. -/
theorem factorial_realizable {w : Nat} (n : Nat) :
    FunctionRealizable Implementation.program w n Implementation.factorialId
      (fun args _ => Env.head args = n ∧ Nat.factorial n < 2 ^ w) := by
  induction n with
  | zero =>
      ram_source_realize (input)
      all_goals simp_all [Nat.factorial_zero]
  | succ n ih =>
      ram_source_realize (input) using ih, factorial_total
      all_goals
        have fits : Nat.factorial (n + 1) < 2 ^ w := by omega
        have inputFits : n + 1 < 2 ^ w :=
          Nat.lt_of_le_of_lt (Nat.self_le_factorial (n + 1)) fits
        have smallerFits : Nat.factorial n < 2 ^ w :=
          Nat.lt_of_le_of_lt (Nat.factorial_le (Nat.le_succ n)) fits
        have productFits : (n + 1) * Nat.factorial n < 2 ^ w :=
          (Nat.factorial_succ n) ▸ fits
        have oneFits : 1 < 2 ^ w :=
          Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.factorial_pos n)) smallerFits
        simp_all only [Nat.add_sub_cancel, Nat.factorial_succ, true_and, and_true] <;> omega

/-- A proposed linear bound whose fixed call overhead is derived from the
actual lowered function. The base case costs thirteen instructions; each
successor adds twenty-four non-call instructions and its actual recursive call. -/
def factorialBodyBound (n : Nat) : Nat :=
  (callCost Implementation.program Implementation.factorialId 0 + 24) * n + 13

/-- A recursive cost hypothesis only concerns the actual smaller argument.
No factorial-value, range, termination or machine-state proof is repeated. -/
theorem factorial_costBound_at (n : Nat) :
    FunctionCostBound Implementation.program Implementation.factorialId
      (fun args _ => Env.head args = n) (fun _ _ => factorialBodyBound n) := by
  induction n with
  | zero =>
      ram_source_cost (input)
      all_goals norm_num [factorialBodyBound]
  | succ n ih =>
      ram_source_cost (input) using ih
      all_goals
        first
        | omega
        | rw [callCost_eq_add]
          simp only [factorialBodyBound, Nat.mul_add, Nat.mul_one]
          omega

/-- The independent linear body bound applies to every realized successful
invocation, uniformly in word width and permitted call nesting. -/
theorem factorial_costBound :
    FunctionCostBound Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args _ => factorialBodyBound (Env.head args)) := by
  intro args heap _
  exact factorial_costBound_at (Env.head args) args heap rfl

/-- The complete invocation bound includes the actual outer call and final halt. -/
def factorialInvocationBound (n : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.factorialId) (factorialBodyBound n) + 1

/-- The actual compiled result is the ordinary mathematical factorial.
Shared publication retains the runner, body-time equation and returned words;
the independent frame and cost theorems concern that same result. Capacity
includes the outer call and the `n` recursive call levels. -/
theorem factorial_execute {w heapLimit : Nat} (n : Nat)
    (fits : Nat.factorial n < 2 ^ w) (entry : Ram.Source.State w)
    (capacity : FunctionCapacity Implementation.program Implementation.factorialId w n heapLimit) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.factorialId heapLimit
        (fun _ => 0) (Implementation.factorial_args n) ⟨#[]⟩ entry,
      outcome.value = Nat.factorial n ∧
      Ram.Source.State.Observes heapLimit 0 entry outcome.result.state ∧
      outcome.bodySteps ≤ factorialBodyBound n ∧
      outcome.result.steps ≤ factorialInvocationBound n := by
  have arguments : EnvFits w (Implementation.factorial_args n) := by
    simp only [Implementation.factorial_args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    exact Nat.lt_of_le_of_lt (Nat.self_le_factorial n) fits
  obtain ⟨outcome, result, bounded⟩ :=
    (factorial_realizable n).execute_le factorial_total factorial_costBound
      { toFunctionCapacity := capacity, arguments := arguments,
        memory := HeapRep.empty (fun _ => 0) heapLimit entry }
      ⟨rfl, fits⟩ trivial trivial
  exact ⟨outcome, result.1, outcome.observes_of_noHeapWrites program_noHeapWrites,
    outcome.bodySteps_le bounded, bounded⟩

end Complexity.Language.Examples.Factorial
