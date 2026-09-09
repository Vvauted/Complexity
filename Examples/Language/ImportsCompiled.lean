/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Imports
import Examples.Language.FactorialCompiled
import Complexity.Computability.Ram.Compiler.Language.Linking.Tactic

/-!
# Compiling a caller of the imported recursive factorial

The existing source client makes an actual call into the imported factorial library.
Its correctness, realizability and cost proofs reuse the library contracts through the
generated embedding, without reopening the factorial induction or constructing register proofs.
The caller adds one call level and its own emitted return and function initialization.

The final theorem concerns this client's actual halted invocation in the combined program,
including its internal library call and the outer calling convention. Code and stack capacity
refer to that combined program, which also contains heap-writing traversal functions.
No claim that the whole program is heap-free or that all RAM entry memory is unchanged is used.
-/

namespace Complexity.Language.Examples.Imports

open Ram.LanguageCompiler

/-- The existing source result supplies the caller's total contract, including preservation
of every initial source heap. No proposed instruction budget is required. -/
theorem factorial_total :
    FunctionTotal Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args heap value finish => value = Nat.factorial (Env.head args) ∧ finish = heap) := by
  apply (Implementation.factorial_total_iff (fun _ _ => True)
    (fun n heap value finish => value = Nat.factorial n ∧ finish = heap)).mpr
  intro n heap _
  exact ⟨Nat.factorial n, heap, factorial_eval_heap n heap, rfl, rfl⟩

/-- The caller adds one level to the library's existing recursive call capacity.
The same factorial range premise bounds the argument and actual returned value. -/
theorem factorial_realizable {w : Nat} (n : Nat) :
    FunctionRealizable Implementation.program w (n + 1) Implementation.factorialId
      (fun args _ => Env.head args = n ∧ Nat.factorial n < 2 ^ w) := by
  ram_source_realize (input) using (Factorial.factorial_realizable n), Factorial.factorial_total
    via Implementation.imports.Factorial.Implementation.embedding
  all_goals
    have fits : Nat.factorial n < 2 ^ w := by omega
    have inputFits : n < 2 ^ w := Nat.lt_of_le_of_lt (Nat.self_le_factorial n) fits
    simp_all

/-- The actual library call uses its imported body bound and unchanged compiler-derived
overhead. The caller's scalar return and function initialization add six instructions. -/
def factorialBodyBound (n : Nat) : Nat :=
  callCost Implementation.program
    (Implementation.imports.Factorial.Implementation.map.toFun Factorial.Implementation.factorialId)
    (Factorial.factorialBodyBound n) + 6

/-- Structural cost rules account for the new caller; the library's recursive bound is
transported rather than proved by another induction or copied from a different implementation. -/
theorem factorial_costBound :
    FunctionCostBound Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args _ => factorialBodyBound (Env.head args)) := by
  ram_source_cost (input) using Factorial.factorial_costBound
    via Implementation.imports.Factorial.Implementation.embedding
  all_goals simp only [factorialBodyBound]; omega

/-- The actual compiled imported-function caller halts with factorial and a complete
instruction bound. The new caller, original recursive calls and outer invocation all count
toward stack capacity; the capacity uses the combined program's actual frame layout. -/
theorem factorial_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n : Nat)
    (fits : Nat.factorial n < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode Implementation.program Implementation.factorialId).length < 2 ^ w)
    (stackCapacity : heapLimit + (n + 2) * Ram.ABI.frameSize
      (programControl Implementation.program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.factorialId.val 1 heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n Env.empty)) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.factorialId) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords (fun _ => 0) (τ := .nat) (Nat.factorial n) ∧
      (lowerFunc Implementation.program Implementation.factorialId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n Env.empty)) entry =
        Part.some bodySteps ∧
      bodySteps ≤ factorialBodyBound n ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.factorialId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.factorialId) (factorialBodyBound n) + 1 := by
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    exact Nat.lt_of_le_of_lt (Nat.self_le_factorial n) fits
  obtain ⟨value, _, _, bodySteps, target, _, result, _, _, execution,
      values, _, time, bodyBound, invocationBound⟩ :=
    (factorial_realizable n).runUntil_le factorial_total factorial_costBound hw args ⟨#[]⟩ arguments
      ⟨rfl, fits⟩ trivial trivial entry (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have actualValue : (value : Nat) = Nat.factorial n := result.1
  exact ⟨bodySteps, target, execution, actualValue ▸ values, time, bodyBound, invocationBound⟩

end Complexity.Language.Examples.Imports
