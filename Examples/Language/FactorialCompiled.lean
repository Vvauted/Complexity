/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Factorial
import Complexity.Computability.Ram.Compiler.Language.CostExecution
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
      apply FunctionRealizable.of_wp
      refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
      intro input
      refine (Env.forall_nil _).mpr ?_
      rintro heap ⟨rfl, fits⟩
      simp_all [Implementation.program, Implementation.signatures,
        Implementation.factorialBody, PrimFits, ValueFits]
      change 1 < 2 ^ w
      exact Nat.one_lt_two_pow (by omega)
  | succ n ih =>
      apply FunctionRealizable.of_wp
      refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
      intro input
      refine (Env.forall_nil _).mpr ?_
      rintro heap ⟨rfl, fits⟩
      have inputFits : n + 1 < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.self_le_factorial (n + 1)) fits
      have smallerFits : Nat.factorial n < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.factorial_le (Nat.le_succ n)) fits
      have productFits : (n + 1) * Nat.factorial n < 2 ^ w :=
        (Nat.factorial_succ n) ▸ fits
      have oneFits : 1 < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.factorial_pos n)) smallerFits
      change RealizationWP Implementation.program w (n + 1) Implementation.factorialBody
        (fun _ => False) (fun _ _ => True)
        ⟨Env.cons (τ := .nat) (n + 1) Env.empty, heap⟩
      ram_source_realize_step using ih, factorial_total
      all_goals
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
      apply FunctionCostBound.of_pointwise
      refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
      intro input
      refine (Env.forall_nil _).mpr ?_
      rintro heap rfl
      ram_source_cost_step
      all_goals norm_num [factorialBodyBound]
  | succ n ih =>
      apply FunctionCostBound.of_pointwise
      refine (Env.forall_cons (τ := .nat) (Γ := []) _).mpr ?_
      intro input
      refine (Env.forall_nil _).mpr ?_
      rintro heap rfl
      ram_source_cost_step using ih
      all_goals
        simp (config := { failIfUnchanged := false }) only [Nat.add_sub_cancel] <;>
          (try rw [callCost_eq_add]) <;>
          simp only [factorialBodyBound, Nat.mul_add, Nat.mul_one] <;> omega

/-- The independent linear body bound applies to every realized successful
invocation, uniformly in word width and permitted call nesting. -/
theorem factorial_costBound :
    FunctionCostBound Implementation.program Implementation.factorialId (fun _ _ => True)
      (fun args _ => factorialBodyBound (Env.head args)) := by
  intro args heap _
  exact factorial_costBound_at (Env.head args) args heap rfl

/-- The actual compiled invocation returns factorial and preserves the entry
state, with a linear body and complete invocation bound. The stack premise
includes the outer call in addition to the `n` recursive call levels. -/
theorem factorial_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n : Nat)
    (fits : Nat.factorial n < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode Implementation.program Implementation.factorialId).length < 2 ^ w)
    (stackCapacity : heapLimit + (n + 1) * Ram.ABI.frameSize
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
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc Implementation.program Implementation.factorialId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n Env.empty)) entry =
        Part.some bodySteps ∧
      bodySteps ≤ factorialBodyBound n ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.factorialId) bodySteps + 1 ≤
        factorialBodyBound n +
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.factorialId) 0 + 1 := by
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    exact Nat.lt_of_le_of_lt (Nat.self_le_factorial n) fits
  obtain ⟨value, _, targetFinish, bodySteps, target, _, result, invocation, _, execution,
      values, observed, time, bodyBound, invocationBound⟩ :=
    (factorial_realizable n).runUntil_le factorial_total factorial_costBound hw args ⟨#[]⟩ arguments
      ⟨rfl, fits⟩ trivial trivial entry (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have unchanged : targetFinish = entry := invocation.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites Implementation.program program_noHeapWrites)
    (lowerBody_noSharedWrites Implementation.program _ (program_noHeapWrites _))
  subst targetFinish
  have actualValue : (value : Nat) = Nat.factorial n := result.1
  refine ⟨bodySteps, target, execution, actualValue ▸ values, observed, time, bodyBound, ?_⟩
  calc
    Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
        (lowerFunc Implementation.program Implementation.factorialId) bodySteps + 1 ≤
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
        (lowerFunc Implementation.program Implementation.factorialId) (factorialBodyBound n) + 1 :=
      invocationBound
    _ = factorialBodyBound n +
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.factorialId) 0 + 1 := by
      simp only [Ram.LocalCompiler.Function.callSteps_eq]
      omega

end Complexity.Language.Examples.Factorial
