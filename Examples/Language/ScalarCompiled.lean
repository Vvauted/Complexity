/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Scalar
import Complexity.Computability.Ram.Compiler.Language.Execution
import Complexity.Computability.Ram.Compiler.Language.CostExecution

/-!
# Transferring the scalar source proof through generic lowering

The independent source program and its mathematical proofs are imported
unchanged. The additional proofs here concern the actual intermediate natural
values and sufficient call nesting. The helper's existing source contract
identifies its actual returned value; its mathematical behavior is not reproved.

The shared lowering theorems produce both callable IR execution and a halted RAM
runner with the same mathematical minimum. No register layout, receiver update
or algorithm-specific source-to-IR adapter appears in this proof. Separate
source-execution cost bounds apply to that same invocation, including its
internal helper call, outer calling convention and final halt.
-/

namespace Complexity.Language.Examples.Scalar

open Ram.LanguageCompiler

/-- The helper needs no nested call and its actual sum must fit the word width. -/
theorem increment_realizable {w : Nat} :
    FunctionRealizable program w 0 (0 : Fin 2)
      (fun args => Env.head args + 1 < 2 ^ w) := by
  apply FunctionRealizable.of_wp
  intro args fits
  change (Env.head args : Nat) + 1 < 2 ^ w at fits
  change RealizationWP program w 0 increment (fun _ => False) (fun _ _ => True) args
  simp only [increment, RealizationWP.letPrim_iff, RealizationWP.ret_iff,
    PrimFits, Prim.eval, Atom.eval, Env.cons_here, valueToNat, and_true]
  change (Env.head args < 2 ^ w ∧ 1 < 2 ^ w ∧ Env.head args + 1 < 2 ^ w) ∧
    Env.head args + 1 < 2 ^ w
  exact ⟨⟨Nat.lt_trans (Nat.lt_succ_self _) fits,
    Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le _)) fits, fits⟩, fits⟩

/-- One call level suffices. The intermediate increment, not merely the final
minimum, and the compared limit must both be representable. -/
theorem boundedIncrement_realizable {w : Nat} :
    FunctionRealizable program w 1 (1 : Fin 2)
      (fun args => Env.head args + 1 < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  apply FunctionRealizable.of_wp
  intro args range
  change (Env.head args : Nat) + 1 < 2 ^ w ∧
    (Env.head (Env.tail args) : Nat) < 2 ^ w at range
  change RealizationWP program w 1 boundedIncrement (fun _ => False) (fun _ _ => True) args
  unfold boundedIncrement
  refine RealizationWP.call increment_realizable increment_total ?_ (by decide) ?_ trivial ?_
  · change EnvFits w (Env.cons (τ := .nat) (Env.head args) Env.empty)
    intro τ scalar v
    cases v with
    | here => exact Nat.lt_trans (Nat.lt_succ_self _) range.1
    | there v => cases v
  · exact range.1
  · intro value returned valueFits
    have actualValue : (value : Nat) = Env.head args + 1 := returned
    subst value
    rw [RealizationWP.letPrim_iff]
    refine ⟨⟨valueFits, range.2⟩, ?_⟩
    simp only [RealizationWP.ite_iff, RealizationWP.ret_iff,
      Prim.eval, Atom.eval, Env.cons_here, Env.cons_there, valueToNat, and_true]
    split
    · exact range.1
    · exact range.2

/-- The automatically lowered helper returns the same mathematical increment.
The entry state and heap boundary are arbitrary; no manual register proof is needed. -/
theorem increment_functionExec {w heapLimit : Nat} (hw : 0 < w) (n : Nat)
    (fits : n + 1 < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 0
      (lowerFunc program (0 : Fin 2))
      (envWords w (Env.cons (τ := .nat) n Env.empty)) entry
      (valueWords w (τ := .nat) (n + 1)) finish := by
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have emptyFits : EnvFits w Env.empty := by intro τ scalar v; cases v
  have arguments : EnvFits w args := emptyFits.cons (τ := .nat) n (fun _ => by
    change n < 2 ^ w
    omega)
  obtain ⟨value, finish, execution, result⟩ :=
    increment_realizable.functionExec (heapLimit := heapLimit)
      increment_total hw args arguments fits trivial entry
  have actualValue : (value : Nat) = n + 1 := result
  exact ⟨finish, actualValue ▸ execution⟩

/-- The same source helper-call and branch program has an actual generated
function execution returning the mathematical minimum. This uses the shared
compiler theorem and the unchanged source correctness proof. -/
theorem boundedIncrement_functionExec {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 1
      (lowerFunc program (1 : Fin 2))
      (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry
      (valueWords w (τ := .nat) (min (n + 1) limit)) finish := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have emptyFits : EnvFits w Env.empty := by intro τ scalar v; cases v
  have limitEnv : EnvFits w (Env.cons (τ := .nat) limit Env.empty) :=
    emptyFits.cons (τ := .nat) limit (fun _ => limitFits)
  have arguments : EnvFits w args :=
    limitEnv.cons (τ := .nat) n (fun _ => by change n < 2 ^ w; omega)
  obtain ⟨value, finish, execution, result⟩ :=
    boundedIncrement_realizable.functionExec (heapLimit := heapLimit)
      boundedIncrement_total hw args arguments ⟨sumFits, limitFits⟩ trivial entry
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨finish, actualValue ▸ execution⟩

/-- The actual compiled machine returns the source-level minimum and preserves
the shared entry state. Its measured instruction count refers to this same
execution, without assuming or claiming an instruction upper bound. -/
theorem boundedIncrement_runUntil {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords w (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have emptyFits : EnvFits w Env.empty := by intro τ scalar v; cases v
  have limitEnv : EnvFits w (Env.cons (τ := .nat) limit Env.empty) :=
    emptyFits.cons (τ := .nat) limit (fun _ => limitFits)
  have arguments : EnvFits w args :=
    limitEnv.cons (τ := .nat) n (fun _ => by change n < 2 ^ w; omega)
  obtain ⟨value, bodySteps, target, result, execution, values, observed, time⟩ :=
    boundedIncrement_realizable.runUntil boundedIncrement_total hw args arguments
      ⟨sumFits, limitFits⟩ trivial entry codeCapacity stackCapacity
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time⟩

/-- The helper body spends four transitions on addition, four on returning its
value and setting the flag, and five on the function-body wrapper. -/
theorem increment_costBound :
    FunctionCostBound program (0 : Fin 2) (fun _ => True) (fun _ => 13) := by
  intro args _ w depth finish value execution steps cost
  cases cost with
  | letPrim tail =>
      cases tail
      change 4 + (2 * 1 + 2) + 5 ≤ 13
      decide

/-- The caller reuses the helper's complete call bound. Its comparison, selected
return branch and wrapper add at most sixteen transitions. -/
theorem boundedIncrement_costBound :
    FunctionCostBound program (1 : Fin 2) (fun _ => True)
      (fun _ => callCost program (0 : Fin 2) 13 + 16) := by
  intro args _ w depth finish value execution steps cost
  cases cost with
  | callReturn calleeCost bodyCost =>
      have helperBound := increment_costBound _ trivial _ calleeCost
      change _ + 5 ≤ 13 at helperBound
      have callBound := callCost_mono program (0 : Fin 2) helperBound
      cases bodyCost with
      | letPrim branch =>
          cases branch with
          | iteTrue returned =>
              cases returned
              exact Nat.add_le_add_right callBound 16
          | iteFalse returned =>
              cases returned
              exact Nat.le_trans (Nat.add_le_add_right callBound 15)
                (Nat.add_le_add_left (by decide : 15 ≤ 16) _)

/-- The same halted machine invocation returns the mathematical minimum and
satisfies the independent source cost bound, including the outer call and halt. -/
theorem boundedIncrement_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords w (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps ∧
      bodySteps ≤ callCost program (0 : Fin 2) 13 + 16 ∧
      Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) (callCost program (0 : Fin 2) 13 + 16) + 1 := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have emptyFits : EnvFits w Env.empty := by intro τ scalar v; cases v
  have limitEnv : EnvFits w (Env.cons (τ := .nat) limit Env.empty) :=
    emptyFits.cons (τ := .nat) limit (fun _ => limitFits)
  have arguments : EnvFits w args :=
    limitEnv.cons (τ := .nat) n (fun _ => by change n < 2 ^ w; omega)
  obtain ⟨value, bodySteps, target, result, execution, values, observed, time,
      bodyBound, invocationBound⟩ :=
    boundedIncrement_realizable.runUntil_le boundedIncrement_total boundedIncrement_costBound
      hw args arguments ⟨sumFits, limitFits⟩ trivial trivial entry codeCapacity stackCapacity
  have actualValue : (value : Nat) = min (n + 1) limit := result
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time,
    bodyBound, invocationBound⟩

end Complexity.Language.Examples.Scalar
