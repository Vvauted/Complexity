/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Specification
import Complexity.Computability.Ram.Verification.StateM.Basic
import Complexity.Computability.Ram.Verification.Time.Basic
import Complexity.Tactic.Ram.Model
import Std.Tactic.Do

/-!
# A small I/O application verified by weakest-precondition rewriting

This fixed program reads one word, increments it, and writes the result. Its
functional proof uses budget-free verification conditions. A separate time
proof checks the compiler-derived instruction count without repeating the
functional postcondition. Their combination supplies the checked compiler
with a contract for a real halted execution of the same generated code.

The result is modular word addition. No natural-number no-overflow claim is
made, and any unconsumed input is retained.

The mathematical increment is also an ordinary `StateM` program verified
with Lean's native `mvcgen`. Its triple is transferred through the existing
RAM refinement and used by the final compiled execution theorem.
-/

namespace Ram.Examples.Verification

open Source

def increment : Expr := .bin .add (.var 0) (.const 1)

def main : Stmt :=
  .seq (.read 0) (.seq (.assign 1 increment) (.write (.var 1)))

/-- The machine implements the ordinary word function `fun x => x + 1`.
The untouched input tail and prior output are retained as ghost parameters,
not reconstructed by unfolding the execution in each client proof. -/
theorem main_refines (rest out : List (Word w)) :
    Refines [] 0 0 main
      (fun x s => s.input = x :: rest ∧ s.outputRev = out)
      (fun y t => t.input = rest ∧ t.outputRev = y :: out)
      (fun x : Word w => x + 1) := by
  ram_refine x s ⟨hin, hout⟩ [main, increment, hin, hout]

/-- The same mathematical increment written with ordinary Lean state effects. -/
def incrementState : StateM (Word w) PUnit := do
  let value ← get
  set (value + 1)

open Std.Do in
/-- Native verification concerns the abstract state, without machine registers
or an instruction budget. Addition keeps its modular word semantics. -/
theorem incrementState_spec (x : Word w) :
    ⦃fun state => ⌜state = x⌝⦄ incrementState
    ⦃⇓ _ state => ⌜state = x + 1⌝⦄ := by
  mvcgen [incrementState]
  simp_all

/-- The existing implementation refinement also describes the standard
returned-value/final-state pair of the stateful mathematical model. -/
theorem main_stateM_refines (rest out : List (Word w)) :
    Refines [] 0 0 main
      (fun x s => s.input = x :: rest ∧ s.outputRev = out)
      (fun result t => t.input = rest ∧ t.outputRev = result.2 :: out)
      (incrementState (w := w)).run := by
  intro x
  exact main_refines rest out x

/-- The functional result is proved before choosing any instruction budget. -/
theorem main_total_contract (x : Word w) (rest out : List (Word w)) :
    TotalContract [] 0 0 main
      (fun s => s.input = x :: rest ∧ s.outputRev = out)
      (fun t => t.input = rest ∧ t.outputRev = (x + 1) :: out) := by
  have refined := (main_stateM_refines rest out).stateM_spec_refines (incrementState_spec x)
  apply (refined x).consequence
  · intro s represented
    exact ⟨represented, rfl⟩
  · rintro target ⟨represented, property⟩
    exact ⟨represented.1, by simpa only [property] using represented.2⟩

/-- Instruction accounting can ignore the functional postcondition. The
seven steps still come from the existing measured compiler semantics. -/
theorem main_timeBound (x : Word w) (rest out : List (Word w)) :
    TimeBound 2 [] 0 0 main
      (fun s => s.input = x :: rest ∧ s.outputRev = out) (fun _ => 7) := by
  have bounded : Contract 2 [] 0 0 main
      (fun s => s.input = x :: rest ∧ s.outputRev = out) (fun _ => True)
      (fun _ => 7) := by
    ram_vc s hs [main, increment, hs.1]
  exact bounded.timeBound

/-- Independent functional and time proofs describe the same execution. -/
theorem main_contract (x : Word w) (rest out : List (Word w)) :
    Contract 2 [] 0 0 main
      (fun s => s.input = x :: rest ∧ s.outputRev = out)
      (fun t => t.input = rest ∧ t.outputRev = (x + 1) :: out)
      (fun _ => 7) :=
  (main_total_contract x rest out).with_timeBound (main_timeBound x rest out)

theorem main_valid : LocalCompiler.Valid 2 [] main := by
  simp [LocalCompiler.Valid, Compiler.Valid, main, increment, Stmt.WellFormed,
    Expr.Bounded, Compiler.CallsValid]

def code : Code := LocalCompiler.rawLink 2 [] main

theorem code_length : code.length = 9 := rfl

theorem checked : LocalCompiler.compileChecked 2 [] main = some code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨main_valid, rfl⟩

/-- The real input includes the stack-boundary header. The full nine-step
budget includes consuming that header and executing the final halt. -/
theorem terminates (x : Word w) (rest : List (Word w)) (hfit : 9 < 2 ^ w) :
    ∃ finish,
      TerminatesWithin code 9 (Ram.State.initial (0 :: x :: rest)) finish ∧
      finish.output = [x + 1] ∧ finish.input = rest := by
  have hcodefit : code.length < 2 ^ w := by rw [code_length]; exact hfit
  have hstackfit : 0 + 0 * ABI.frameSize 2 < 2 ^ w := by
    simpa only [Nat.zero_mul, Nat.zero_add] using
      Nat.lt_trans (by decide : 0 < 9) hfit
  obtain ⟨sourceFinal, targetFinal, hpost, hrun, hout, hin⟩ :=
    (main_contract x rest []).compile checked hcodefit hstackfit ⟨rfl, rfl⟩
  refine ⟨targetFinal, ?_, ?_, hin.trans hpost.1⟩
  · simpa using hrun
  · ram_model [hout, Source.State.output, hpost.2]

end Ram.Examples.Verification
