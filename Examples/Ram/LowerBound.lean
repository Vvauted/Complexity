/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Search.Function
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Tactic.Ram.Run

/-!
# Executable lower-bound search

The ordinary `lowerBound` function executes the declared binary search on an
existing array reference. Its result is the standard list insertion index,
including the length sentinel when every element is below the key. Sortedness
and the represented list occur only in erased correctness premises.

The separate time theorem bounds the actual complete invocation, including
call setup, return and halt. No proposed result or time budget is supplied to
the executable function. Memory is already represented: neither a host loader
nor its work is included in this RAM count, and no extra strict endpoint
condition is imposed on the array.
-/

namespace Ram.Examples.LowerBound

open Source Source.Array Source.Array.Search

/-- Sorted represented data and sufficient stack space make the actual call
halt. This proof uses the budget-free typed contract, not a time estimate. -/
theorem lowerBound_halts {array : ArrayRef 32} (key : Word 32)
    {heapLimit : Nat} {entry : Source.State 32}
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧
      xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (hstack : heapLimit + ABI.frameSize functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts functions.registers functions.program
      functions.functionIndex.lowerBound functions.function.lowerBound.params heapLimit
      (functions.arguments.lowerBound array key) entry := by
  obtain ⟨xs, represented, sorted⟩ := safe
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (arg := (array, key))
    (contract := function_contract (program := functions.program) (depth := 0)
      (by decide : 2 ≤ 32) sorted)
    (pre := ⟨rfl, represented⟩)) [functions.function_lookup.lowerBound]
  simpa using hstack

/-- Execute binary search and decode its returned insertion index. Runtime
inputs are the reference, key, heap boundary and preloaded state; all safety
proofs are erased and the mathematical list is not an execution argument. -/
def lowerBound (array : ArrayRef 32) (key : Word 32) (heapLimit : Nat)
    (entry : Source.State 32)
    (safe : ∃ xs, array.Rep heapLimit xs entry ∧
      xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (hstack : heapLimit + ABI.frameSize functions.registers < 2 ^ 32) : Nat :=
  (functions.apply.lowerBound array key heapLimit entry
    (lowerBound_halts key safe hstack)).toNat

/-- The actual executable value is the standard first index at least the key.
No separate reference implementation or instruction bound enters the equation. -/
theorem lowerBound_eq {heapLimit : Nat} {array : ArrayRef 32} (key : Word 32)
    {xs : List (Word 32)} {entry : Source.State 32}
    (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + ABI.frameSize functions.registers < 2 ^ 32) :
    lowerBound array key heapLimit entry ⟨xs, represented, sorted⟩ hstack =
      xs.findIdx (fun x => decide (key.toNat ≤ x.toNat)) := by
  obtain ⟨value, finish, execution, result, unchanged⟩ :=
    function_contract (program := functions.program) (depth := 0)
      (by decide : 2 ≤ 32) sorted (array, key) entry ⟨rfl, represented⟩
  subst finish
  have returned : functions.apply.lowerBound array key heapLimit entry
      (lowerBound_halts key ⟨xs, represented, sorted⟩ hstack) = value := by
    ram_run_apply (LocalCompiler.Function.applyTyped_eq_of_execution
      (kind := .word) functions.results_length.lowerBound
      (lowerBound_halts key ⟨xs, represented, sorted⟩ hstack) (execution := execution))
      [functions.function_lookup.lowerBound]
    simpa using hstack
  simpa only [lowerBound, returned] using result.eq_findIdx

/-- The same total call has a logarithmic full transition bound. Its outer
overhead is normalized from the actual generated call and return code. -/
theorem runTotal_steps_le {heapLimit : Nat} {array : ArrayRef 32} (key : Word 32)
    {xs : List (Word 32)} {entry : Source.State 32}
    (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + ABI.frameSize functions.registers < 2 ^ 32) :
    (functions.runTotal.lowerBound array key heapLimit entry
      (lowerBound_halts key ⟨xs, represented, sorted⟩ hstack)).steps ≤
      25 * Nat.clog 2 (xs.length + 1) + 69 := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract (program := functions.program) (depth := 0)
      (by decide : 2 ≤ 32) sorted (array, key) entry ⟨rfl, represented⟩
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (lowerBound_halts key ⟨xs, represented, sorted⟩ hstack) (execution := execution)
    (time := function_timeBound (program := functions.program) (depth := 0)
      (by decide : 2 ≤ 32) sorted) (pre := ⟨rfl, represented⟩))
    [functions.function_lookup.lowerBound, functions.result_eq.lowerBound]
  simpa using hstack

end Ram.Examples.LowerBound
