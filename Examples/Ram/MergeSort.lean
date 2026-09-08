/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.StateM
import Complexity.Computability.Ram.Array.MergeSort.Time
import Complexity.Computability.Ram.Array.MergeSort.FunctionTime
import Complexity.Computability.Ram.Array.Model
import Complexity.Computability.Ram.Array.Observation
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Computability.Ram.Source.Named.Basic
import Complexity.Tactic.Ram.Run

/-!
# Recursive merge sort on the actual RAM machine

The main block invokes one fixed recursive function on a preloaded source
array and an equally sized disjoint scratch allocation. It includes the
initial call and final halt, but does not include an unimplemented loader or
allocator. Both recursive calls, merging, copying and stack frame work are
counted by the compiler-backed contracts.

The `Function` namespace below exposes the source-facing two-array declaration,
its actual executable shared-state result, ordinary list/StateM specifications,
and a separate full-invocation bound. It does not wrap the older three-argument
main block above it.
-/

namespace Ram.Examples.MergeSort

open Source.Array.MergeSort

def main : Stmt := .call [3] 0 [.var 0, .var 1, .var 2]

def code : Code := LocalCompiler.rawLink 9 program main

/-- Ordinary recursive source. The mathematical canonical sort is nowhere
called by this program: only RAM calls, word operations, loads and stores occur. -/
def named : Named.Bundle := ram_program% {
  fn sort(base, scratch, length) locals
      (leftRemaining, rightRemaining, savedBase, savedScratch, savedLength, middle) {
    if 1 < length {
      savedBase := base;
      savedScratch := scratch;
      savedLength := length;
      middle := length / 2;
      rightRemaining := call sort(savedBase, savedScratch, middle);
      rightRemaining := call sort(savedBase + middle, savedScratch + middle, savedLength - middle);
      base := savedBase;
      scratch := savedBase + middle;
      length := savedScratch;
      leftRemaining := middle;
      rightRemaining := savedLength - middle;
      while leftRemaining ||| rightRemaining {
        if leftRemaining {
          if rightRemaining {
            if load[base] <= load[scratch] {
              store[length] := load[base];
              base := base + 1;
              length := length + 1;
              leftRemaining := leftRemaining - 1;
            } else {
              store[length] := load[scratch];
              scratch := scratch + 1;
              length := length + 1;
              rightRemaining := rightRemaining - 1;
            }
          } else {
            store[length] := load[base];
            base := base + 1;
            length := length + 1;
            leftRemaining := leftRemaining - 1;
          }
        } else {
          store[length] := load[scratch];
          scratch := scratch + 1;
          length := length + 1;
          rightRemaining := rightRemaining - 1;
        }
      }
      base := savedScratch;
      scratch := savedBase;
      length := savedLength;
      while length {
        store[scratch] := load[base];
        base := base + 1;
        scratch := scratch + 1;
        length := length - 1;
      }
    }
    return 0;
  }
  main locals (base, scratch, length, result) {
    result := call sort(base, scratch, length);
  }
}

theorem valid : LocalCompiler.Valid 9 program main := by
  have hcombine := Combine.wellFormed (by decide : 9 ≤ 9)
  have hcalls := Combine.callsValid program
  simpa [LocalCompiler.Valid, Compiler.Valid, program, main, function, condition,
    setup, leftArgs, rightArgs, Func.WellFormed, Stmt.WellFormed,
    Expr.Bounded, Compiler.CallsValid] using And.intro hcombine hcalls

theorem checked : LocalCompiler.compileChecked 9 program main = some code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩

set_option maxRecDepth 4096 in
theorem code_length : code.length = 321 := rfl

set_option maxRecDepth 4096 in
theorem named_compiles : named.compile = some code := by decide

/-- Source-level main contract, retaining caller locals across the initial
ordinary function call. Register 3 receives the function's zero return value. -/
theorem main_contract {heapLimit : Nat} {base scratch : Word w} {xs : List (Word w)}
    (hw : 2 ≤ w) :
    Source.RelContract 9 program heapLimit (Nat.clog 2 xs.length + 1) main
      (Pre heapLimit base scratch xs)
      (fun entry finish => Post heapLimit base scratch xs entry finish ∧
        (∀ r, r ≠ 3 → finish.regs r = entry.regs r) ∧ finish.regs 3 = 0)
      (fun _ => budget xs.length + 81) := by
  have lookup : program[0]? = some (function 0) := rfl
  apply (call_total_contract 3 hw lookup).with_timeBound
  have entered : ∀ entry, Pre heapLimit base scratch xs entry →
      (recursionSpec heapLimit 0 w).pre xs
        (entry.enter ([Expr.var 0, .var 1, .var 2].map entry.eval)) := by
    intro entry hp
    change Pre heapLimit _ _ xs _
    simpa [Source.State.enter, Source.State.eval, Expr.eval, hp.base_reg, hp.scratch_reg]
      using hp.enter_params
  have cost := Source.TimeBound.call (dsts := [3]) lookup entered
    (recursive_timeBound (control := 9) hw lookup xs)
  apply cost.mono_budget
  intro entry hp
  change 46 + 1 + budget xs.length + 33 + 1 ≤ budget xs.length + 81
  omega

/-- The preloaded main block pays for its initial call and the actual halt.
The depth premise includes that initial call, not just recursive body depth. -/
theorem block_runs {heapLimit : Nat} {base scratch : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w)
    (hpre : Pre heapLimit base scratch xs s)
    (hmatch : Source.State.Matches heapLimit 9 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 9)).toNat)
    (hcodefit : code.length < 2 ^ w)
    (hstack : Compiler.StackFits 9 (Nat.clog 2 xs.length + 1) start) :
    ∃ sourceFinal finish,
      TerminatesWithin code (budget xs.length + 82) start finish ∧
      (Post heapLimit base scratch xs s sourceFinal ∧
        (∀ r, r ≠ 3 → sourceFinal.regs r = s.regs r) ∧ sourceFinal.regs 3 = 0) ∧
      Source.State.Observes heapLimit 9 sourceFinal finish ∧
      FramePreserved 9 heapLimit start finish := by
  simpa only [Nat.add_assoc] using
    (main_contract hw).compile_block_observed checked hcodefit hpre hmatch hpc hheap hstack

/-- Every assertion observes the same halted machine, including preservation
outside both buffers and restoration of caller-visible registers. -/
structure Result (heapLimit : Nat) (base scratch : Word w) (xs : List (Word w))
    (entry finish : State w) : Prop where
  source_array : ArrayRep finish.mem base (sorted xs)
  scratch_array : ∃ workspace, workspace.length = xs.length ∧ ArrayRep finish.mem scratch workspace
  frame : ∀ address, address.toNat < heapLimit →
    (address.toNat < base.toNat ∨ base.toNat + xs.length ≤ address.toNat) →
    (address.toNat < scratch.toNat ∨ scratch.toNat + xs.length ≤ address.toNat) →
      finish.mem address = entry.mem address
  other : ∀ r, r < 9 → r ≠ 3 → finish.regs r = entry.regs r
  result : finish.regs 3 = 0
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev

theorem sort_on_machine {heapLimit : Nat} {base scratch : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w)
    (hpre : Pre heapLimit base scratch xs s)
    (hmatch : Source.State.Matches heapLimit 9 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 9)).toNat)
    (hcodefit : code.length < 2 ^ w)
    (hstack : Compiler.StackFits 9 (Nat.clog 2 xs.length + 1) start) :
    ∃ finish, TerminatesWithin code (budget xs.length + 82) start finish ∧
      Result heapLimit base scratch xs start finish := by
  obtain ⟨sourceFinal, finish, he, ⟨hp, hr, hz⟩, ho, _⟩ :=
    block_runs hw hpre hmatch hpc hheap hcodefit hstack
  refine ⟨finish, he, ho.array hp.source_array, ?_,
    ho.twoBufferFrame hmatch.observes hp.frame, ?_, ?_, ?_, ?_⟩
  · obtain ⟨workspace, hlen, ha⟩ := hp.scratch_array
    exact ⟨workspace, hlen, ho.array ha⟩
  · intro r hlocal hr3
    exact (ho.regs r hlocal).symm.trans ((hr r hr3).trans (hmatch.regs r hlocal))
  · exact (ho.regs 3 (by decide)).symm.trans hz
  · exact ho.input.symm.trans (hp.input.trans hmatch.input)
  · exact ho.output.symm.trans (hp.output.trans hmatch.output)

/-- Mathlib's `IsBigO` applies to the very budget in `sort_on_machine`, not
to the host-side canonical sort. Size counts source-array words. -/
theorem budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => ((budget n + 82 : Nat) : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) :=
  Bounds.block_budget_isBigO

namespace Function

open Source.Array Source.Array.MergeSort.Function

/-- Existing disjoint arrays of equal extent. The lists are erased witnesses
of the preloaded heap, not runtime arguments or an assumed execution. -/
def Safe (array scratch : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32) : Prop :=
  ∃ xs workspace, workspace.length = xs.length ∧
    array.Rep heapLimit xs entry ∧ scratch.Rep heapLimit workspace entry ∧
    ArraysDisjoint array.base xs.length scratch.base xs.length

variable {array scratch : ArrayRef 32} {heapLimit : Nat} {entry : Source.State 32}

/-- Budget-free recursive correctness supplies termination of the actual call.
Capacity includes the nested merge helper and the outer function frame. -/
theorem halts (safe : Safe array scratch heapLimit entry)
    (hstack : heapLimit + (Nat.clog 2 array.length.toNat + 2) *
      ABI.frameSize sortFunctions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts sortFunctions.registers sortFunctions.program
      sortFunctions.functionIndex.sort sortFunctions.function.sort.params heapLimit
      (sortFunctions.arguments.sort array scratch) entry := by
  obtain ⟨xs, workspace, length, sourceArray, scratchArray, disjoint⟩ := safe
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (arg := (array, scratch))
    (contract := function_contract (by decide : 2 ≤ 32) length disjoint)
    (pre := ⟨rfl, sourceArray, scratchArray⟩)) [sortFunctions.function_lookup.sort]
  simpa only [sourceArray.1, Nat.add_assoc] using hstack

/-- Run the recursive two-array function and return its actual shared state.
No time bound, mathematical answer, loader or host-side recursive sort is used. -/
def sort (array scratch : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32)
    (safe : Safe array scratch heapLimit entry)
    (hstack : heapLimit + (Nat.clog 2 array.length.toNat + 2) *
      ABI.frameSize sortFunctions.registers < 2 ^ 32) : Source.State 32 :=
  (sortFunctions.applyState.sort array scratch heapLimit entry (halts safe hstack)).2

variable (safe : Safe array scratch heapLimit entry)
variable (hstack : heapLimit + (Nat.clog 2 array.length.toNat + 2) *
  ABI.frameSize sortFunctions.registers < 2 ^ 32)
variable {xs workspace : List (Word 32)} (length : workspace.length = xs.length)
variable (sourceArray : array.Rep heapLimit xs entry)
variable (scratchArray : scratch.Rep heapLimit workspace entry)
variable (disjoint : ArraysDisjoint array.base xs.length scratch.base xs.length)

include length sourceArray scratchArray disjoint

/-- The mathematical sorted result, scratch extent and frame describe the
same state returned by ordinary application of the compiled function. -/
theorem sort_spec :
    let finish := sort array scratch heapLimit entry safe hstack
    array.Rep heapLimit (sorted xs) finish ∧
      (∃ now, scratch.Rep heapLimit now finish) ∧
      TwoBufferFrame array.base xs.length scratch.base xs.length entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev := by
  have post := by
    ram_run_apply (LocalCompiler.Function.applyStateTyped_spec
      (arg := (array, scratch)) sortFunctions.results_length.sort (halts safe hstack)
      (contract := function_contract (by decide : 2 ≤ 32) length disjoint)
      (pre := ⟨rfl, sourceArray, scratchArray⟩)) [sortFunctions.function_lookup.sort]
    simpa only [sourceArray.1, Nat.add_assoc] using hstack
  simpa only [sort, sortFunctions.applyState.sort,
    max_eq_right (by decide : 1 ≤ sortFunctions.registers)] using post

/-- Actual source-array contents equal the ordinary canonical list sort. -/
theorem sort_contents :
    arrayContents (sort array scratch heapLimit entry safe hstack).mem
      array.base array.length.toNat = sorted xs := by
  have represented := (sort_spec safe hstack length sourceArray scratchArray disjoint).1
  rw [represented.1]
  exact represented.2.1.contents_eq

/-- The executable result is a sorted permutation by the existing list theorem,
without reopening recursion, word bindings or the RAM calling convention. -/
theorem sort_sorted :
    SortedPerm xs (arrayContents (sort array scratch heapLimit entry safe hstack).mem
      array.base array.length.toNat) := by
  rw [sort_contents safe hstack length sourceArray scratchArray disjoint]
  exact sorted_spec xs

/-- The same observed contents implement the existing ordinary `StateM` model.
The model is a specification; it is never called by the RAM implementation. -/
theorem sort_stateM :
    arrayContents (sort array scratch heapLimit entry safe hstack).mem
      array.base array.length.toNat = ((sortState (w := 32)).run xs).2 :=
  sort_contents safe hstack length sourceArray scratchArray disjoint

/-- The same actual invocation counts recursive calls, descriptor arithmetic,
merge, copy, the outer frame and halt. Storage is already represented. -/
theorem runTotal_steps_le :
    (sortFunctions.runTotal.sort array scratch heapLimit entry
      (halts safe hstack)).steps ≤ bodyBudget xs.length + 81 := by
  obtain ⟨value, finish, execution, _⟩ := function_contract
    (by decide : 2 ≤ 32) length disjoint (array, scratch) entry
      ⟨rfl, sourceArray, scratchArray⟩
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (halts safe hstack) (execution := execution)
    (time := function_timeBound (by decide : 2 ≤ 32) length disjoint)
    (pre := ⟨rfl, sourceArray, scratchArray⟩))
    [sortFunctions.function_lookup.sort, sortFunctions.result_eq.sort]
  simpa only [sourceArray.1, Nat.add_assoc] using hstack

omit length sourceArray scratchArray disjoint in
/-- An asymptotic theorem for the natural-number reserve. Each fixed-width run
still requires its represented input and genuine code/stack capacity. -/
theorem budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => ((bodyBudget n + 81 : Nat) : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) := by
  refine (Asymptotics.IsBigO.of_norm_le (g := fun n =>
    (Recurrence.balancedBudget 85 227 n : ℝ)) ?_).trans
      (Recurrence.balancedBudget_isBigO 85 227)
  intro n
  simpa only [Real.norm_natCast] using
    (Nat.cast_le.mpr (Recurrence.balancedBudget_add_const_le 4 227 81 n) :
      ((bodyBudget n + 81 : Nat) : ℝ) ≤ (Recurrence.balancedBudget 85 227 n : ℝ))

end Function

end Ram.Examples.MergeSort
