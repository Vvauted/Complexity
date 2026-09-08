/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Time
import Complexity.Computability.Ram.Array.Model
import Complexity.Computability.Ram.Array.Observation
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Tactic.Ram.Run

/-!
# A complete linear merge on the actual RAM machine

The shared declaration in `Array.Merge.Function` uses the same fixed merge loop
as the reusable contract. Its input consists of two preloaded source arrays and a disjoint,
already allocated destination. The sources may overlap each other. The block
theorem explicitly starts at PC 1 and includes halt, not an implicit loader
or allocator. The bitwise-OR guard does not add the two counts in a word.

The result theorem observes standard `List.merge` in the halted target heap,
with both sources, destination-external heap words, I/O, and higher user
registers preserved by that same run. Sortedness is needed only by the final
sorted-merge theorem, not by the general machine execution theorem.

`Function.merge` executes the typed three-array function and returns its actual
shared state. Its mathematical contents theorem uses ordinary `List.merge`;
the separate count includes both the inner core call and the outer typed call.
-/

namespace Ram.Examples.Merge

open Source.Array

def code (control : Nat) : Code := LocalCompiler.rawLink control [] Source.Array.Merge.program

/-- Observe the shared source loop as a standalone block. The callable
interface below uses the same declaration, not another copy of its source. -/
def named : Named.Bundle where
  registers := 5
  declarations := []
  main := Source.Array.Merge.mergeFunctions.function.mergeCore.body

theorem named_body : named.main = Source.Array.Merge.program := rfl

theorem valid {control : Nat} (hcontrol : 5 ≤ control) :
    LocalCompiler.Valid control [] Source.Array.Merge.program := by
  refine ⟨Source.Array.Merge.wellFormed hcontrol, Source.Array.Merge.callsValid [], ?_⟩
  simp

theorem checked {control : Nat} (hcontrol : 5 ≤ control) :
    LocalCompiler.compileChecked control [] Source.Array.Merge.program = some (code control) :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid hcontrol, rfl⟩

theorem named_code : LocalCompiler.rawLink 5 [] named.main = code 5 := rfl

theorem named_compiles : named.compile = some (code 5) :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid (by decide), rfl⟩

theorem code_length (control : Nat) : (code control).length = 84 := rfl

/-- All output observations are attached to one completed target execution.
Heap preservation is stated inside the source-visible heap; compiler-private
stack/control storage is not misidentified as user array storage. -/
structure Result (control heapLimit : Nat) (left right destination : Word w)
    (xs ys : List (Word w)) (entry finish : State w) : Prop where
  destination_array : ArrayRep finish.mem destination (unsignedMerge xs ys)
  left_array : ArrayRep finish.mem left xs
  right_array : ArrayRep finish.mem right ys
  frame : ∀ address, address.toNat < heapLimit →
    address.toNat < destination.toNat ∨ destination.toNat + xs.length + ys.length ≤ address.toNat →
      finish.mem address = entry.mem address
  left_pointer : finish.regs 0 = arrayAddr left xs.length
  right_pointer : finish.regs 1 = arrayAddr right ys.length
  destination_pointer : finish.regs 2 = arrayAddr destination (xs.length + ys.length)
  left_count : finish.regs 3 = 0
  right_count : finish.regs 4 = 0
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → r < control → finish.regs r = entry.regs r

/-- The source contract and existing checked compiler supply the complete
target execution. The extra one is the actual halt; PC 1 excludes the unused
input-header prologue from both the execution and its claimed budget. -/
theorem block_runs {control heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {s : Source.State w} {start : State w}
    (hw : 0 < w) (hcontrol : 5 ≤ control)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (hpre : Source.Array.Merge.Pre heapLimit left right destination xs ys scratch s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ sourceFinal finish,
      TerminatesWithin (code control) (34 * (xs.length + ys.length) + 5) start finish ∧
      Source.Array.Merge.Post heapLimit left right destination xs ys s sourceFinal ∧
      Source.State.Observes heapLimit control sourceFinal finish ∧
      FramePreserved control heapLimit start finish := by
  have hstack : Compiler.StackFits control 0 start := by
    simpa only [Compiler.StackFits, Nat.zero_mul, Nat.add_zero] using
      Word.toNat_lt (start.regs (ABI.sp control))
  simpa only [Nat.add_assoc] using
    (Source.Array.Merge.contract (control := control) (functions := []) (depth := 0)
      hw hlen hdl hdr).compile_block_observed
      (checked hcontrol) hcodefit hpre hmatch hpc hheap hstack

/-- General merge works even for unsorted source arrays and permits overlap
between them. Its actual result is standard `List.merge`, with unchanged
sources, a destination frame, final pointers/counts, and retained caller I/O. -/
theorem merge_on_machine {control heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {s : Source.State w} {start : State w}
    (hw : 0 < w) (hcontrol : 5 ≤ control)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (hpre : Source.Array.Merge.Pre heapLimit left right destination xs ys scratch s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ finish,
      TerminatesWithin (code control) (34 * (xs.length + ys.length) + 5) start finish ∧
      Result control heapLimit left right destination xs ys start finish := by
  obtain ⟨sourceFinal, finish, he, hp, ho, _⟩ :=
    block_runs hw hcontrol hlen hdl hdr hpre hmatch hpc hheap hcodefit
  refine ⟨finish, he, ho.array hp.destination_array,
    ho.array hp.left_array, ho.array hp.right_array,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using ho.arrayFrame hmatch.observes hp.frame
  · exact (ho.regs 0 (by omega)).symm.trans hp.left_pointer
  · exact (ho.regs 1 (by omega)).symm.trans hp.right_pointer
  · exact (ho.regs 2 (by omega)).symm.trans hp.destination_pointer
  · exact (ho.regs 3 (by omega)).symm.trans hp.left_count
  · exact (ho.regs 4 (by omega)).symm.trans hp.right_count
  · exact ho.input.symm.trans (hp.input.trans hmatch.input)
  · exact ho.output.symm.trans (hp.output.trans hmatch.output)
  · intro r hr hrc
    exact (ho.regs r hrc).symm.trans ((hp.other r hr).trans (hmatch.regs r hrc))

/-- When both source lists are sorted, the very same halted heap contains a
sorted permutation of their concatenation. The mathematical bridge is the
existing standard merge theorem, not an added sortedness assumption on the
general machine execution rule. -/
theorem merge_sorted_on_machine {control heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {s : Source.State w} {start : State w}
    (hw : 0 < w) (hcontrol : 5 ≤ control)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (hxs : xs.Pairwise unsignedLE) (hys : ys.Pairwise unsignedLE)
    (hpre : Source.Array.Merge.Pre heapLimit left right destination xs ys scratch s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ finish output,
      TerminatesWithin (code control) (34 * (xs.length + ys.length) + 5) start finish ∧
      Result control heapLimit left right destination xs ys start finish ∧
      ArrayRep finish.mem destination output ∧ SortedPerm (xs ++ ys) output := by
  obtain ⟨finish, he, hr⟩ := merge_on_machine hw hcontrol hlen hdl hdr hpre hmatch hpc hheap hcodefit
  exact ⟨finish, unsignedMerge xs ys, he, hr, hr.destination_array,
    (SortedPerm.refl hxs).merge (SortedPerm.refl hys)⟩

namespace Function

open Source.Array.Merge

/-- Three existing represented arrays admit a merge into the independent
destination. The two sources need not be disjoint from each other. -/
def Safe (left right destination : ArrayRef 32) (heapLimit : Nat)
    (entry : Source.State 32) : Prop :=
  ∃ xs ys scratch, scratch.length = xs.length + ys.length ∧
    left.Rep heapLimit xs entry ∧ right.Rep heapLimit ys entry ∧
    destination.Rep heapLimit scratch entry ∧
    ArraysDisjoint destination.base (xs.length + ys.length) left.base xs.length ∧
    ArraysDisjoint destination.base (xs.length + ys.length) right.base ys.length

variable {left right destination : ArrayRef 32} {heapLimit : Nat} {entry : Source.State 32}

/-- Termination of the typed wrapper and its core follows from budget-free
correctness. Stack capacity pays for both live function frames. -/
theorem halts (safe : Safe left right destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize mergeFunctions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts mergeFunctions.registers mergeFunctions.program
      mergeFunctions.functionIndex.merge mergeFunctions.function.merge.params heapLimit
      (mergeFunctions.arguments.merge left right destination) entry := by
  obtain ⟨xs, ys, scratch, length, leftArray, rightArray, destinationArray, hdl, hdr⟩ := safe
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (arg := (left, right, destination))
    (contract := function_contract (by decide : 0 < 32) length hdl hdr)
    (pre := ⟨rfl, leftArray, rightArray, destinationArray⟩))
    [mergeFunctions.function_lookup.merge]
  exact hstack

/-- Execute the three-array function and return its actual shared state.
The lists and safety proofs are erased; no result or time budget is an input. -/
def merge (left right destination : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32)
    (safe : Safe left right destination heapLimit entry)
    (hstack : heapLimit + 2 * ABI.frameSize mergeFunctions.registers < 2 ^ 32) :
    Source.State 32 :=
  (mergeFunctions.applyState.merge left right destination heapLimit entry (halts safe hstack)).2

variable (safe : Safe left right destination heapLimit entry)
variable (hstack : heapLimit + 2 * ABI.frameSize mergeFunctions.registers < 2 ^ 32)
variable {xs ys scratch : List (Word 32)} (length : scratch.length = xs.length + ys.length)
variable (leftArray : left.Rep heapLimit xs entry) (rightArray : right.Rep heapLimit ys entry)
variable (destinationArray : destination.Rep heapLimit scratch entry)
variable (hdl : ArraysDisjoint destination.base (xs.length + ys.length) left.base xs.length)
variable (hdr : ArraysDisjoint destination.base (xs.length + ys.length) right.base ys.length)

include length leftArray rightArray destinationArray hdl hdr

/-- Ordinary array representations specify the state produced by the actual
typed application. Only the destination may change; both sources and I/O survive. -/
theorem merge_spec :
    let finish := merge left right destination heapLimit entry safe hstack
    left.Rep heapLimit xs finish ∧ right.Rep heapLimit ys finish ∧
      destination.Rep heapLimit (unsignedMerge xs ys) finish ∧
      ArrayFrame destination.base (xs.length + ys.length) entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev := by
  have post := by
    ram_run_apply (LocalCompiler.Function.applyStateTyped_spec
      (arg := (left, right, destination))
      mergeFunctions.results_length.merge (halts safe hstack)
      (contract := function_contract (by decide : 0 < 32) length hdl hdr)
      (pre := ⟨rfl, leftArray, rightArray, destinationArray⟩))
      [mergeFunctions.function_lookup.merge]
    exact hstack
  simpa only [merge, mergeFunctions.applyState.merge,
    max_eq_right (by decide : 1 ≤ mergeFunctions.registers)] using post

/-- The actual destination contents equal standard list merge. Sortedness is
not required for this equation about the implementation. -/
theorem merge_contents :
    arrayContents (merge left right destination heapLimit entry safe hstack).mem
      destination.base destination.length.toNat = unsignedMerge xs ys := by
  have represented :=
    (merge_spec safe hstack length leftArray rightArray destinationArray hdl hdr).2.2.1
  rw [represented.1]
  exact represented.2.1.contents_eq

/-- Upstream merge properties give a sorted permutation of both inputs,
without reopening the implementation's loop, bindings or calling convention. -/
theorem merge_sorted (hxs : xs.Pairwise unsignedLE) (hys : ys.Pairwise unsignedLE) :
    SortedPerm (xs ++ ys)
      (arrayContents (merge left right destination heapLimit entry safe hstack).mem
        destination.base destination.length.toNat) := by
  rw [merge_contents safe hstack length leftArray rightArray destinationArray hdl hdr]
  exact (SortedPerm.refl hxs).merge (SortedPerm.refl hys)

/-- The complete typed invocation includes both core and wrapper calls,
their returns, and the final halt. Preloading remains outside this count. -/
theorem runTotal_steps_le :
    (mergeFunctions.runTotal.merge left right destination heapLimit entry
      (halts safe hstack)).steps ≤ 34 * (xs.length + ys.length) + 122 := by
  obtain ⟨value, finish, execution, _⟩ := function_contract
    (by decide : 0 < 32) length hdl hdr (left, right, destination) entry
      ⟨rfl, leftArray, rightArray, destinationArray⟩
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (halts safe hstack) (execution := execution)
    (time := function_timeBound (by decide : 0 < 32) length hdl hdr)
    (pre := ⟨rfl, leftArray, rightArray, destinationArray⟩))
    [mergeFunctions.function_lookup.merge, mergeFunctions.result_eq.merge]
  exact hstack

end Function

end Ram.Examples.Merge
