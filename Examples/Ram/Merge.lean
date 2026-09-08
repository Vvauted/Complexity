/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Basic
import Complexity.Computability.Ram.Array.Observation
import Complexity.Computability.Ram.Source.Named.Basic

/-!
# A complete linear merge on the actual RAM machine

The named source below is the same fixed merge program as the reusable array
contract. Its input consists of two preloaded source arrays and a disjoint,
already allocated destination. The sources may overlap each other. The block
theorem explicitly starts at PC 1 and includes halt, not an implicit loader
or allocator. The bitwise-OR guard does not add the two counts in a word.

The result theorem observes standard `List.merge` in the halted target heap,
with both sources, destination-external heap words, I/O, and higher user
registers preserved by that same run. Sortedness is needed only by the final
sorted-merge theorem, not by the general machine execution theorem.
-/

namespace Ram.Examples.Merge

open Source.Array

def code (control : Nat) : Code := LocalCompiler.rawLink control [] Source.Array.Merge.program

/-- Ordinary source syntax: loads and stores, not a host-side merge primitive.
On equal heads the left source is chosen, just as by standard `List.merge`. -/
def named : Named.Bundle := ram_program% {
  main locals (left, right, destination, leftRemaining, rightRemaining) {
    while leftRemaining ||| rightRemaining {
      if leftRemaining {
        if rightRemaining {
          if load[left] <= load[right] {
            store[destination] := load[left];
            left := left + 1;
            destination := destination + 1;
            leftRemaining := leftRemaining - 1;
          } else {
            store[destination] := load[right];
            right := right + 1;
            destination := destination + 1;
            rightRemaining := rightRemaining - 1;
          }
        } else {
          store[destination] := load[left];
          left := left + 1;
          destination := destination + 1;
          leftRemaining := leftRemaining - 1;
        }
      } else {
        store[destination] := load[right];
        right := right + 1;
        destination := destination + 1;
        rightRemaining := rightRemaining - 1;
      }
    }
  }
}

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

end Ram.Examples.Merge
