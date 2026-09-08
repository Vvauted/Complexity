/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Observation
import Complexity.Computability.Ram.Array.Sort.Complexity
import Complexity.Computability.Ram.Source.Named.Basic

/-!
# The complete binary insertion sort on the actual machine

The input array is preloaded and the base and length are in registers 0 and
5. These theorems explicitly start at PC 1, count all instructions of the
sorting program and its halt, and make no claim to include a skipped loader.

One fixed program handles arbitrary representable arrays, including empty
arrays and duplicates. Its observed heap is mathlib's insertion sort of the
original words; the standard sortedness/permutation specification follows.
Only the array interval and working registers 1–4 and 6 may change. A caller
can choose any local-register bound at least seven and retain its higher
source-visible registers. Compiler control and scratch registers are not
mistakenly included in that preservation assertion.
-/

namespace Ram.Examples.InsertionSort

open Source.Array

def code (control : Nat) : Code := LocalCompiler.rawLink control [] Sort.program

/-- Ordinary named source for the same compiled program. The inner search
finds a lower bound; the backward loop then moves real heap words. -/
def named : Named.Bundle := ram_program% {
  main locals (base, key, lo, hi, cursor, length, index) {
    index := 0;
    while index < length {
      key := load[base + index];
      hi := index;
      lo := 0;
      while lo < hi {
        cursor := lo + (hi - lo) / 2;
        if load[base + cursor] < key {
          lo := cursor + 1;
        } else {
          hi := cursor;
        }
      }
      hi := index;
      cursor := hi;
      while lo < cursor {
        store[base + cursor] := load[base + (cursor - 1)];
        cursor := cursor - 1;
      }
      store[base + lo] := key;
      index := index + 1;
    }
  }
}

theorem named_valid : LocalCompiler.Valid 7 [] named.main := by
  simp [named, LocalCompiler.Valid, Compiler.Valid, Stmt.WellFormed,
    Expr.Bounded, Compiler.CallsValid]

/-- The surface block associates sequential statements differently from the
modular proof, but both produce literally the same machine instructions. -/
theorem named_code : LocalCompiler.rawLink 7 [] named.main = code 7 := rfl

theorem named_compiles : named.compile = some (code 7) :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨named_valid, named_code.symm⟩

theorem valid {control : Nat} (hcontrol : 7 ≤ control) :
    LocalCompiler.Valid control [] Sort.program := by
  refine ⟨Sort.wellFormed hcontrol, Sort.callsValid [], ?_⟩
  simp

theorem checked {control : Nat} (hcontrol : 7 ≤ control) :
    LocalCompiler.compileChecked control [] Sort.program = some (code control) :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid hcontrol, rfl⟩

theorem code_length (control : Nat) : (code control).length = 77 := rfl

/-- Sorting plus halt from a preloaded matching machine state. The private
stack-pointer/older-stack frame and all source-visible observations refer to
the same terminating target run. -/
theorem block_runs {control heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w) (hcontrol : 7 ≤ control)
    (hpre : Sort.Pre heapLimit base xs s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ sourceFinal finish,
      TerminatesWithin (code control) (Sort.budget xs.length + 1) start finish ∧
      Sort.Post heapLimit base xs s sourceFinal ∧
      Source.State.Observes heapLimit control sourceFinal finish ∧
      FramePreserved control heapLimit start finish := by
  have hstack : Compiler.StackFits control 0 start := by
    simpa only [Compiler.StackFits, Nat.zero_mul, Nat.add_zero] using
      Word.toNat_lt (start.regs (ABI.sp control))
  exact (Sort.contract (control := control) (functions := []) (depth := 0) hw).compile_block_observed
    (checked hcontrol) hcodefit hpre hmatch hpc hheap hstack

/-- The same actual halted run, now with the quadratic complexity bound. -/
theorem block_runs_quadratic {control heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w) (hcontrol : 7 ≤ control)
    (hpre : Sort.Pre heapLimit base xs s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ sourceFinal finish,
      TerminatesWithin (code control) (44 * xs.length ^ 2 + 35 * xs.length + 7)
        start finish ∧
      Sort.Post heapLimit base xs s sourceFinal ∧
      Source.State.Observes heapLimit control sourceFinal finish ∧
      FramePreserved control heapLimit start finish := by
  obtain ⟨sourceFinal, finish, he, hp, ho, hf⟩ :=
    block_runs hw hcontrol hpre hmatch hpc hheap hcodefit
  exact ⟨sourceFinal, finish, he.mono (Sort.budget_add_halt_le_quadratic xs.length), hp, ho, hf⟩

/-- Direct heap/result observations: standard insertion sort, unchanged
array-external heap and I/O, and preserved caller registers above the seven
algorithm registers. The displayed budget includes the actual halt. -/
theorem sort_on_machine {control heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w) (hcontrol : 7 ≤ control)
    (hpre : Sort.Pre heapLimit base xs s)
    (hmatch : Source.State.Matches heapLimit control s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
    (hcodefit : (code control).length < 2 ^ w) :
    ∃ finish,
      TerminatesWithin (code control)
        (xs.length * (25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 35) + 7)
        start finish ∧
      ArrayRep finish.mem base (xs.insertionSort unsignedLE) ∧
      (∀ address, address.toNat < heapLimit →
        address.toNat < base.toNat ∨ base.toNat + xs.length ≤ address.toNat →
          finish.mem address = start.mem address) ∧
      finish.regs 0 = base ∧ finish.regs 5 = start.regs 5 ∧
      (finish.regs 6).toNat = xs.length ∧
      (∀ r, 7 ≤ r → r < control → finish.regs r = start.regs r) ∧
      finish.input = start.input ∧ finish.outputRev = start.outputRev := by
  obtain ⟨sourceFinal, finish, he, hp, ho, _⟩ :=
    block_runs hw hcontrol hpre hmatch hpc hheap hcodefit
  refine ⟨finish, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Sort.budget, Nat.add_assoc] using he
  · exact ho.array hp.array
  · exact ho.arrayFrame hmatch.observes hp.frame
  · exact (ho.regs 0 (by omega)).symm.trans hp.base_reg
  · exact (ho.regs 5 (by omega)).symm.trans (hp.length_reg.trans (hmatch.regs 5 (by omega)))
  · rw [← ho.regs 6 (by omega)]
    exact hp.processed_reg
  · intro r hr hrc
    exact (ho.regs r hrc).symm.trans ((hp.other r hr).trans (hmatch.regs r hrc))
  · exact ho.input.symm.trans (hp.input.trans hmatch.input)
  · exact ho.output.symm.trans (hp.output.trans hmatch.output)

end Ram.Examples.InsertionSort
