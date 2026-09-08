/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Search
import Complexity.Computability.Ram.Source.Named.Basic
import Complexity.Computability.Ram.Verification.Execution

/-!
# A compiled sorted-array lower-bound search

The ordinary named program below lowers to the reusable search contract.
Execution starts at the main block with the array preloaded in the heap and
base, key and length already in registers. The theorem counts every executed
search instruction and the final halt, not an unimplemented input loader.

The returned index is observed in the actual machine register, the original
array is observed in machine memory, and every source-heap address is unchanged.
The compiler's private stack frame is tracked separately by `FramePreserved`.
-/

namespace Ram.Examples.BinarySearch

def named : Named.Bundle := ram_program% {
  main locals (base, key, lo, hi, mid) {
    lo := 0;
    while lo < hi {
      mid := lo + (hi - lo) / 2;
      if load[base + mid] < key {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
  }
}

theorem named_body : named.main = Source.Array.lowerBound := rfl

theorem valid : LocalCompiler.Valid 5 [] Source.Array.lowerBound := by
  simp [LocalCompiler.Valid, Compiler.Valid, Source.Array.lowerBound,
    Source.Array.Search.fixedRegisters, Source.Array.address,
    Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]

def code : Code := LocalCompiler.rawLink 5 [] Source.Array.lowerBound

theorem named_compiles : named.compile = some code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩

theorem code_length : code.length = 31 := rfl

/-- Run the checked block from a matching preloaded state at PC 1, then
execute its halt. The budget includes no skipped initialization prologue. -/
theorem block_runs {heapLimit : Nat} {base key : Word w} {xs : List (Word w)}
    {s : Source.State w} {start : State w} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (hpre : Source.Array.LowerBoundPre heapLimit base key xs s)
    (hmatch : Source.State.Matches heapLimit 5 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 5)).toNat)
    (hcodefit : code.length < 2 ^ w) :
    ∃ sourceFinal finish,
      TerminatesWithin code (25 * Nat.clog 2 (xs.length + 1) + 7) start finish ∧
      Source.Array.LowerBoundPost heapLimit base key xs s sourceFinal ∧
      Source.State.Observes heapLimit 5 sourceFinal finish ∧
      FramePreserved 5 heapLimit start finish := by
  have hstack : Compiler.StackFits 5 0 start := by
    simpa only [Compiler.StackFits, Nat.zero_mul, Nat.add_zero] using
      Word.toNat_lt (start.regs (ABI.sp 5))
  simpa only [Nat.add_assoc] using
    (Source.Array.lowerBound_contract (control := 5) (program := []) (depth := 0)
      hw hsorted).compile_block_observed
      (LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩)
      hcodefit hpre hmatch hpc hheap hstack

/-- The actual halted machine contains the correct insertion index and the
unchanged sorted array. Heap and I/O preservation are stated against the
actual entry machine, not just an intermediate source-level result. -/
theorem lower_bound_on_machine {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {s : Source.State w} {start : State w} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (hpre : Source.Array.LowerBoundPre heapLimit base key xs s)
    (hmatch : Source.State.Matches heapLimit 5 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 5)).toNat)
    (hcodefit : code.length < 2 ^ w) :
    ∃ finish,
      TerminatesWithin code (25 * Nat.clog 2 (xs.length + 1) + 7) start finish ∧
      Source.Array.LowerBoundSpec xs key (finish.regs 2).toNat ∧
      ArrayRep finish.mem base xs ∧
      (∀ address, address.toNat < heapLimit → finish.mem address = start.mem address) ∧
      finish.regs 0 = base ∧ finish.regs 1 = key ∧
      finish.input = start.input ∧ finish.outputRev = start.outputRev := by
  obtain ⟨sourceFinal, finish, he, hp, ho, _⟩ :=
    block_runs hw hsorted hpre hmatch hpc hheap hcodefit
  refine ⟨finish, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ho.regs 2 (by decide)]
    exact hp.result
  · refine ⟨hp.array.1.fits, ?_⟩
    intro i hi
    exact (ho.heap _ (hp.array.addr_lt hi)).symm.trans (hp.array.1.lookup i hi)
  · intro address ha
    exact (ho.heap address ha).symm.trans
      ((congrFun hp.mem address).trans (hmatch.heap address ha))
  · exact (ho.regs 0 (by decide)).symm.trans hp.base_reg
  · exact (ho.regs 1 (by decide)).symm.trans hp.key_reg
  · exact ho.input.symm.trans (hp.input.trans hmatch.input)
  · exact ho.output.symm.trans (hp.output.trans hmatch.output)

end Ram.Examples.BinarySearch
