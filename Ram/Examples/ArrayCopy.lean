/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Traversal
import Ram.Named.Declaration
import Ram.Array.Observation

/-!
# A compiled non-overlapping array-copy block

This is the named version of the reusable traversal in `Ram.Array.Traversal`.
Its code is fixed for every length, word width, and array content. The machine
theorems start at the main block with preloaded arrays and the three operands
already in registers; they do not claim an uncharged input loader or an
execution from the machine's zero-initialized state.

The final halt is executed and counted. The destination and unchanged source
are observed in the actual halted machine memory, not only in a source state.
Every destination-external word in the source heap is also preserved, while
the separate ABI frame relation retains the old stack.
-/

namespace Ram.Examples.ArrayCopy

ram_def named := ram_program% {
  main locals (source, destination, remaining) {
    while remaining {
      store[destination] := load[source];
      source := source + 1;
      destination := destination + 1;
      remaining := remaining - 1;
    }
  }
}

theorem named_body : named.main = Source.Array.copy := rfl

theorem valid : LocalCompiler.Valid 3 [] Source.Array.copy := by
  simp [LocalCompiler.Valid, Compiler.Valid, Source.Array.copy,
    Source.Array.copyCondition, Source.Array.copyBody,
    Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]

def code : Code := LocalCompiler.rawLink 3 [] Source.Array.copy

theorem named_compiles : named.compile = some code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩

theorem code_length : code.length = 21 := rfl

/-- Run the compiled block and its halt from an already matching, preloaded
state at PC 1. The skipped prologue is not included in this block budget. -/
theorem block_runs {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {s : Source.State w} {start : State w}
    (hw : 0 < w) (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (hpre : Source.Array.CopyPre heapLimit source destination xs ys s)
    (hmatch : Source.State.Matches heapLimit 3 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 3)).toNat)
    (hcodefit : code.length < 2 ^ w) :
    ∃ sourceFinal finish,
      TerminatesWithin code (19 * xs.length + 3) start finish ∧
      Source.Array.CopyPost heapLimit source destination xs s sourceFinal ∧
      Source.State.Observes heapLimit 3 sourceFinal finish ∧
      FramePreserved 3 heapLimit start finish := by
  have hstack : Compiler.StackFits 3 0 start := by
    simpa only [Compiler.StackFits, Nat.zero_mul, Nat.add_zero] using
      Word.toNat_lt (start.regs (ABI.sp 3))
  simpa only [Nat.add_assoc] using
    (Source.Array.copy_contract (control := 3) (program := []) (depth := 0)
      hw hlen hdisjoint).compile_block_observed
      (LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩)
      hcodefit hpre hmatch hpc hheap hstack

/-- The mathematical source list is present at both source and destination in
the actual final RAM memory. The frame observation covers every other heap
word; it does not equate private target stack words with source memory. -/
theorem copies_on_machine {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {s : Source.State w} {start : State w}
    (hw : 0 < w) (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (hpre : Source.Array.CopyPre heapLimit source destination xs ys s)
    (hmatch : Source.State.Matches heapLimit 3 s start)
    (hpc : start.pc = 1) (hheap : heapLimit ≤ (start.regs (ABI.sp 3)).toNat)
    (hcodefit : code.length < 2 ^ w) :
    ∃ finish,
      TerminatesWithin code (19 * xs.length + 3) start finish ∧
      ArrayRep finish.mem source xs ∧ ArrayRep finish.mem destination xs ∧
      (∀ address, address.toNat < heapLimit →
        address.toNat < destination.toNat ∨ destination.toNat + xs.length ≤ address.toNat →
        finish.mem address = start.mem address) ∧
      finish.regs named.mainReg.remaining = 0 ∧ finish.input = start.input ∧
      finish.outputRev = start.outputRev := by
  obtain ⟨sourceFinal, finish, he, hp, ho, _⟩ :=
    block_runs hw hlen hdisjoint hpre hmatch hpc hheap hcodefit
  refine ⟨finish, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ho.array hp.source_array
  · exact ho.array hp.destination_array
  · exact ho.arrayFrame hmatch.observes hp.frame
  · exact (ho.regs named.mainReg.remaining (by decide)).symm.trans hp.count
  · exact ho.input.symm.trans (hp.input.trans hmatch.input)
  · exact ho.output.symm.trans (hp.output.trans hmatch.output)

end Ram.Examples.ArrayCopy
