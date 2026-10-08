/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Space

/-!
# Reusable heap and stack regions of actual arena invocations

A small source safety certificate bounds accesses in the unchanged actual
invocation. Its stack remains at the public heap separator; the unused address
gap is not part of the footprint. Region inclusion, rather than a per-call
cardinality sum, allows repeated invocations to reuse their stack words.

`raise_stack` realizes a previously certified source invocation at a larger
actual stack base. It starts from the same complete entry state and retains the
new invocation's full returned RAM memory, not the smaller-stack run's memory.
-/

namespace Ram.LanguageCompiler
open Complexity.Language

/-- A smaller heap separator needs no additional code or stack capacity. -/
theorem FunctionCapacity.mono_heap {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth small large : Nat}
    (capacity : FunctionCapacity program fn w depth large) (bound : small ≤ large) :
    FunctionCapacity program fn w depth small :=
  ⟨capacity.positive, capacity.codeCapacity,
    (Nat.add_le_add_right bound _).trans_lt capacity.stackCapacity⟩

namespace FunctionArenaExecution

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w depth heapLimit H : Nat}
variable {placement : Nat → Word w} {args : Env signatures[fn].params}
variable {heap : Heap} {entry : Source.State w}

/-- Every actual address belongs to the small heap prefix or the real high
stack interval. Determinism aligns the independently supplied source count. -/
theorem heapAccesses_subset_regions
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry)
    {bodySteps : Nat} {value : List (Word w)} {finish : Source.State w}
    (invocation : Source.FunctionMeasuredExec (programControl program) (lowerProgram program)
      H depth (lowerFunc program fn) (envWords placement args) bodySteps entry value finish)
    (separated : H ≤ heapLimit) :
    outcome.heapAccesses ⊆ Ram.addressInterval w 0 H ∪
      Ram.addressInterval w heapLimit ((depth + 1) * ABI.frameSize (programControl program)) := by
  intro address member
  have same := (outcome.invocation.deterministic invocation).1
  unfold heapAccesses at member
  rw [outcome.steps_eq, same] at member
  have regions := LocalCompiler.Function.heapAccesses_in_regions (compile_eq_some program fn)
    (lowerProgram_lookup program fn) outcome.capacity.codeCapacity separated
    outcome.capacity.stackCapacity invocation member
  rcases regions with low | high
  · apply Finset.mem_union_left
    apply (Ram.mem_addressInterval_iff (by
      have := outcome.capacity.stackCapacity
      omega)).mpr
    exact ⟨Nat.zero_le _, by simpa only [Nat.zero_add] using low⟩
  · exact Finset.mem_union_right _
      ((Ram.mem_addressInterval_iff outcome.capacity.stackCapacity.le).mpr high)

/-- Realize the same source invocation at the specified larger actual stack
base. The returned state is the new real runner result. Source effects, placement,
cursor and instruction count are retained, together with a small final arena
and an address-set bound suitable for sequential reuse. -/
theorem raise_stack
    (small : FunctionArenaExecution program fn depth H placement args heap entry)
    (capacity : FunctionCapacity program fn w depth heapLimit)
    (separated : H ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      outcome.value = small.value ∧ outcome.heap = small.heap ∧
      outcome.finalPlacement = small.finalPlacement ∧ outcome.cursor = small.cursor ∧
      outcome.result.steps = small.result.steps ∧
      ArenaRep outcome.finalPlacement outcome.cursor H outcome.heap outcome.nextEntry ∧
      outcome.heapAccesses ⊆ Ram.addressInterval w 0 H ∪
        Ram.addressInterval w heapLimit
          ((depth + 1) * ABI.frameSize (programControl program)) := by
  have invocation := small.invocation.mono_heap separated
  obtain ⟨target, run, returned, observed⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured (compile_eq_some program fn)
      (lowerProgram_lookup program fn) capacity.codeCapacity capacity.stackCapacity invocation
  have same (address : Word w) (below : address.toNat < H) :
      target.mem address = small.result.state.mem address :=
    (observed.heap address (below.trans_le separated)).symm.trans
      (small.observed.heap address below)
  have smallMemory : ArenaRep small.finalPlacement small.cursor H small.heap
      (Source.State.ofRam target) := by
    apply small.memory.of_mem_eq_on (Nat.le_refl _) small.memory.cursor_le
    · exact (same 0 (by
        have positive := small.memory.cursor_pos.trans_le small.memory.cursor_le
        simpa only [BitVec.toNat_zero] using positive)).trans small.memory.cursor_eq
    · intro address _ below
      exact same address (below.trans_le small.memory.cursor_le)
  have largeFits : heapLimit < 2 ^ w := by
    have := capacity.stackCapacity
    omega
  let outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry := {
    value := small.value
    heap := small.heap
    finalPlacement := small.finalPlacement
    cursor := small.cursor
    result := ⟨target, LocalCompiler.Function.callSteps (programControl program)
      (lowerFunc program fn) small.bodySteps + 1, .halted⟩
    sourceFinish := small.sourceFinish
    bodySteps := small.bodySteps
    capacity := capacity
    source := small.source
    run := run
    halted := rfl
    returned := by simpa only [lowerFunc_results_length] using returned
    fits := small.fits
    memory := smallMemory.mono_heap separated largeFits
    agreement := small.agreement
    invocation := invocation
    observed := observed
    steps_eq := rfl }
  exact ⟨outcome, rfl, rfl, rfl, rfl, small.steps_eq.symm, smallMemory,
    outcome.heapAccesses_subset_regions small.invocation separated⟩

end FunctionArenaExecution
end Ram.LanguageCompiler
