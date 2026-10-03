/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
import Complexity.Computability.Ram.Compiler.Local.Function.Space
import Complexity.Computability.Ram.Execution.Space

/-!
# Source resource bounds for seeded physical RAM space

A source readiness proof may use a small heap bound `H` while the actual RAM
stack starts at a larger `heapLimit`. The invocation, code, entry memory and
instruction count are unchanged. The footprint includes the initial reserved
arena prefix and every actual heap/stack access, but not the unused address gap.
This measures cumulative physical words, not exact peak-live storage. Registers,
code, streams and external loading remain separate. No time budget is required.
-/

namespace Ram.LanguageCompiler
open Complexity.Language

namespace ArenaRep

/-- Widen only a safety limit, retaining all represented addresses and memory. -/
theorem mono_heap {w cursor small large : Nat} {placement : Nat → Word w}
    {heap : Heap} {entry : Source.State w}
    (arena : ArenaRep placement cursor small heap entry) (bound : small ≤ large)
    (fits : large < 2 ^ w) : ArenaRep placement cursor large heap entry := by
  refine ⟨⟨?_, arena.heapRep.fit, arena.heapRep.disjoint, arena.heapRep.backward⟩,
    arena.cursor_pos, arena.cursor_le.trans bound, fits, arena.cursor_eq,
    arena.storedReserved⟩
  intro object value found
  exact ⟨(arena.heapRep.stored found).1, (arena.heapRep.stored found).2.trans bound⟩

end ArenaRep

private theorem seeded_regions_card {w H stackBase frames initialWords : Nat}
    {accesses : Finset (Word w)} (initial : initialWords ≤ H)
    (fits : stackBase + frames < 2 ^ w) (separated : H ≤ stackBase)
    (bounded : ∀ address ∈ accesses,
      address.toNat < H ∨ stackBase ≤ address.toNat ∧ address.toNat < stackBase + frames) :
    (Ram.initialSegment w initialWords ∪ accesses).card ≤ H + frames := by
  let region := Ram.addressInterval w 0 H ∪ Ram.addressInterval w stackBase frames
  have contained : Ram.initialSegment w initialWords ∪ accesses ⊆ region := by
    intro address member
    rcases Finset.mem_union.mp member with seeded | accessed
    · obtain ⟨index, before, rfl⟩ := Finset.mem_image.mp seeded
      have small : index < H := (Finset.mem_range.mp before).trans_le initial
      apply Finset.mem_union_left
      apply (Ram.mem_addressInterval_iff (by omega)).mpr
      rw [Word.ofNat_toNat_of_lt (by omega)]
      exact ⟨Nat.zero_le _, by simpa only [Nat.zero_add] using small⟩
    · rcases bounded address accessed with low | high
      · exact Finset.mem_union_left _
          ((Ram.mem_addressInterval_iff (by omega)).mpr ⟨Nat.zero_le _, by omega⟩)
      · exact Finset.mem_union_right _
          ((Ram.mem_addressInterval_iff (Nat.le_of_lt fits)).mpr high)
  exact (Finset.card_le_card contained).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (Ram.addressInterval_card_le w 0 H)
        (Ram.addressInterval_card_le w stackBase frames)))

namespace FunctionArenaExecution

/-- The published runner result is the actual halted execution of its compiled
code at the unchanged entry stack base. -/
theorem machine_exec {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth heapLimit : Nat} {placement : Nat → Word w}
    {args : Env signatures[fn].params} {heap : Heap} {entry : Source.State w}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry) :
    Ram.Exec (lowerCode program fn) outcome.result.steps
        (LocalCompiler.Function.start (programControl program) heapLimit
          (envWords placement args) entry) outcome.result.state ∧
      outcome.result.state.status = .halted := by
  apply Ram.runUntil_halted_iff.mp
  have executed := outcome.run_halted
  simp only [LocalCompiler.Function.runUntil, envWords_length, ↓reduceIte] at executed
  have compiled := compile_eq_some program fn
  simp only [Fin.getElem_fin] at compiled
  rw [compiled] at executed
  simpa only [Option.bind_some] using executed

/-- The same published invocation has a small physical footprint whenever its
measured source invocation admits the smaller heap bound. The actual stack base
and runner are those of `outcome`, not replaced by the proof's heap bound. -/
theorem spaceWords_le_regions {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth heapLimit H initialWords : Nat} {placement : Nat → Word w}
    {args : Env signatures[fn].params} {heap : Heap} {entry finish : Source.State w}
    {value : List (Word w)}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry)
    (invocation : Source.FunctionMeasuredExec (programControl program) (lowerProgram program)
      H depth (lowerFunc program fn) (envWords placement args) outcome.bodySteps entry value finish)
    (separated : H ≤ heapLimit) (initial : initialWords ≤ H) :
    Ram.spaceWords (lowerCode program fn) outcome.result.steps
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry) (Ram.initialSegment w initialWords) ≤
      H + (depth + 1) * ABI.frameSize (programControl program) := by
  apply seeded_regions_card initial outcome.capacity.stackCapacity separated
  intro address member
  rw [outcome.steps_eq] at member
  exact LocalCompiler.Function.heapAccesses_in_regions (compile_eq_some program fn)
    (lowerProgram_lookup program fn) outcome.capacity.codeCapacity separated
    outcome.capacity.stackCapacity invocation member

/-- A reusable finite space certificate retains the same actual result and
trace. It does not choose an alternative computation or space observation. -/
theorem spaceBound_regions {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth heapLimit H initialWords : Nat} {placement : Nat → Word w}
    {args : Env signatures[fn].params} {heap : Heap} {entry finish : Source.State w}
    {value : List (Word w)}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry)
    (invocation : Source.FunctionMeasuredExec (programControl program) (lowerProgram program)
      H depth (lowerFunc program fn) (envWords placement args) outcome.bodySteps entry value finish)
    (separated : H ≤ heapLimit) (initial : initialWords ≤ H) :
    Ram.SpaceBound (lowerCode program fn) outcome.result.steps
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry) outcome.result.state (Ram.initialSegment w initialWords)
      (H + (depth + 1) * ABI.frameSize (programControl program)) :=
  ⟨outcome.machine_exec.1, outcome.machine_exec.2,
    outcome.spaceWords_le_regions invocation separated initial⟩

end FunctionArenaExecution

namespace ArenaExecutionCost

/-- Publish the actual large-stack invocation from a source proof with a small
heap limit, preserving its result, heap, cursor and exact measured count. -/
theorem execute_space {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit H depth cursor finalCursor steps : Nat}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {ready : ArenaReady execution w H depth cursor finalCursor}
    {placement : Nat → Word w} {entry : Source.State w}
    (cost : ArenaExecutionCost ready steps)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (separated : H ≤ heapLimit) (smallArena : ArenaRep placement cursor H heap entry) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      outcome.value = value ∧ outcome.heap = finish.heap ∧ outcome.cursor = finalCursor ∧
      outcome.bodySteps = steps + 2 ∧
      Ram.spaceWords (lowerCode program fn) outcome.result.steps
        (LocalCompiler.Function.start (programControl program) heapLimit
          (envWords placement args) entry) (Ram.initialSegment w cursor) ≤
        H + (depth + 1) * ABI.frameSize (programControl program) := by
  obtain ⟨finalPlacement, sourceFinish, smallInvocation, finalArena, agreement⟩ :=
    cost.functionMeasuredExec (programControl program) launch.positive
      launch.arguments launch.rooted entry smallArena
  have invocation := smallInvocation.mono_heap separated
  obtain ⟨target, run, returned, observed⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured (compile_eq_some program fn)
      (lowerProgram_lookup program fn) launch.codeCapacity launch.stackCapacity invocation
  have largeFits : heapLimit < 2 ^ w := launch.arena.limit_lt
  let outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry := {
    value := value
    heap := finish.heap
    finalPlacement := finalPlacement
    cursor := finalCursor
    result := ⟨target, LocalCompiler.Function.callSteps (programControl program)
      (lowerFunc program fn) (steps + 2) + 1, .halted⟩
    sourceFinish := sourceFinish
    bodySteps := steps + 2
    capacity := launch.toFunctionCapacity
    source := Complexity.Language.Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩
    run := run
    halted := rfl
    returned := by simpa only [lowerFunc_results_length] using returned
    fits := ready.outcome_fits
    memory := (finalArena.mono_heap separated largeFits).of_observes observed
    agreement := agreement
    invocation := invocation
    observed := observed
    steps_eq := rfl }
  exact ⟨outcome, rfl, rfl, rfl, rfl,
    outcome.spaceWords_le_regions smallInvocation separated smallArena.cursor_le⟩

end ArenaExecutionCost

namespace ArenaReady

/-- Successful publication and physical space do not require a proposed time
budget. Scope reclamation uses its actual maximum reserve `H`, not final cursor. -/
theorem execute_space {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit H depth cursor finalCursor : Nat}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {placement : Nat → Word w} {entry : Source.State w}
    (ready : ArenaReady execution w H depth cursor finalCursor)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (separated : H ≤ heapLimit) (smallArena : ArenaRep placement cursor H heap entry) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      outcome.value = value ∧ outcome.heap = finish.heap ∧ outcome.cursor = finalCursor ∧
      Ram.spaceWords (lowerCode program fn) outcome.result.steps
        (LocalCompiler.Function.start (programControl program) heapLimit
          (envWords placement args) entry) (Ram.initialSegment w cursor) ≤
        H + (depth + 1) * ABI.frameSize (programControl program) := by
  obtain ⟨steps, cost⟩ := ready.exists_cost
  obtain ⟨outcome, returned, heapEq, cursorEq, _, space⟩ :=
    cost.execute_space launch separated smallArena
  exact ⟨outcome, returned, heapEq, cursorEq, space⟩

end ArenaReady
end Ram.LanguageCompiler
