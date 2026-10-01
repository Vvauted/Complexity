/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Rebase.Realization
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Allocation
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic

/-!
# Readiness of allocating boundary rebasing

The actual allocator and rebasing worker retain the existing source contents
and frame contract. The final arena cursor grows by exactly the input length,
including zero. Only the input cells that are read, the base and the source
length need word bounds; allocation requires actual remaining arena capacity.
These measured witnesses do not choose a time budget or a physical placement.
-/

namespace Ram.LanguageCompiler.BufferRebase

open Complexity.Language
open Complexity.Language.Buffer

/-- The nonallocating worker preserves the arena cursor and retains its actual
source contents, updated destination and outside-view frame. -/
theorem copyInto_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (base : Nat) (input output : Array Nat) (heap : Heap)
    (sourceContents : source.Contents heap input) (targetContents : target.Contents heap output)
    (separated : target.Disjoint source) (extent : input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w) (baseFits : base < 2 ^ w)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    ArenaMeasured Rebase.program w heapLimit 0 (Rebase.program.body Rebase.copyIntoId)
      (fun finish control finalCursor _ => ∃ value, control = .returned value ∧
        finalCursor = cursor ∧ source.Contents finish.heap input ∧
        target.Contents finish.heap (copied (input.map (· - base)) output 0 input.size) ∧
        target.PreservesOutside heap finish.heap)
      ⟨Rebase.copyInto_args source target base, heap⟩ cursor := by
  obtain ⟨finish, value, realized⟩ :=
    copyInto_realizable positive input output valuesFit
      (Rebase.copyInto_args source target base) heap
      ⟨sourceContents, targetContents, separated, extent, targetFits, baseFits⟩
  have property := (rebaseInto_total input output).postcondition
    (args := Rebase.copyInto_args source target base) (heap := heap)
    ⟨sourceContents, targetContents, separated, extent⟩ realized.erase
  have ready := realized.arenaReady heapLimit cursor
  obtain ⟨steps, cost⟩ := ready.exists_cost
  exact ⟨finish, .returned value, cursor, steps, realized.erase, ready, cost,
    value, rfl, rfl, property⟩

/-- Allocate and rebase with exact retained cursor growth. The result and old
contents frame come from the independently proved source specification. -/
theorem copy_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (source : Buffer .nat) (base : Nat) (input : Array Nat) (heap : Heap)
    (observed : source.Contents heap input)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w)
    (lengthFits : input.size < 2 ^ w) (baseFits : base < 2 ^ w)
    (space : cursor + input.size ≤ heapLimit) :
    ArenaMeasured Rebase.program w heapLimit 1 (Rebase.program.body Rebase.copyId)
      (fun finish control finalCursor _ => ∃ target, control = .returned target ∧
        finalCursor = cursor + input.size ∧
        target.Contents finish.heap (input.map (· - base)) ∧
        target.object = heap.objects.size ∧ PreservesContents heap finish.heap)
      ⟨Rebase.copy_args source base, heap⟩ cursor := by
  let allocated := heap.alloc (τ := .nat) source.length 0
  let target := allocated.1
  let initialValues := Array.replicate source.length 0
  have sourceFits : source.length < 2 ^ w := by simpa only [observed.size_eq] using lengthFits
  have capacity : cursor + source.length ≤ heapLimit := by
    simpa only [observed.size_eq] using space
  have targetFits : target.length < 2 ^ w := by
    simpa only [target, allocated, Heap.alloc_length] using sourceFits
  have sourceNow : source.Contents allocated.2 input := observed.alloc source.length 0
  have initialized : target.Contents allocated.2 initialValues := heap.alloc_contents source.length 0
  have separated : target.Disjoint source := observed.valid.rooted.disjoint_alloc source.length 0
  have worker := copyInto_arenaMeasured (heapLimit := heapLimit)
    (cursor := cursor + source.length) positive source target base input initialValues allocated.2
    sourceNow initialized separated
    (by simpa only [initialValues, Array.size_replicate] using observed.size_eq.le)
    targetFits baseFits valuesFit
  have measured : ArenaMeasured Rebase.program w heapLimit 1 (Rebase.program.body Rebase.copyId)
      (fun _ control finalCursor _ => ∃ target, control = .returned target ∧
        finalCursor = cursor + input.size)
      ⟨Rebase.copy_args source base, heap⟩ cursor := by
    ram_source_arena_step
    apply ArenaMeasured.alloc
    · exact Nat.two_pow_pos w
    · exact capacity
    · ram_source_arena_step
      ram_source_arena_call measured using worker
        as workerFinish workerValue workerCursor workerSteps workerObserved workerFits
      have cursorEq := workerObserved.1
      subst workerCursor
      ram_source_arena_step
      simp only [observed.size_eq]
  exact measured.with_spec (rebase_total input) observed

/-- The measured allocating body supplies reusable indexed readiness for every
existing execution, without requiring callers to build a new source execution. -/
theorem copy_arenaResources {w : Nat} (positive : 0 < w) (input : Array Nat)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) (heapLimit : Nat) :
    FunctionArenaResources Rebase.program (Rebase.program.body Rebase.copyId)
      (fun args : Buffer .nat × Nat => Rebase.copy_args args.1 args.2)
      (fun args heap => args.1.Contents heap input) w heapLimit 1 (fun _ => input.size) := by
  intro args heap cursor observed fits capacity finish value execution
  have sourceFits : args.1.length < 2 ^ w := fits .here
  have baseFits : args.2 < 2 ^ w := fits (.there .here)
  obtain ⟨finalCursor, steps, ready, _, target, returned, cursorEq, _⟩ :=
    (copy_arenaMeasured positive args.1 args.2 input heap observed valuesFit
      (by simpa only [observed.size_eq] using sourceFits) baseFits capacity).at_exec execution
  exact ⟨finalCursor, ready, cursorEq.le⟩

end Ram.LanguageCompiler.BufferRebase
