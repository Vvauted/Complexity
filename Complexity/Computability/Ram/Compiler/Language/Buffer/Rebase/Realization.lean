/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Rebase
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources.Finite
import Complexity.Computability.Ram.Compiler.Language.Arena.Verification
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.LoopTactic
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Word realization of the boundary-rebasing worker

The existing source contracts supply loop invariants, progress and termination.
This module checks the actual reads, truncated natural subtraction, writes and
index increments against the selected word width. The base and read cells must
fit; no ordering of a cell above the base is needed for natural subtraction.
The worker does not allocate. Arena transport retains its writes and an unchanged
cursor, without a time budget or a physical placement.
-/

namespace Ram.LanguageCompiler.BufferRebase

open Complexity.Language
open Complexity.Language.Buffer

/-- Source observations and scalar ranges for the actual rebasing worker. -/
def copyIntoPre (w : Nat) (input output : Array Nat) :
    Env [.buffer .nat, .buffer .nat, .nat] → Heap → Prop :=
  fun args heap => args.head.Contents heap input ∧
    args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
    input.size ≤ output.size ∧ args.tail.head.length < 2 ^ w ∧
    args.tail.tail.head < 2 ^ w

/-- Guard readiness checks the actual length, cursor and Boolean result. -/
theorem guard_realizable {w : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (base index : Nat) (heap : Heap)
    (indexFits : index < 2 ^ w) (lengthFits : source.length < 2 ^ w) :
    RealizationWP Rebase.program w 0 Rebase.copyInto_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨Rebase.copyInto_loop1.View.symm (index, source, target, base, ()), heap⟩ := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  ram_source_locals Rebase.copyInto_loop1
  ram_source_realize_step
  all_goals first | omega | split <;> omega

/-- A single actual body reads the represented source cell, writes its value,
and advances the cursor. The existing source invariant supplies access validity. -/
theorem body_realizable {w : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (base : Nat) (input output : Array Nat)
    (index : Nat) (heap : Heap)
    (current : rebaseInvariant source target base input output index heap)
    (available : index < input.size) (extent : input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w) (baseFits : base < 2 ^ w) (valueFits : input[index] < 2 ^ w) :
    RealizationWP Rebase.program w 0 Rebase.copyInto_loop1.Body
      (fun _ => True) (fun _ _ => True)
      ⟨Rebase.copyInto_loop1.View.symm (index, source, target, base, ()), heap⟩ := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  have sourceSize : input.size = source.length := current.2.1.size_eq
  have targetSize : output.size = target.length := by
    simpa only [copied_size] using current.2.2.size_eq
  have loaded : heap.read source index = .ok input[index] := current.2.1.read available
  have writable (value : Nat) : ∃ finish, heap.write target index value = .ok finish := by
    have within : index < (copied (input.map (· - base)) output 0 index).size := by
      simp only [copied_size]
      omega
    obtain ⟨finish, written, _⟩ := current.2.2.write_exists within value
    exact ⟨finish, written⟩
  ram_source_locals Rebase.copyInto_loop1
  ram_source_realize_step
  all_goals
    simp only [loaded, Except.ok.injEq] at *
    first
    | omega
    | exact ⟨input[index], rfl, valueFits⟩
    | exact writable _

/-- Add ranges to the already terminating source loop. Invariant preservation
and termination reuse the source contracts, with no second loop induction. -/
theorem loop_realizable {w : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (base : Nat) (input output : Array Nat)
    (index : Nat) (heap : Heap)
    (current : rebaseInvariant source target base input output index heap)
    (separated : target.Disjoint source) (extent : input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w) (baseFits : base < 2 ^ w)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    RealizationWP Rebase.program w 0 Rebase.copyInto_loop1.Code
      (fun _ => True) (fun _ _ => False)
      ⟨Rebase.copyInto_loop1.View.symm (index, source, target, base, ()), heap⟩ := by
  have sourceSize : input.size = source.length := current.2.1.size_eq
  have targetSize : output.size = target.length := by
    simpa only [copied_size] using current.2.2.size_eq
  have sourceFits : source.length < 2 ^ w := by omega
  ram_source_loop_realize
    using (rebase_guard source target base input output),
      (rebase_body source target base input output separated extent)
    total rebase_loop source target base input output heap separated extent
  case enterBody =>
    intro _ _ _ _ _ ready
    exact ⟨ready.2.2.1, ready.2.2.2.mp rfl⟩
  · exact ⟨current, Buffer.PreservesOutside.refl target heap⟩
  · rintro ⟨i, ⟨⟩⟩ entry initial
    exact guard_realizable positive source target base i entry
      (by have := initial.1; omega) sourceFits
  · rintro ⟨i, ⟨⟩⟩ entry ⟨j, ⟨⟩⟩ afterHeap initial ready
    have available : j < input.size := ready.2.2.2.mp rfl
    exact body_realizable positive source target base input output j afterHeap
      ready.2.2.1 available extent targetFits baseFits (valuesFit j available)
  · intro _ _ _ _ _ _ _ _ completed
    exact completed.2.1
  · exact current

/-- The actual callable copy-into body needs no nested-call capacity. Source
validity, destination length and read-cell ranges suffice without a time budget. -/
theorem copyInto_realizable {w : Nat} (positive : 0 < w) (input output : Array Nat)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    FunctionRealizable Rebase.program w 0 Rebase.copyIntoId (copyIntoPre w input output) := by
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold copyIntoPre
  ram_source_realize (source target base)
  all_goals
    rcases ‹source.Contents _ input ∧ target.Contents _ output ∧ target.Disjoint source ∧
      input.size ≤ output.size ∧ target.length < 2 ^ w ∧ base < 2 ^ w› with
      ⟨sourceContents, targetContents, separated, extent, targetFits, baseFits⟩
    first
    | omega
    | apply (loop_realizable positive source target base input output 0 _
        (by simpa only [rebaseInvariant, copied_zero] using
          And.intro (Nat.zero_le input.size) (And.intro sourceContents targetContents))
        separated extent targetFits baseFits valuesFit).mono_post
      · intro finish _
        ram_source_realize_step
      · intro value finish impossible
        exact False.elim impossible

/-- The same nonallocating copy body is arena-realizable at every entry cursor.
The bridge retains its writes and introduces no additional capacity or cost premise. -/
theorem copyInto_arenaRealizable {w : Nat} (positive : 0 < w)
    (input output : Array Nat) (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w)
    (heapLimit : Nat) :
    FunctionArenaRealizable Rebase.program w heapLimit 0 Rebase.copyIntoId
      (fun args heap _ => copyIntoPre w input output args heap) :=
  (copyInto_realizable positive input output valuesFit).arenaRealizable heapLimit

/-- Indexed zero-growth readiness for actual copy-into invocations. Callers
choose the existing source arguments; determinism retains their same execution. -/
theorem copyInto_arenaResources {w : Nat} (positive : 0 < w)
    (input output : Array Nat) (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w)
    (heapLimit : Nat) :
    FunctionArenaResources Rebase.program (Rebase.program.body Rebase.copyIntoId)
      (fun args : Env [.buffer .nat, .buffer .nat, .nat] => args)
      (copyIntoPre w input output) w heapLimit 0 (fun _ => 0) := by
  exact FunctionArenaResources.of_functionRealizable (same := rfl)
    (copyInto_realizable positive input output valuesFit) (fun _ _ ready => ready)

end Ram.LanguageCompiler.BufferRebase
