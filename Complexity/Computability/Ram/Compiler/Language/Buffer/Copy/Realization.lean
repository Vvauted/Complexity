/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources.Finite
import Complexity.Computability.Ram.Compiler.Language.Arena.Verification
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.LoopTactic
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Word realization of the shared source copy loop

The existing source copy invariant, step contracts and terminating loop supply
all mathematical behavior and descent. This module adds ranges for the actual
reads, offset additions, writes and loop increments. The destination length
bound and the source contract's extent imply the source length, offset and
access-index bounds. Only source cells that are actually read need value ranges;
the old destination contents need not fit this local realization interface.

The copy loop has no nested calls and performs no allocation. Its existing
fixed-heap realization therefore supplies arena readiness with an unchanged
cursor, while retaining the actual destination writes. Neither realization nor
its arena transport requires a time budget, a physical placement, or an assumed
target execution. A complete machine launch still needs its heap representation
and code/stack capacity conditions.
-/

namespace Ram.LanguageCompiler.BufferCopy

open Complexity.Language
open Complexity.Language.Buffer

/-- Source validity and the one sufficient descriptor range for copying into
an existing target. Source cell ranges are supplied separately. -/
def copyIntoPre (w : Nat) (input output : Array Nat) :
    Env [.buffer .nat, .buffer .nat, .nat] → Heap → Prop :=
  fun args heap => args.head.Contents heap input ∧
    args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
    args.tail.tail.head + input.size ≤ output.size ∧ args.tail.head.length < 2 ^ w

/-- Guard readiness checks the actual length, cursor and Boolean result. -/
theorem guard_realizable {w : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (offset index : Nat) (heap : Heap)
    (indexFits : index < 2 ^ w) (lengthFits : source.length < 2 ^ w) :
    RealizationWP Copy.program w 0 Copy.copyInto_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨Copy.copyInto_loop1.View.symm (index, source, target, offset, ()), heap⟩ := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  ram_source_locals Copy.copyInto_loop1
  ram_source_realize_step
  all_goals first | omega | split <;> omega

/-- A single actual body reads the represented source cell, writes its value,
and advances the cursor. The existing source invariant supplies access validity. -/
theorem body_realizable {w : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (offset : Nat) (input output : Array Nat)
    (index : Nat) (heap : Heap)
    (current : copyInvariant source target offset input output index heap)
    (available : index < input.size) (extent : offset + input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w) (valueFits : input[index] < 2 ^ w) :
    RealizationWP Copy.program w 0 Copy.copyInto_loop1.Body
      (fun _ => True) (fun _ _ => True)
      ⟨Copy.copyInto_loop1.View.symm (index, source, target, offset, ()), heap⟩ := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  have sourceSize : input.size = source.length := current.2.1.size_eq
  have targetSize : output.size = target.length := by
    simpa only [copied_size] using current.2.2.size_eq
  have loaded : heap.read source index = .ok input[index] := current.2.1.read available
  have writable (value : Nat) : ∃ finish, heap.write target (offset + index) value = .ok finish := by
    have within : offset + index < (copied input output offset index).size := by
      simp only [copied_size]
      omega
    obtain ⟨finish, written, _⟩ := current.2.2.write_exists within value
    exact ⟨finish, written⟩
  ram_source_locals Copy.copyInto_loop1
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
    (source target : Buffer .nat) (offset : Nat) (input output : Array Nat)
    (index : Nat) (heap : Heap)
    (current : copyInvariant source target offset input output index heap)
    (separated : target.Disjoint source) (extent : offset + input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    RealizationWP Copy.program w 0 Copy.copyInto_loop1.Code
      (fun _ => True) (fun _ _ => False)
      ⟨Copy.copyInto_loop1.View.symm (index, source, target, offset, ()), heap⟩ := by
  have sourceSize : input.size = source.length := current.2.1.size_eq
  have targetSize : output.size = target.length := by
    simpa only [copied_size] using current.2.2.size_eq
  have sourceFits : source.length < 2 ^ w := by omega
  ram_source_loop_realize
    using (copy_guard source target offset input output),
      (copy_body source target offset input output separated extent)
    total copy_loop source target offset input output heap separated extent
  case enterBody =>
    intro _ _ _ _ _ ready
    exact ⟨ready.2.2.1, ready.2.2.2.mp rfl⟩
  · exact ⟨current, Buffer.PreservesOutside.refl target heap⟩
  · rintro ⟨i, ⟨⟩⟩ entry initial
    exact guard_realizable positive source target offset i entry
      (by have := initial.1; omega) sourceFits
  · rintro ⟨i, ⟨⟩⟩ entry ⟨j, ⟨⟩⟩ afterHeap initial ready
    have available : j < input.size := ready.2.2.2.mp rfl
    exact body_realizable positive source target offset input output j afterHeap
      ready.2.2.1 available extent targetFits (valuesFit j available)
  · intro _ _ _ _ _ _ _ _ completed
    exact completed.2.1
  · exact current

/-- The actual callable copy-into body needs no nested-call capacity. Source
validity, destination length and read-cell ranges suffice without a time budget. -/
theorem copyInto_realizable {w : Nat} (positive : 0 < w) (input output : Array Nat)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    FunctionRealizable Copy.program w 0 Copy.copyIntoId (copyIntoPre w input output) := by
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold copyIntoPre
  ram_source_realize (source target offset)
  all_goals
    rcases ‹source.Contents _ input ∧ target.Contents _ output ∧ target.Disjoint source ∧
      offset + input.size ≤ output.size ∧ target.length < 2 ^ w› with
      ⟨sourceContents, targetContents, separated, extent, targetFits⟩
    first
    | omega
    | apply (loop_realizable positive source target offset input output 0 _
        (by simpa only [copyInvariant, copied_zero] using
          And.intro (Nat.zero_le input.size) (And.intro sourceContents targetContents))
        separated extent targetFits valuesFit).mono_post
      · intro finish _
        ram_source_realize_step
      · intro value finish impossible
        exact False.elim impossible

/-- The same nonallocating copy body is arena-realizable at every entry cursor.
The bridge retains its writes and introduces no additional capacity or cost premise. -/
theorem copyInto_arenaRealizable {w : Nat} (positive : 0 < w)
    (input output : Array Nat) (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w)
    (heapLimit : Nat) :
    FunctionArenaRealizable Copy.program w heapLimit 0 Copy.copyIntoId
      (fun args heap _ => copyIntoPre w input output args heap) :=
  (copyInto_realizable positive input output valuesFit).arenaRealizable heapLimit

/-- Indexed zero-growth readiness for actual copy-into invocations. Callers
choose the existing source arguments; determinism retains their same execution. -/
theorem copyInto_arenaResources {w : Nat} (positive : 0 < w)
    (input output : Array Nat) (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w)
    (heapLimit : Nat) :
    FunctionArenaResources Copy.program (Copy.program.body Copy.copyIntoId)
      (fun args : Env [.buffer .nat, .buffer .nat, .nat] => args)
      (copyIntoPre w input output) w heapLimit 0 (fun _ => 0) := by
  exact FunctionArenaResources.of_functionRealizable (same := rfl)
    (copyInto_realizable positive input output valuesFit) (fun _ _ ready => ready)

end Ram.LanguageCompiler.BufferCopy
