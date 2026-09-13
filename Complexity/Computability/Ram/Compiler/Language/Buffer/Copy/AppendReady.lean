/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.Realization
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Allocation
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic

/-!
# Readiness of the existing allocating array append

The actual append body allocates its destination, invokes the shared copy-into
body twice, and returns the new buffer. Its old source contract supplies the
ordinary array append result and preservation of every initial observation.
The input views may overlap. Only the fresh destination is required to be
disjoint, which follows from the actual allocation.

The measured interface retains an existing source execution, its compiler count,
the actual final heap and the exact cursor increase. It assumes no time budget.
Word ranges and enough space for the combined output are explicit; complete
machine launches additionally require their representation and code/stack facts.
-/

namespace Ram.LanguageCompiler.BufferCopy

open Complexity.Language
open Complexity.Language.Buffer

/-- The same copy-into invocation has its source contents/frame postcondition and
an unchanged arena cursor. Its actual compiler count is retained without a bound. -/
theorem copyInto_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (source target : Buffer .nat) (offset : Nat) (input output : Array Nat) (heap : Heap)
    (sourceContents : source.Contents heap input) (targetContents : target.Contents heap output)
    (separated : target.Disjoint source) (extent : offset + input.size ≤ output.size)
    (targetFits : target.length < 2 ^ w)
    (valuesFit : ∀ i (hi : i < input.size), input[i] < 2 ^ w) :
    ArenaMeasured Copy.program w heapLimit 0 (Copy.program.body Copy.copyIntoId)
      (fun finish control finalCursor _ => ∃ value, control = .returned value ∧
        finalCursor = cursor ∧ source.Contents finish.heap input ∧
        target.Contents finish.heap (copied input output offset input.size) ∧
        target.PreservesOutside heap finish.heap)
      ⟨Copy.copyInto_args source target offset, heap⟩ cursor := by
  obtain ⟨finish, value, realized⟩ :=
    copyInto_realizable positive input output valuesFit
      (Copy.copyInto_args source target offset) heap
      ⟨sourceContents, targetContents, separated, extent, targetFits⟩
  have property := (copyInto_total input output).postcondition
    (args := Copy.copyInto_args source target offset) (heap := heap)
    ⟨sourceContents, targetContents, separated, extent⟩ realized.erase
  have ready := realized.arenaReady heapLimit cursor
  obtain ⟨steps, cost⟩ := ready.exists_cost
  exact ⟨finish, .returned value, cursor, steps, realized.erase, ready, cost,
    value, rfl, rfl, property⟩

/-- Allocate and append through the actual two copying calls. Both calls reuse
one caller depth; the exact reserved growth is the combined output length. The
array equation and old-heap frame come from the existing source append theorem. -/
theorem append_arenaMeasured {w heapLimit cursor : Nat} (positive : 0 < w)
    (left right : Buffer .nat) (leftValues rightValues : Array Nat) (heap : Heap)
    (observedLeft : left.Contents heap leftValues)
    (observedRight : right.Contents heap rightValues)
    (leftValuesFit : ∀ i (hi : i < leftValues.size), leftValues[i] < 2 ^ w)
    (rightValuesFit : ∀ i (hi : i < rightValues.size), rightValues[i] < 2 ^ w)
    (sizeFits : leftValues.size + rightValues.size < 2 ^ w)
    (space : cursor + leftValues.size + rightValues.size ≤ heapLimit) :
    ArenaMeasured Copy.program w heapLimit 1 (Copy.program.body Copy.appendId)
      (fun finish control finalCursor _ => ∃ target, control = .returned target ∧
        finalCursor = cursor + leftValues.size + rightValues.size ∧
        target.Contents finish.heap (leftValues ++ rightValues) ∧
        target.object = heap.objects.size ∧ PreservesContents heap finish.heap)
      ⟨Copy.append_args left right, heap⟩ cursor := by
  let totalSize := left.length + right.length
  let allocated := heap.alloc (τ := .nat) totalSize 0
  let target := allocated.1
  let initialValues : Array Nat := Array.replicate totalSize 0
  have leftSize : leftValues.size = left.length := observedLeft.size_eq
  have rightSize : rightValues.size = right.length := observedRight.size_eq
  have leftFits : left.length < 2 ^ w := by omega
  have rightFits : right.length < 2 ^ w := by omega
  have totalFits : totalSize < 2 ^ w := by dsimp only [totalSize]; omega
  have capacity : cursor + totalSize ≤ heapLimit := by dsimp only [totalSize]; omega
  have targetFits : target.length < 2 ^ w := by
    simpa only [target, allocated, Heap.alloc_length] using totalFits
  have leftNow : left.Contents allocated.2 leftValues := observedLeft.alloc totalSize 0
  have rightNow : right.Contents allocated.2 rightValues := observedRight.alloc totalSize 0
  have initialized : target.Contents allocated.2 initialValues := heap.alloc_contents totalSize 0
  have separatedLeft : target.Disjoint left := observedLeft.valid.rooted.disjoint_alloc totalSize 0
  have separatedRight : target.Disjoint right := observedRight.valid.rooted.disjoint_alloc totalSize 0
  have firstCopy := copyInto_arenaMeasured (heapLimit := heapLimit)
    (cursor := cursor + totalSize) positive left target 0 leftValues initialValues allocated.2
    leftNow initialized separatedLeft
    (by simp only [initialValues, Array.size_replicate, Nat.zero_add]; dsimp only [totalSize]; omega)
    targetFits leftValuesFit
  have measured : ArenaMeasured Copy.program w heapLimit 1
      (Copy.program.body Copy.appendId)
      (fun _ control finalCursor _ => ∃ target, control = .returned target ∧
        finalCursor = cursor + leftValues.size + rightValues.size)
      ⟨Copy.append_args left right, heap⟩ cursor := by
    ram_source_arena_step
    apply ArenaMeasured.alloc
    · exact Nat.two_pow_pos w
    · exact capacity
    · ram_source_arena_step
      ram_source_arena_call measured using firstCopy
        as firstFinish firstValue firstCursor firstSteps firstObserved firstFits
      have firstCursorEq := firstObserved.1
      subst firstCursor
      have rightAfter : right.Contents firstFinish.heap rightValues :=
        firstObserved.2.2.2 right rightValues separatedRight rightNow
      have secondCopy := copyInto_arenaMeasured (heapLimit := heapLimit)
        (cursor := cursor + totalSize) positive right target left.length rightValues
        (copied leftValues initialValues 0 leftValues.size) firstFinish.heap
        rightAfter firstObserved.2.2.1 separatedRight
        (by simp only [copied_size, initialValues, Array.size_replicate];
            dsimp only [totalSize]; omega)
        targetFits rightValuesFit
      ram_source_arena_step
      ram_source_arena_call measured using secondCopy
        as secondFinish secondValue secondCursor secondSteps secondObserved secondFits
      have secondCursorEq := secondObserved.1
      subst secondCursor
      ram_source_arena_step
      exact ⟨_, rfl, by dsimp only [totalSize]; omega⟩
  exact measured.with_spec (append_total leftValues rightValues) ⟨observedLeft, observedRight⟩

end Ram.LanguageCompiler.BufferCopy
