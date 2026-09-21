/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedList
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Models
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendCost
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Nonuniform costs for the existing array-record loop

The unchanged `ArrayRangeNative.repeatAppend` copies a growing array on each
iteration. Its generated mathematical guard/body contracts transport the
current array observations through the actual heaps. The shared arena loop rule
reuses these contracts with a finite-sum potential, without a second execution
induction, a new termination argument or reconstruction of array handles.

The inferred body certificate uses the real allocating append cost, including
the caller's record updates. Structural composition accounts for the enclosing
function and its initialization once. The resulting all-input bound grows as
`1 + count + count * initialSize + count² * chunkSize`; its mathlib asymptotic
corollary concerns this same envelope. These are conditional cost contracts,
not readiness, capacity, space or complete launched-execution guarantees.
-/

namespace Complexity.Language.Examples.LinkedList.NativeRange.RepeatAppendCost

open Ram.LanguageCompiler
open ArrayRangeNative.Source.repeatAppend_loop1
open scoped BigOperators

/-- Infer the actual guard's uniform cost at the caller's depth. -/
def guardCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound ArrayRangeNative.Source.program w heapLimit 2
      Guard initial bound } := by
  ram_source_arena_cost

/-- Infer one round's cost from the current mathematical input lengths and
actual heap observations. Both append inputs may share storage. -/
def bodyCost (size : Nat) : { bound : Nat //
    ∀ w heapLimit (model : Model) (locals : Locals) (heap : Heap),
      (model_state model).values.size + (model_chunk model).size = size →
      modelRel model locals heap →
      StmtArenaCostBound ArrayRangeNative.Source.program w heapLimit 2
        Body ⟨View.symm locals, heap⟩ bound } := ⟨_, by
  intro w heapLimit model locals heap sized related
  have stateObserved := model_rel_state related
  have chunkObserved := model_rel_chunk related
  have bounded := BufferCopy.append_costBound
    (model_state model).values (model_chunk model) w heapLimit
  rw [sized] at bounded
  ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1 at *
  ram_source_arena_cost
    [bounded at (_, _)
      via ArrayRangeNative.Source.imports.Complexity.Language.Buffer.Copy.embedding]
  all_goals exact ⟨stateObserved.1, chunkObserved⟩⟩

/-- Sum the size-dependent round envelopes and the final false guard. -/
def loopBound (count size chunk : Nat) : Nat :=
  guardCost.val + 11 + ∑ index ∈ Finset.range count,
    (guardCost.val + (bodyCost (size + (index + 1) * chunk)).val + 10)

/-- The real append supplies the slope; caller bookkeeping is size-independent. -/
theorem bodyCost_eq (size : Nat) :
    (bodyCost size).val =
      (14 + BufferCopy.copyIntoGuardCost.val + BufferCopy.copyIntoBodyCost.val + 10) * size +
        (bodyCost 0).val := by
  simp only [bodyCost, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [BufferCopy.appendBodyBound_eq size]
  ring

/-- One iteration increases the current array length and consumes its own charge. -/
theorem loopBound_succ (count size chunk : Nat) :
    loopBound (count + 1) size chunk = guardCost.val + (bodyCost (size + chunk)).val +
      loopBound count (size + chunk) chunk + 10 := by
  unfold loopBound
  rw [Finset.sum_range_succ']
  have shifted : (∑ index ∈ Finset.range count,
      (guardCost.val + (bodyCost (size + (index + 1 + 1) * chunk)).val + 10)) =
      ∑ index ∈ Finset.range count,
        (guardCost.val + (bodyCost (size + chunk + (index + 1) * chunk)).val + 10) := by
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun size => guardCost.val + (bodyCost size).val + 10) (by ring)
  rw [shifted]
  have first : (bodyCost (size + (0 + 1) * chunk)).val = (bodyCost (size + chunk)).val :=
    congrArg (fun size => (bodyCost size).val) (by omega)
  rw [first]
  omega

/-- Reuse the existing mathematical round contracts at every actual intermediate
heap. No resource invariant beyond their array observations is needed here. -/
theorem loop_costBound (w heapLimit : Nat) (model : Model) (entry : State _)
    (related : modelRel model (View entry.locals) entry.heap) :
    StmtArenaCostBound ArrayRangeNative.Source.program w heapLimit 2 Code entry
      (loopBound (model_remaining model) (model_state model).values.size (model_chunk model).size) := by
  change StmtArenaCostBound _ _ _ _ _ ⟨entry.locals, entry.heap⟩ _
  rw [← Equiv.symm_apply_apply View entry.locals]
  refine StmtArenaCostBound.while_model View ArrayRangeNative.Source.program Guard Body
    modelRel modelGuard modelStep guard_model (fun current _ => body_model current)
    (fun _ => True) (fun _ _ _ => trivial)
    (fun _ => guardCost.val)
    (fun current => (bodyCost ((model_state current).values.size + (model_chunk current).size)).val)
    (fun current => loopBound (model_remaining current)
      (model_state current).values.size (model_chunk current).size)
    ?_ ?_ ?_ ?_ trivial related
  · intro current actual currentHeap _ _
    exact guardCost.property w heapLimit ⟨View.symm actual, currentHeap⟩
  · intro current actual currentHeap _ _ observed
    exact (bodyCost _).property w heapLimit current actual currentHeap rfl observed
  · intro current _ stopped
    change decide (0 < model_remaining current) = false at stopped
    have empty : model_remaining current = 0 := Nat.eq_zero_of_not_pos (of_decide_eq_false stopped)
    simp only [empty, loopBound, Finset.sum_range_zero, Nat.add_zero, le_refl]
  · intro current _ active
    change decide (0 < model_remaining current) = true at active
    have positive : 0 < model_remaining current := of_decide_eq_true active
    change guardCost.val + (bodyCost ((model_state current).values.size +
        (model_chunk current).size)).val +
      loopBound (model_remaining current - 1)
        ((model_state current).values.append (model_chunk current)).size (model_chunk current).size +
        10 ≤ loopBound (model_remaining current)
          (model_state current).values.size (model_chunk current).size
    have sizeStep : ((model_state current).values.append (model_chunk current)).size =
        (model_state current).values.size + (model_chunk current).size := Array.size_append
    rw [sizeStep, ← loopBound_succ, Nat.sub_add_cancel positive]

/-- Infer the unchanged function's statement envelope using only count and
input lengths, before introducing handles, payloads, word width or heap limit. -/
def functionCost (count size chunkSize : Nat) : { bound : Nat //
    ∀ w heapLimit (chunkValues : Array Nat) (initialValue : Payload)
      (chunk : Buffer .nat) (initial : Buffer .nat × Nat) (heap : Heap),
      initialValue.values.size = size → chunkValues.size = chunkSize →
      chunk.Contents heap chunkValues → state_representation.Rel initialValue initial heap →
      StmtArenaCostBound ArrayRangeNative.Source.program w heapLimit 2
        (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
        ⟨ArrayRangeNative.Source.repeatAppend_args count chunk initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit chunkValues initialValue chunk initial heap initialSize chunkSizeEq
    chunkObserved initialObserved
  ram_source_arena_cost
  apply StmtArenaCostBound.mono
  · apply loop_costBound w heapLimit
      (mkModel (remaining := count) (state := initialValue) (initial := initialValue)
        (chunk := chunkValues) (count := count))
    ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1
    simp_all [modelRel, mkModel, state_representation]
  · simp only [mkModel, model_remaining, model_state, model_chunk, initialSize, chunkSizeEq]
    exact Nat.le_refl _⟩

/-- The callable function adds its existing initialization charge exactly once. -/
def functionBodyBound (count size chunk : Nat) : Nat :=
  (functionCost count size chunk).val + 2

/-- Bound the same callable function under its original array/record observations,
without imposing disjointness, termination budgets or capacity assumptions. -/
theorem function_costBound (count : Nat) (chunkValues : Array Nat) (initialValue : Payload)
    (w heapLimit : Nat) :
    FunctionArenaCostBound ArrayRangeNative.Source.program
      (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
      (fun input : Buffer .nat × (Buffer .nat × Nat) =>
        ArrayRangeNative.Source.repeatAppend_args count input.1 input.2)
      (fun input heap => input.1.Contents heap chunkValues ∧
        state_representation.Rel initialValue input.2 heap)
      w heapLimit 2
      (fun _ => functionBodyBound count initialValue.values.size chunkValues.size) := by
  apply FunctionArenaCostBound.of_stmt
  intro input heap observed
  exact (functionCost _ _ _).property w heapLimit chunkValues initialValue input.1 input.2
    heap rfl rfl observed.1 observed.2

/-- All iteration-dependent work is the finite sum; the remaining caller work
is exactly its zero-iteration envelope. -/
theorem functionBodyBound_eq (count size chunk : Nat) :
    functionBodyBound count size chunk = functionBodyBound 0 0 0 +
      ∑ index ∈ Finset.range count,
        (guardCost.val + (bodyCost (size + (index + 1) * chunk)).val + 10) := by
  simp only [functionBodyBound, functionCost, loopBound, Finset.sum_range_zero, Nat.add_zero]
  omega

/-- An all-input polynomial bound obtained by bounding each actual round's size
by the final array size. Compiler-derived coefficients remain explicit. -/
theorem functionBodyBound_le (count size chunk : Nat) :
    functionBodyBound count size chunk ≤ functionBodyBound 0 0 0 + count *
      (guardCost.val + (bodyCost 0).val + 10 +
        (14 + BufferCopy.copyIntoGuardCost.val + BufferCopy.copyIntoBodyCost.val + 10) *
          (size + count * chunk)) := by
  rw [functionBodyBound_eq]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _index ∈ Finset.range count,
        (guardCost.val + (bodyCost 0).val + 10 +
          (14 + BufferCopy.copyIntoGuardCost.val + BufferCopy.copyIntoBodyCost.val + 10) *
            (size + count * chunk)) := by
      apply Finset.sum_le_sum
      intro index inside
      have next : index + 1 ≤ count := Finset.mem_range.mp inside
      have growing := Nat.mul_le_mul_left
        (14 + BufferCopy.copyIntoGuardCost.val + BufferCopy.copyIntoBodyCost.val + 10)
        (Nat.add_le_add_left (Nat.mul_le_mul_right chunk next) size)
      rw [bodyCost_eq]
      omega
    _ = _ := by simp

/-- The same three-parameter envelope has mathlib's asymptotic growth bound.
The proof uses an all-input inequality, not constraints on relative input sizes. -/
theorem isBigO_functionBodyBound :
    Asymptotics.IsBigO Filter.atTop
      (fun input : Nat × Nat × Nat =>
        (functionBodyBound input.1 input.2.1 input.2.2 : ℝ))
      (fun input : Nat × Nat × Nat =>
        ((1 + input.1 * (1 + input.2.1 + input.1 * input.2.2) : Nat) : ℝ)) := by
  let slope := 14 + BufferCopy.copyIntoGuardCost.val + BufferCopy.copyIntoBodyCost.val + 10
  let base := guardCost.val + (bodyCost 0).val + 10
  let coefficient := functionBodyBound 0 0 0 + base + slope
  apply Asymptotics.IsBigO.of_bound (coefficient : ℝ)
  apply Filter.Eventually.of_forall
  rintro ⟨count, size, chunk⟩
  have zeroLe : functionBodyBound 0 0 0 ≤ coefficient := by omega
  have baseLe : base ≤ coefficient := by omega
  have slopeLe : slope ≤ coefficient := by omega
  have roundLe : base + slope * (size + count * chunk) ≤
      coefficient * (1 + size + count * chunk) := by
    calc
      _ ≤ coefficient + coefficient * (size + count * chunk) :=
        Nat.add_le_add baseLe (Nat.mul_le_mul_right _ slopeLe)
      _ = _ := by ring
  have bounded : functionBodyBound count size chunk ≤
      coefficient * (1 + count * (1 + size + count * chunk)) := by
    calc
      _ ≤ functionBodyBound 0 0 0 + count * (base + slope * (size + count * chunk)) :=
        functionBodyBound_le count size chunk
      _ ≤ coefficient + count * (coefficient * (1 + size + count * chunk)) :=
        Nat.add_le_add zeroLe (Nat.mul_le_mul_left count roundLe)
      _ = _ := by ring
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr bounded : (functionBodyBound count size chunk : ℝ) ≤
      ((coefficient * (1 + count * (1 + size + count * chunk)) : Nat) : ℝ))

end Complexity.Language.Examples.LinkedList.NativeRange.RepeatAppendCost
