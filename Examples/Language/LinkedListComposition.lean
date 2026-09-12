/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedListFoldAllocation
import Examples.Language.LinkedListCompiled
import Mathlib.Tactic.Ring

/-!
# Traversing a newly allocated native list

The existing `NativeLists.reverseSum` first allocates an actual reversed list,
then traverses that returned list with the existing addition callback. Source
correctness transports the mathematical List observation across the first call;
the same observation selects the second call's length-dependent cost certificate.
No decoder, second implementation or per-consumer register proof is introduced.

The final RAM theorem retains the same actual heap and allocation cursor. The
original list remains observable. A final-sum range supplies all addition ranges;
the additional arena allowance is three words per original element.
-/

namespace Complexity.Language.Examples.LinkedList

open Ram.LanguageCompiler

/-- The shared fold envelope uses the original addition callback's proved cost.
Call-frame and traversal coefficients belong to the library, not this consumer. -/
def sumFoldBound (length : Nat) : Nat :=
  List.Fold.linearFunctionBound (accTy := .nat) (kind := .nat)
    Reducer.program Reducer.addId rfl 10 length

/-- Select the actual sum-fold certificate at its mathematical input length.
The callback's ordinary range domain is retained, separately from correctness. -/
theorem sumFold_costBound (w heapLimit length : Nat) :
    FunctionArenaCostBound NativeLists.Operations.fold1.program
      (NativeLists.Operations.fold1.program.body NativeLists.Operations.fold1.foldId)
      List.Fold.functionArgs
      (fun input heap =>
        List.Fold.functionCostPre (kind := .nat) Representation.nat Nat.add
          (fun accumulator head => accumulator + head < 2 ^ w) input heap ∧
        input.2.1.length = length)
      w heapLimit 4 (fun _ => sumFoldBound length) := by
  intro input heap allowed finish value execution cursor finalCursor ready steps cost
  have bounded := List.Fold.functionCostBound_of_actual (add_fold_contract w)
    (add_fold_costBound_at_depth w heapLimit 3)
    input heap allowed.1 finish value execution ready cost
  dsimp only at bounded
  rw [List.Fold.functionBound_const, allowed.2] at bounded
  exact bounded

/-- Infer both actual calls' costs, carrying the first call's source
postcondition to the new list's cost proof. The source declaration itself and
its mathematical correctness theorem remain unchanged. -/
def reverseSumCost (length : Nat) : { bound : Nat //
    ∀ w heapLimit (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap),
      values.length = length → (Representation.list .nat).Rel values root heap →
      values.sum < 2 ^ w →
      StmtArenaCostBound NativeLists.Source.program w heapLimit 5
        (NativeLists.Source.program.body NativeLists.Source.reverseSumId)
        ⟨NativeLists.Source.reverseSum_args root, heap⟩ bound } :=
  ⟨_, by
    intro w heapLimit values root heap lengthEq observed fits
    have reverseInput : values.length = length ∧
        (Representation.list .nat).Rel values root heap := ⟨lengthEq, observed⟩
    have reversedFits : 0 + (NativeLists.reverse values).sum < 2 ^ w := by
      simpa only [reverse_eq, List.sum_reverse, Nat.zero_add] using fits
    have reversedLength : (NativeLists.reverse values).length = length := by
      simpa only [reverse_eq, List.length_reverse] using lengthEq
    have sumInput : ∀ actualRoot currentHeap,
        (Representation.list .nat).Rel (NativeLists.reverse values) actualRoot currentHeap →
        List.Fold.functionCostPre (kind := .nat) Representation.nat Nat.add
          (fun accumulator head => accumulator + head < 2 ^ w)
          (0, NativeLists.reverse values, 0, actualRoot) currentHeap ∧
        (NativeLists.reverse values).length = length := by
      intro actualRoot currentHeap contents
      exact ⟨⟨sum_admissible 0 _ reversedFits, rfl, contents⟩, reversedLength⟩
    ram_source_arena_cost [
      (reverse_costBound w heapLimit length) at (values, root)
        using (NativeLists.reverse_refines values trivial),
      (sumFold_costBound w heapLimit length) at (0, NativeLists.reverse values, 0, _)
        via NativeLists.Source.imports.NativeLists.Operations.fold1.embedding]
    all_goals (apply sumInput; assumption)⟩

/-- The inferred body envelope adds the actual outer invocation and final halt
once. Both inner traversals and their callbacks are already included. -/
def reverseSumInvocationBound (length : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeLists.Source.program)
    (lowerFunc NativeLists.Source.program NativeLists.Source.reverseSumId)
    ((reverseSumCost length).val + 2) + 1

/-- The inferred complete invocation bound is affine in length. This identity
states that fact without introducing another set of compiler coefficients. -/
theorem reverseSumInvocationBound_affine (length : Nat) :
    reverseSumInvocationBound length + length * reverseSumInvocationBound 0 =
      length * reverseSumInvocationBound 1 + reverseSumInvocationBound 0 := by
  simp only [reverseSumInvocationBound, reverseSumCost, reverseCost,
    reverseAppendBodyBound, reverseAppendCost, reverseAppendFoldBound, sumFoldBound,
    List.Fold.linearFunctionBound, callCost, Ram.LocalCompiler.Function.callSteps_eq,
    Nat.zero_mul, Nat.one_mul]
  ring

/-- The proved whole-invocation envelope is linear in the input length,
using mathlib's ordinary `IsBigO`, not a separate complexity predicate. -/
theorem isBigO_reverseSumInvocationBound :
    Asymptotics.IsBigO Filter.atTop
      (fun length => (reverseSumInvocationBound length : ℝ))
      (fun length : Nat => (length : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound
    ((reverseSumInvocationBound 1 + reverseSumInvocationBound 0 : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with length positive
  have fixed : reverseSumInvocationBound 0 ≤ length * reverseSumInvocationBound 0 := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (reverseSumInvocationBound 0) positive
  have bound : reverseSumInvocationBound length ≤
      (reverseSumInvocationBound 1 + reverseSumInvocationBound 0) * length := by
    calc
      _ ≤ length * reverseSumInvocationBound 1 + reverseSumInvocationBound 0 := by
        have affine := reverseSumInvocationBound_affine length
        omega
      _ ≤ length * reverseSumInvocationBound 1 + length * reverseSumInvocationBound 0 :=
        Nat.add_le_add_left fixed _
      _ = _ := by ring
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr bound : (reverseSumInvocationBound length : ℝ) ≤
      (((reverseSumInvocationBound 1 + reverseSumInvocationBound 0) * length : Nat) : ℝ))

/-- Compose existing measured calls at their actual returned heap and cursor.
The independent reverse specification supplies the List observed by the fold. -/
theorem reverseSum_measured {w heapLimit cursor : Nat}
    (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap)
    (positive : 0 < w) (observed : (Representation.list .nat).Rel values root heap)
    (fits : values.sum < 2 ^ w) (space : cursor + 3 * values.length ≤ heapLimit) :
    ArenaMeasured NativeLists.Source.program w heapLimit 5
      (NativeLists.Source.program.body NativeLists.Source.reverseSumId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor ≤ cursor + 3 * values.length)
      ⟨NativeLists.Source.reverseSum_args root, heap⟩ cursor := by
  have ranges := sum_ranges 0 values (by simpa only [Nat.zero_add] using fits)
  have reversed := (reverse_measured values root heap positive observed ranges.2 space).with_spec
    (NativeLists.reverse_refines values trivial) observed
  ram_source_arena_call measured using reversed
  rename_i reverseFinish reversed reverseCursor reverseSteps reverseProperty reverseFits
  have reverseCursorBound := reverseProperty.1
  have reversedObserved : (Representation.list .nat).Rel (NativeLists.reverse values)
      reversed reverseFinish.heap := reverseProperty.2
  have reversedFits : 0 + (NativeLists.reverse values).sum < 2 ^ w := by
    simpa only [reverse_eq, List.sum_reverse, Nat.zero_add] using fits
  have reversedRanges := sum_ranges 0 (NativeLists.reverse values) reversedFits
  have folded := List.Fold.arenaMeasured (add_fold_contract w)
    (add_fold_resources_at_depth w heapLimit 3) (add_fold_costBound_at_depth w heapLimit 3)
    0 (NativeLists.reverse values) 0 reversed reverseFinish.heap reverseCursor positive
    (sum_admissible 0 _ reversedFits) rfl reversedRanges.1 reversedRanges.2
    (by simp only [List.Fold.accumulated_const, Nat.mul_zero, Nat.add_zero]; omega)
    reversedObserved
  ram_source_arena_call measured using folded
    via NativeLists.Source.imports.NativeLists.Operations.fold1.embedding
  rename_i finalFinish finalValue finalCursor finalSteps foldProperty finalFits
  have cursorBound := foldProperty.2
  simp only [List.Fold.accumulated_const, Nat.mul_zero, Nat.add_zero] at cursorBound
  exact ⟨_, rfl, by omega⟩

/-- Compose the actual allocating reverse with the scalar fold at its actual
returned heap and cursor. The second traversal reserves no additional words. -/
theorem reverseSum_ready_cost {w heapLimit cursor : Nat}
    (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap)
    (positive : 0 < w) (observed : (Representation.list .nat).Rel values root heap)
    (fits : values.sum < 2 ^ w) (space : cursor + 3 * values.length ≤ heapLimit) :
    ∃ finish value finalCursor steps,
      ∃ execution : Exec NativeLists.Source.program
          (NativeLists.Source.program.body NativeLists.Source.reverseSumId)
          ⟨NativeLists.Source.reverseSum_args root, heap⟩ finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit 5 cursor finalCursor,
          ArenaExecutionCost ready steps ∧ steps ≤ (reverseSumCost values.length).val ∧
          finalCursor ≤ cursor + 3 * values.length := by
  exact (reverseSum_measured values root heap positive observed fits space).exists_returned_le
    ((reverseSumCost values.length).property w heapLimit values root heap rfl observed fits)

/-- The native allocation-then-traversal program halts on RAM with `values.sum`.
The original List remains observable in the same final heap. The instruction
bound covers both traversals, initialization, calls, returns and halt; input
loading is excluded. The cursor bound concerns cumulative fresh allocation,
not exact peak live storage or reclamation. -/
theorem reverseSum_execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (values : List Nat) (root : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    (fits : values.sum < 2 ^ w) {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeLists.Source.program NativeLists.Source.reverseSumId
      5 heapLimit placement (NativeLists.Source.reverseSum_args root) heap cursor entry)
    (space : cursor + 3 * values.length ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeLists.Source.program NativeLists.Source.reverseSumId
        5 heapLimit placement (NativeLists.Source.reverseSum_args root) heap entry,
      outcome.value = values.sum ∧ (Representation.list .nat).Rel values root outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧ outcome.cursor ≤ cursor + 3 * values.length ∧
      outcome.bodySteps ≤ (reverseSumCost values.length).val + 2 ∧
      outcome.result.steps ≤ reverseSumInvocationBound values.length := by
  have measured := reverseSum_measured values root heap launch.positive observed fits space
  obtain ⟨outcome, cursorBound, represented, shape, bodyBound, stepsBound⟩ :=
    measured.execute_le (P := fun _ _ finalCursor => finalCursor ≤ cursor + 3 * values.length)
      ((reverseSumCost values.length).property w heapLimit values root heap rfl observed fits)
      (NativeLists.reverseSum_refines values trivial) launch observed
  have result : outcome.value = values.sum := by
    change NativeLists.reverseSum values = outcome.value at represented
    simpa only [reverseSum_eq] using represented.symm
  exact ⟨outcome, result, Representation.list_mono observed shape, shape, cursorBound,
    bodyBound, stepsBound⟩

end Complexity.Language.Examples.LinkedList
