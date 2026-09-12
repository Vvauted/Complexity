/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedListAllocation
import Complexity.Computability.Ram.Compiler.Language.List.IsEmpty
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.FunctionExecution

/-!
# Scalar and compound native branch results on RAM

The ordinary `headOr` and `inspectOrPrepend` declarations retain their generated
source correctness. Their resource proofs use the actual Uncons and constructor
executions, including selected-branch allocation and initialized result slots.
Structural bounds are inferred from these bodies and supplied callee contracts.

The shared publication rule connects the independent mathematical result and
resource proofs to one halted invocation. Input loading is outside the count;
finite word, code, stack and arena conditions remain those of the actual launch.
-/

namespace Complexity.Language.Examples.LinkedList

open Ram.LanguageCompiler

/-- Native emptiness uses the actual root-tag call, with a bound inferred from
its supplied certificate and the generated caller's return instructions. -/
def isEmptyCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeViews.Source.program w heapLimit 1
      (NativeViews.Source.program.body NativeViews.Source.isEmptyId) initial bound } := by
  ram_source_arena_cost [
    (Ram.LanguageCompiler.List.IsEmpty.arenaCostBound .nat _ _ _)
      via NativeViews.Source.imports.NativeViews.Operations.isEmptyNat.embedding]

/-- Complete native invocation accounting, including initialization, call and halt. -/
def isEmptySteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeViews.Source.program)
    (lowerFunc NativeViews.Source.program NativeViews.Source.isEmptyId)
    (isEmptyCost.val + 2) + 1

/-- The native wrapper reuses the tag test's actual execution at any heap and
cursor. No node is read, so readiness needs neither head ranges nor a heap
representation; complete RAM invocation retains its usual launch conditions. -/
theorem isEmpty_measured {w heapLimit cursor : Nat}
    (root : Option (NodeRef .nat)) (heap : Heap) (positive : 0 < w) :
    ArenaMeasured NativeViews.Source.program w heapLimit 1
      (NativeViews.Source.program.body NativeViews.Source.isEmptyId)
      (fun finish control finalCursor _ =>
        ∃ value, control = .returned value ∧ finish.heap = heap ∧ finalCursor = cursor)
      ⟨NativeViews.Source.isEmpty_args root, heap⟩ cursor := by
  have checked := Ram.LanguageCompiler.List.IsEmpty.arenaMeasured .nat root heap
    (heapLimit := heapLimit) (depth := 0) (cursor := cursor) positive
  ram_source_arena_call measured using checked
    via NativeViews.Source.imports.NativeViews.Operations.isEmptyNat.embedding
  refine ⟨_, rfl, ?_⟩
  ram_source_arena_step

/-- Ordinary native List emptiness and its constant instruction bound hold for
the same halted RAM call. The heap and cursor stay unchanged, and input loading
is outside the count. Source correctness has no resource premise. -/
theorem isEmpty_execute_le {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (values : List Nat) (root : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeViews.Source.program
      NativeViews.Source.isEmptyId 1 heapLimit placement
      (NativeViews.Source.isEmpty_args root) heap cursor entry) :
    ∃ outcome : FunctionArenaExecution NativeViews.Source.program
        NativeViews.Source.isEmptyId 1 heapLimit placement
        (NativeViews.Source.isEmpty_args root) heap entry,
      outcome.value = values.isEmpty ∧ outcome.heap = heap ∧ outcome.cursor = cursor ∧
      outcome.bodySteps ≤ isEmptyCost.val + 2 ∧ outcome.result.steps ≤ isEmptySteps := by
  obtain ⟨outcome, ⟨heapEq, cursorEq⟩, ⟨answer, represented, answerEq⟩,
      _shape, bodyBound, stepsBound⟩ :=
    (isEmpty_measured root heap launch.positive).execute_le
      (P := fun finalHeap _ finalCursor => finalHeap = heap ∧ finalCursor = cursor)
      (isEmptyCost.property w heapLimit _) (nativeIsEmpty_correct values trivial)
      launch observed
  change answer = outcome.value at represented
  exact ⟨outcome, represented.symm.trans answerEq, heapEq, cursorEq, bodyBound, stepsBound⟩

/-- Scalar head selection has a uniform bound inferred from the real node read
and generated branch, assignment and return instructions. -/
def headOrCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeViews.Source.program w heapLimit 1
      (NativeViews.Source.program.body NativeViews.Source.headOrId) initial bound } := by
  ram_source_arena_cost [
    (Ram.LanguageCompiler.List.Uncons.arenaCostBound .nat _ _ _)
      via NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding]

/-- Complete preloaded invocation bound, including initialization, call and halt. -/
def headOrSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeViews.Source.program)
    (lowerFunc NativeViews.Source.program NativeViews.Source.headOrId)
    (headOrCost.val + 2) + 1

/-- An ordinary scalar List match returns the mathematical head or fallback on
RAM, without changing the heap or allocation cursor. Its complete instruction
bound is independent of List length. -/
theorem headOr_execute_le {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (fallback : Nat) (values : List Nat) (root : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeViews.Source.program
      NativeViews.Source.headOrId 1 heapLimit placement
      (NativeViews.Source.headOr_args fallback root) heap cursor entry) :
    ∃ outcome : FunctionArenaExecution NativeViews.Source.program
        NativeViews.Source.headOrId 1 heapLimit placement
        (NativeViews.Source.headOr_args fallback root) heap entry,
      outcome.value = values.head?.getD fallback ∧
      outcome.heap = heap ∧ outcome.cursor = cursor ∧
      outcome.bodySteps ≤ headOrCost.val + 2 ∧ outcome.result.steps ≤ headOrSteps := by
  have positive : 0 < w := launch.positive
  have fallbackFits : fallback < 2 ^ w := launch.arguments .here
  obtain ⟨readFinish, parts, readSteps, readExecution, readReady, readCost,
      _readStepsLe, readHeapEq, _partsObserved⟩ :=
    Ram.LanguageCompiler.List.Uncons.ready_cost .nat values root heap
      (depth := 0) (cursor := cursor) positive launch.arena.heapRep observed
  have measured : ArenaMeasured NativeViews.Source.program w heapLimit 1
      (NativeViews.Source.program.body NativeViews.Source.headOrId)
      (fun finish control finalCursor _ =>
        ∃ value, control = .returned value ∧ finish.heap = heap ∧ finalCursor = cursor)
      ⟨NativeViews.Source.headOr_args fallback root, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using readCost via
      NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding
    all_goals exact ⟨_, rfl, readHeapEq⟩
  obtain ⟨outcome, ⟨heapEq, cursorEq⟩, ⟨answer, represented, answerEq⟩,
      _shape, bodyBound, stepsBound⟩ :=
    measured.execute_le (P := fun finalHeap _ finalCursor =>
      finalHeap = heap ∧ finalCursor = cursor) (headOrCost.property w heapLimit _)
      (headOr_correct (fallback, values) trivial) launch ⟨rfl, observed⟩
  change answer = outcome.value at represented
  exact ⟨outcome, represented.symm.trans answerEq, heapEq, cursorEq, bodyBound, stepsBound⟩

/-- The two-call helper's bound is inferred without reopening either callee. -/
def inspectAndPrependCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeViews.Source.program w heapLimit 2
      (NativeViews.Source.program.body NativeViews.Source.inspectAndPrependId) initial bound } := by
  ram_source_arena_cost [
    (Ram.LanguageCompiler.List.Uncons.arenaCostBound .nat _ _ _)
      via NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding,
    (prepend_arenaCostBound _ _)
      via NativeViews.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding]

/-- A caller can reuse the helper's uniform certificate, including initialization. -/
theorem inspectAndPrepend_arenaCostBound (w heapLimit : Nat) :
    FunctionArenaCostBound NativeViews.Source.program
      (NativeViews.Source.program.body NativeViews.Source.inspectAndPrependId)
      id (fun _ _ => True) w heapLimit 2 (fun _ => inspectAndPrependCost.val + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap _
  exact inspectAndPrependCost.property w heapLimit _

/-- Reading and prepending share the actual intermediate heap. Three fresh words
are sufficient, and the witness retains the actual compound returned value. -/
theorem inspectAndPrepend_ready_cost {w heapLimit cursor : Nat}
    (head : Nat) (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap)
    {placement : Nat → Ram.Word w} {entry : Ram.Source.State w}
    (positive : 0 < w) (headFits : head < 2 ^ w)
    (memory : HeapRep placement heapLimit heap entry)
    (observed : (Representation.list .nat).Rel values root heap)
    (space : cursor + 3 ≤ heapLimit) :
    ∃ finish value steps,
      ∃ execution : Exec NativeViews.Source.program
        (NativeViews.Source.program.body NativeViews.Source.inspectAndPrependId)
        ⟨NativeViews.Source.inspectAndPrepend_args head root, heap⟩ finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit 2 cursor (cursor + 3),
          ArenaExecutionCost ready steps := by
  obtain ⟨readFinish, parts, readSteps, readExecution, readReady, readCost,
      _readStepsLe, _readHeapEq, _partsObserved⟩ :=
    Ram.LanguageCompiler.List.Uncons.ready_cost .nat values root heap
      (depth := 1) (cursor := cursor) positive memory observed
  obtain ⟨_, _, prependCost⟩ :=
    prepend_ready_cost head root readFinish.heap positive headFits space
  have measured : ArenaMeasured NativeViews.Source.program w heapLimit 2
      (NativeViews.Source.program.body NativeViews.Source.inspectAndPrependId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor = cursor + 3)
      ⟨NativeViews.Source.inspectAndPrepend_args head root, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using readCost via
      NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding
    ram_source_arena_call exact using prependCost via
      NativeViews.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
    exact ⟨_, rfl⟩
  obtain ⟨finish, value, _, steps, execution, ready, cost, rfl⟩ :=
    ArenaMeasured.exists_returned_iff.mp measured
  exact ⟨finish, value, steps, execution, ready, cost⟩

/-- The compound join's bound includes real initialization of all result fields,
and uses the selected branch maximum instead of charging both branch executions. -/
def inspectOrPrependCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeViews.Source.program w heapLimit 3
      (NativeViews.Source.program.body NativeViews.Source.inspectOrPrependId) initial bound } := by
  ram_source_arena_cost [(inspectAndPrepend_arenaCostBound _ _)]

/-- Full preloaded invocation bound of the compound conditional. -/
def inspectOrPrependSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeViews.Source.program)
    (lowerFunc NativeViews.Source.program NativeViews.Source.inspectOrPrependId)
    (inspectOrPrependCost.val + 2) + 1

/-- A conditional returns an optional head/tail together with a List, through
the actual RAM runner. Only its true path allocates; both retain every old List
observation. Correctness, cursor growth and instruction bounds concern the same
invocation, including compound-slot initialization and field copies. -/
theorem inspectOrPrepend_execute_le {w heapLimit cursor : Nat}
    {placement : Nat → Ram.Word w} (flag : Bool) (head : Nat)
    (values : List Nat) (root : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeViews.Source.program
      NativeViews.Source.inspectOrPrependId 3 heapLimit placement
      (NativeViews.Source.inspectOrPrepend_args flag head root) heap cursor entry)
    (space : cursor + (if flag then 3 else 0) ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeViews.Source.program
        NativeViews.Source.inspectOrPrependId 3 heapLimit placement
        (NativeViews.Source.inspectOrPrepend_args flag head root) heap entry,
      ((Representation.nat.prod (Representation.list .nat)).option.prod
        (Representation.list .nat)).Rel
        (if flag then (values.head?.map (fun value => (value, values.tail)), head :: values)
          else (none, values)) outcome.value outcome.heap ∧
      (Representation.list .nat).Rel values root outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + (if flag then 3 else 0) ∧
      outcome.bodySteps ≤ inspectOrPrependCost.val + 2 ∧
      outcome.result.steps ≤ inspectOrPrependSteps := by
  have positive : 0 < w := launch.positive
  have headFits : head < 2 ^ w := launch.arguments (.there .here)
  have measured : ArenaMeasured NativeViews.Source.program w heapLimit 3
      (NativeViews.Source.program.body NativeViews.Source.inspectOrPrependId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧
          finalCursor = cursor + (if flag then 3 else 0))
      ⟨NativeViews.Source.inspectOrPrepend_args flag head root, heap⟩ cursor := by
    cases flag with
    | false =>
        ram_source_arena_step
        exact ⟨_, rfl, rfl⟩
    | true =>
        obtain ⟨_, _, _, _, _, inspectionCost⟩ :=
          inspectAndPrepend_ready_cost head values root heap positive headFits
            launch.arena.heapRep observed space
        ram_source_arena_step
        ram_source_arena_call exact using inspectionCost
        exact ⟨_, rfl, rfl⟩
  obtain ⟨outcome, cursorEq, ⟨_, result, rfl⟩, shape, bodyBound, stepsBound⟩ :=
    measured.execute_le (P := fun _ _ finalCursor =>
      finalCursor = cursor + (if flag then 3 else 0))
      (inspectOrPrependCost.property w heapLimit _)
      (inspectOrPrepend_correct (flag, head, values) trivial) launch ⟨rfl, rfl, observed⟩
  exact ⟨outcome, result, Representation.list_mono observed shape, shape,
    cursorEq, bodyBound, stepsBound⟩

end Complexity.Language.Examples.LinkedList
