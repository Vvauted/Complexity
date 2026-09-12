/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedList
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.List.Uncons
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.FunctionExecution

/-!
# Executing a native linked-list constructor on RAM

This is the actual generated `NativeConstruction.Source.prepend` wrapper, not
the imported constructor considered in isolation. Its ordinary source refinement
supplies `head :: values`; the shared constructor-call rule supplies readiness
and the exact count for the same execution. The invocation includes both call
levels, initialization, the wrapper return and the final halt.

The returned execution retains the actual extended heap and updated cursor.
The original tail remains available in that same heap, including when it is
shared by other roots. No disjointness or suffix copying is required.
-/

namespace Complexity.Language.Examples.LinkedList

open Ram.LanguageCompiler

/-- Infer the straight-line wrapper's bound from its actual body and the
constructor certificate. The measured theorem below establishes the exact count. -/
def prependCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeConstruction.Source.program w heapLimit 1
      (NativeConstruction.Source.program.body NativeConstruction.Source.prependId) initial bound } := by
  ram_source_arena_cost [(Ram.LanguageCompiler.List.Cons.arenaCostBound .nat _ _ 0)
    via NativeConstruction.Source.imports.NativeConstruction.Operations.consNat.embedding]

/-- The actual imported constructor call and the wrapper's own return. -/
def prependBodySteps : Nat := prependCost.val

/-- Full instruction count for the generated wrapper, including its outer
invocation, private-flag initialization and final halt exactly once. -/
def prependSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeConstruction.Source.program)
    (lowerFunc NativeConstruction.Source.program NativeConstruction.Source.prependId)
    (prependBodySteps + 2) + 1

/-- The wrapper's uniform cost follows from the actual constructor certificate
and its own generated statements, independently of readiness or termination. -/
theorem prepend_arenaCostBound (w heapLimit : Nat) :
    FunctionArenaCostBound NativeConstruction.Source.program
      (NativeConstruction.Source.program.body NativeConstruction.Source.prependId)
      id (fun _ _ => True) w heapLimit 1 (fun _ => prependBodySteps + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap _
  exact prependCost.property w heapLimit ⟨args, heap⟩

/-- The generated constructor body exposes its exact allocation and instruction
count in ordinary arguments, so later callers reuse it at their current heap
and cursor without opening the imported constructor again. -/
theorem prepend_ready_cost {w heapLimit cursor : Nat}
    (head : Nat) (tail : Option (NodeRef .nat)) (heap : Heap)
    (positive : 0 < w) (headFits : head < 2 ^ w)
    (space : cursor + 3 ≤ heapLimit) :
    ∃ execution : Exec NativeConstruction.Source.program
        (NativeConstruction.Source.program.body NativeConstruction.Source.prependId)
        ⟨NativeConstruction.Source.prepend_args head tail, heap⟩
        ⟨NativeConstruction.Source.prepend_args head tail, (heap.cons head tail).2⟩
        (.returned (some (heap.cons head tail).1)),
      ∃ ready : ArenaReady execution w heapLimit 1 cursor (cursor + 3),
        ArenaExecutionCost ready prependBodySteps := by
  obtain ⟨originalReady, originalCost⟩ :=
    Ram.LanguageCompiler.List.Cons.ready_cost .nat head tail heap
      (depth := 0) positive headFits space
  have measured : ArenaMeasured NativeConstruction.Source.program w heapLimit 1
      (NativeConstruction.Source.program.body NativeConstruction.Source.prependId)
      (fun finish control finalCursor steps =>
        finish = ⟨NativeConstruction.Source.prepend_args head tail, (heap.cons head tail).2⟩ ∧
          control = .returned (some (heap.cons head tail).1) ∧ finalCursor = cursor + 3 ∧
            steps = prependBodySteps)
      ⟨NativeConstruction.Source.prepend_args head tail, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using originalCost via
      NativeConstruction.Source.imports.NativeConstruction.Operations.consNat.embedding
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost,
      rfl, rfl, rfl, rfl⟩ := measured
  exact ⟨execution, ready, cost⟩

/-- The ordinary native constructor halts in one real allocating RAM invocation.
The source refinement is independent of resources; the launch supplies the
existing finite-word, rootedness and code/stack conditions. Only three additional
arena words are needed, regardless of the represented tail's length. -/
theorem prepend_execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (head : Nat) (values : List Nat) (tail : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values tail heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeConstruction.Source.program
      NativeConstruction.Source.prependId 1 heapLimit placement
      (NativeConstruction.Source.prepend_args head tail) heap cursor entry)
    (space : cursor + 3 ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeConstruction.Source.program
        NativeConstruction.Source.prependId 1 heapLimit placement
        (NativeConstruction.Source.prepend_args head tail) heap entry,
      (Representation.list .nat).Rel (head :: values) outcome.value outcome.heap ∧
      outcome.heap = (heap.cons head tail).2 ∧
      outcome.value = some (heap.cons head tail).1 ∧
      (Representation.list .nat).Rel values tail outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + 3 ∧
      outcome.bodySteps = prependBodySteps + 2 ∧
      outcome.result.steps = prependSteps := by
  obtain ⟨execution, ready, cost⟩ :=
    prepend_ready_cost head tail heap launch.positive (launch.arguments .here) space
  obtain ⟨outcome, valueEq, heapEq, cursorEq, bodyEq⟩ :=
    cost.execute (fn := NativeConstruction.Source.prependId) launch
  have represented := outcome.post
    (NativeConstruction.prepend_refines (head, values) trivial) ⟨rfl, observed⟩
  have result : (Representation.list .nat).Rel (head :: values)
      outcome.value outcome.heap := by
    change (Representation.list .nat).Rel (NativeConstruction.prepend head values)
      outcome.value outcome.heap at represented
    simpa only [prepend_eq] using represented
  have allocated : outcome.heap = (heap.cons head tail).2 := heapEq
  have tailRetained : (Representation.list .nat).Rel values tail outcome.heap := by
    rw [allocated]
    exact observed.node_alloc head tail
  have shape : heap.ShapeExtends outcome.heap := by
    rw [allocated]
    exact heap.shapeExtends_cons head tail
  refine ⟨outcome, result, allocated, valueEq, tailRetained, shape, cursorEq, bodyEq, ?_⟩
  rw [outcome.steps_eq, bodyEq]
  rfl

/-- Infer both actual wrapper calls and the final return from the generated body.
The exact execution theorem below retains both calls at the same nesting depth. -/
def prependPairCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeConstruction.Source.program w heapLimit 2
      (NativeConstruction.Source.program.body NativeConstruction.Source.prependPairId)
      initial bound } := by
  ram_source_arena_cost [(prepend_arenaCostBound _ _)]

/-- Two sequential calls to the same generated constructor reuse its exact body
count. Each call pays its own frame work; the final return belongs to the caller. -/
def prependPairBodySteps : Nat := prependPairCost.val

/-- The actual two-constructor wrapper's complete invocation count, including
its own initialization, outer call and final halt. -/
def prependPairSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeConstruction.Source.program)
    (lowerFunc NativeConstruction.Source.program NativeConstruction.Source.prependPairId)
    (prependPairBodySteps + 2) + 1

/-- Two calls to the generated constructor run sequentially at depth two and
retain both actual allocations. The ordinary result and shared-tail frame refer
to the same halted invocation whose exact count includes both wrapper calls. -/
theorem prependPair_execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (first second : Nat) (values : List Nat) (tail : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values tail heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeConstruction.Source.program
      NativeConstruction.Source.prependPairId 2 heapLimit placement
      (NativeConstruction.Source.prependPair_args first second tail) heap cursor entry)
    (space : cursor + 6 ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeConstruction.Source.program
        NativeConstruction.Source.prependPairId 2 heapLimit placement
        (NativeConstruction.Source.prependPair_args first second tail) heap entry,
      (Representation.list .nat).Rel (first :: second :: values) outcome.value outcome.heap ∧
      (Representation.list .nat).Rel values tail outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + 6 ∧
      outcome.bodySteps = prependPairBodySteps + 2 ∧
      outcome.result.steps = prependPairSteps := by
  have positive : 0 < w := launch.positive
  have firstFits : first < 2 ^ w := launch.arguments .here
  have secondFits : second < 2 ^ w := launch.arguments (.there .here)
  have firstSpace : cursor + 3 ≤ heapLimit := by omega
  have nextSpace : (cursor + 3) + 3 ≤ heapLimit := by omega
  let middle := heap.cons second tail
  let allocated := middle.2.cons first (some middle.1)
  obtain ⟨secondExecution, secondReady, secondCost⟩ :=
    prepend_ready_cost second tail heap positive secondFits firstSpace
  obtain ⟨firstExecution, firstReady, firstCost⟩ :=
    prepend_ready_cost first (some middle.1) middle.2 positive firstFits nextSpace
  have measured : ArenaMeasured NativeConstruction.Source.program w heapLimit 2
      (NativeConstruction.Source.program.body NativeConstruction.Source.prependPairId)
      (fun _ control finalCursor steps =>
        control = .returned (some allocated.1) ∧ finalCursor = cursor + 6 ∧
          steps = prependPairBodySteps)
      ⟨NativeConstruction.Source.prependPair_args first second tail, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using secondCost
    ram_source_arena_call exact using firstCost
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, rfl, rfl, rfl⟩ := measured
  obtain ⟨outcome, _, heapEq, cursorEq, bodyEq⟩ :=
    cost.execute (fn := NativeConstruction.Source.prependPairId) launch
  have represented := outcome.post
    (NativeConstruction.prependPair_refines (first, second, values) trivial)
    ⟨rfl, rfl, observed⟩
  have result : (Representation.list .nat).Rel (first :: second :: values)
      outcome.value outcome.heap := by
    change (Representation.list .nat).Rel (NativeConstruction.prependPair first second values)
      outcome.value outcome.heap at represented
    simpa only [prependPair_eq] using represented
  have shape : heap.ShapeExtends outcome.heap := by
    rw [heapEq]
    exact execution.heap_shapeExtends
  refine ⟨outcome, result, Representation.list_mono observed shape, shape, cursorEq, bodyEq, ?_⟩
  rw [outcome.steps_eq, bodyEq]
  rfl

/-- Only the chosen branch allocates: three nodes on the true path and two on
the false path, including the common continuation's final constructor call. -/
def choosePrependReserve (flag : Bool) : Nat :=
  (if flag then 3 else 0) + 3 + 3

/-- The actual branch and common continuation's core count. The option copies
are the initialized join slot, its assignment and its immutable continuation
alias. Branch and sequence overheads are the existing compiler costs. -/
def choosePrependBodySteps (flag : Bool) : Nat :=
  let copy := 2 * fieldCount (.option (.node .nat))
  let prependCall := callCost NativeBranches.Source.program
    (NativeBranches.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.map.toFun
      NativeConstruction.Source.prependId) (prependBodySteps + 2)
  let consCall := callCost NativeBranches.Source.program
    (NativeBranches.Source.imports.NativeBranches.Operations.consNat.map.toFun
      NativeBranches.Operations.consNat.consId)
    (Ram.LanguageCompiler.List.Cons.bodySteps .nat + 2)
  copy + ((if flag then consCall + (prependCall + copy) + 3
    else prependCall + copy + 2) + 2 + (copy + (prependCall + (copy + 2))))

/-- The selected branch's complete invocation, including the wrapper's own
initialization, outer call and halt. Untaken branch calls are not charged. -/
def choosePrependSteps (flag : Bool) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeBranches.Source.program)
    (lowerFunc NativeBranches.Source.program NativeBranches.Source.choosePrependId)
    (choosePrependBodySteps flag + 2) + 1

/-- A native list-valued conditional allocates along its actual selected branch,
merges that list, then invokes the common continuation on the same real heap.
The original roots remain observable even if they share nodes. The execution
record retains complete physical memory and placement for a subsequent call. -/
theorem choosePrepend_execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (flag : Bool) (head : Nat) (leftValues rightValues : List Nat)
    (left right : Option (NodeRef .nat)) {heap : Heap}
    (leftObserved : (Representation.list .nat).Rel leftValues left heap)
    (rightObserved : (Representation.list .nat).Rel rightValues right heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeBranches.Source.program
      NativeBranches.Source.choosePrependId 2 heapLimit placement
      (NativeBranches.Source.choosePrepend_args flag head left right) heap cursor entry)
    (space : cursor + choosePrependReserve flag ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeBranches.Source.program
        NativeBranches.Source.choosePrependId 2 heapLimit placement
        (NativeBranches.Source.choosePrepend_args flag head left right) heap entry,
      (Representation.list .nat).Rel
        (head :: head :: (if flag then head :: leftValues else rightValues))
        outcome.value outcome.heap ∧
      (Representation.list .nat).Rel leftValues left outcome.heap ∧
      (Representation.list .nat).Rel rightValues right outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + choosePrependReserve flag ∧
      outcome.bodySteps = choosePrependBodySteps flag + 2 ∧
      outcome.result.steps = choosePrependSteps flag := by
  have positive : 0 < w := launch.positive
  have headFits : head < 2 ^ w := launch.arguments (.there .here)
  have measured : ArenaMeasured NativeBranches.Source.program w heapLimit 2
      (NativeBranches.Source.program.body NativeBranches.Source.choosePrependId)
      (fun _ control finalCursor steps =>
        ∃ value, control = .returned value ∧
          finalCursor = cursor + choosePrependReserve flag ∧
          steps = choosePrependBodySteps flag)
      ⟨NativeBranches.Source.choosePrepend_args flag head left right, heap⟩ cursor := by
    cases flag with
    | false =>
        change cursor + 6 ≤ heapLimit at space
        have firstSpace : cursor + 3 ≤ heapLimit := by omega
        have lastSpace : (cursor + 3) + 3 ≤ heapLimit := by omega
        let selected := heap.cons head right
        obtain ⟨_, _, selectedCost⟩ :=
          prepend_ready_cost head right heap positive headFits firstSpace
        obtain ⟨_, _, lastCost⟩ :=
          prepend_ready_cost head (some selected.1) selected.2 positive headFits lastSpace
        ram_source_arena_step
        ram_source_arena_call exact using selectedCost via
          NativeBranches.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
        ram_source_arena_call exact using lastCost via
          NativeBranches.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
        exact ⟨_, rfl, rfl, rfl⟩
    | true =>
        change cursor + 9 ≤ heapLimit at space
        have firstSpace : cursor + 3 ≤ heapLimit := by omega
        have secondSpace : (cursor + 3) + 3 ≤ heapLimit := by omega
        have lastSpace : ((cursor + 3) + 3) + 3 ≤ heapLimit := by omega
        let grown := heap.cons head left
        let selected := grown.2.cons head (some grown.1)
        obtain ⟨_, firstCost⟩ := Ram.LanguageCompiler.List.Cons.ready_cost
          .nat head left heap (depth := 1) positive headFits firstSpace
        obtain ⟨_, _, selectedCost⟩ :=
          prepend_ready_cost head (some grown.1) grown.2 positive headFits secondSpace
        obtain ⟨_, _, lastCost⟩ :=
          prepend_ready_cost head (some selected.1) selected.2 positive headFits lastSpace
        ram_source_arena_step
        ram_source_arena_call exact using firstCost via
          NativeBranches.Source.imports.NativeBranches.Operations.consNat.embedding
        ram_source_arena_call exact using selectedCost via
          NativeBranches.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
        ram_source_arena_call exact using lastCost via
          NativeBranches.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
        exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨finish, value, _, _, execution, ready, cost, rfl, rfl⟩ :=
    ArenaMeasured.exists_returned_iff.mp measured
  obtain ⟨outcome, _, heapEq, cursorEq, bodyEq⟩ :=
    cost.execute (fn := NativeBranches.Source.choosePrependId) launch
  have represented := outcome.post
    (NativeBranches.choosePrepend_refines (flag, head, leftValues, rightValues) trivial)
    ⟨rfl, rfl, leftObserved, rightObserved⟩
  have result : (Representation.list .nat).Rel
      (head :: head :: (if flag then head :: leftValues else rightValues))
      outcome.value outcome.heap := by
    change (Representation.list .nat).Rel
      (NativeBranches.choosePrepend flag head leftValues rightValues)
      outcome.value outcome.heap at represented
    simpa only [choosePrepend_eq] using represented
  have shape : heap.ShapeExtends outcome.heap := by
    rw [heapEq]
    exact execution.heap_shapeExtends
  refine ⟨outcome, result, Representation.list_mono leftObserved shape,
    Representation.list_mono rightObserved shape, shape, cursorEq, bodyEq, ?_⟩
  rw [outcome.steps_eq, bodyEq]
  rfl

/-- Infer the wrapper's uniform structural bound from its actual body and the
two callee certificates. No call-table index or field-copy formula is supplied. -/
def replaceHeadCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound NativeViews.Source.program w heapLimit 2
      (NativeViews.Source.program.body NativeViews.Source.replaceHeadId) initial bound } := by
  ram_source_arena_cost [
    (Ram.LanguageCompiler.List.Uncons.arenaCostBound .nat _ _ _)
      via NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding,
    (prepend_arenaCostBound _ _)
      via NativeViews.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding]

/-- The inferred bound is independent of word width, heap limit and List length. -/
def replaceHeadBodyBound : Nat := replaceHeadCost.val

/-- Complete constant invocation bound, including the enclosing initialization,
outer call and halt. Input loading is outside this preloaded-call boundary. -/
def replaceHeadSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeViews.Source.program)
    (lowerFunc NativeViews.Source.program NativeViews.Source.replaceHeadId)
    (replaceHeadBodyBound + 2) + 1

/-- Ordinary List matching reads at most one actual node, shares its tail and
allocates one new head. The same halted RAM execution satisfies the native
mathematical equation, a length-independent instruction bound and three-word
growth. Every old List observation remains valid, including shared tails. -/
theorem replaceHead_execute_le {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (replacement : Nat) (values : List Nat) (root : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeViews.Source.program
      NativeViews.Source.replaceHeadId 2 heapLimit placement
      (NativeViews.Source.replaceHead_args replacement root) heap cursor entry)
    (space : cursor + 3 ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeViews.Source.program
        NativeViews.Source.replaceHeadId 2 heapLimit placement
        (NativeViews.Source.replaceHead_args replacement root) heap entry,
      (Representation.list .nat).Rel (replacement :: values.tail)
        outcome.value outcome.heap ∧
      (Representation.list .nat).Rel values root outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + 3 ∧
      outcome.bodySteps ≤ replaceHeadBodyBound + 2 ∧
      outcome.result.steps ≤ replaceHeadSteps := by
  have positive : 0 < w := launch.positive
  have replacementFits : replacement < 2 ^ w := launch.arguments .here
  obtain ⟨readFinish, parts, readSteps, readExecution, readReady, readCost,
      _readStepsLe, _readHeapEq, _partsObserved⟩ :=
    Ram.LanguageCompiler.List.Uncons.ready_cost .nat values root heap
      (depth := 1) (cursor := cursor) positive launch.arena.heapRep observed
  obtain ⟨_, _, prependCost⟩ := prepend_ready_cost replacement
    (parts.elim none Prod.snd) readFinish.heap positive replacementFits space
  have measured : ArenaMeasured NativeViews.Source.program w heapLimit 2
      (NativeViews.Source.program.body NativeViews.Source.replaceHeadId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor = cursor + 3)
      ⟨NativeViews.Source.replaceHead_args replacement root, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using readCost via
      NativeViews.Source.imports.NativeViews.Operations.unconsNat.embedding
    all_goals
      ram_source_arena_call exact using prependCost via
        NativeViews.Source.imports.Complexity.Language.Examples.LinkedList.NativeConstruction.Source.embedding
    all_goals
      exact ⟨_, rfl⟩
  obtain ⟨outcome, cursorEq, ⟨_, result, rfl⟩, shape, bodyBound, stepsBound⟩ :=
    measured.execute_le (P := fun _ _ finalCursor => finalCursor = cursor + 3)
      (replaceHeadCost.property w heapLimit _)
      (replaceHead_correct (replacement, values) trivial) launch ⟨rfl, observed⟩
  exact ⟨outcome, result, Representation.list_mono observed shape, shape,
    cursorEq, bodyBound, stepsBound⟩

end Complexity.Language.Examples.LinkedList
