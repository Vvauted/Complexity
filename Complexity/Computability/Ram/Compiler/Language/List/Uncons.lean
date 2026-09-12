/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Uncons
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.MeasuredNode
import Complexity.Computability.Ram.Compiler.Language.Arena.ExecutionCost
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Compiling decomposition of represented linked lists

The source operation matches the optional root and, when present, reads the
actual node's head and shared tail. Its result is related to ordinary list
head/tail observations at the unchanged heap. No suffix is copied or validated
by traversal, and mathematical object identifiers are not machine addresses.

The bound composes the existing match, node-read, option-construction and return
rules. The public theorem describes the same halted RAM invocation, including
its outer call and halt. Preloading the input heap remains outside this boundary.
-/

namespace Ram.LanguageCompiler.List.Uncons

open Complexity.Language
open Complexity.Language.List.Uncons

/-- Realization needs only the actual nonempty-root lookup and the ranges of
its returned fields. It imposes no scan or separate bound on source node IDs. -/
theorem realizable (kind : CellTy) {w : Nat} (hw : 0 < w) :
    FunctionRealizable (program kind) w 0 (entry kind)
      (fun args heap => ∀ ref, args.head = some ref →
        ∃ head tail, heap.node? kind ref.object = some (head, tail) ∧
          ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
            (kind.toValue head, tail)) := by
  intro args heap readable
  change ∃ finish value,
    RealizedExec (program kind) w 0 (body kind) ⟨args, heap⟩ finish (.returned value)
  have tagFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  cases selected : args.head with
  | none =>
      refine ⟨⟨args, heap⟩, none, .matchNone selected ?_⟩
      exact .letPrim
        (finish := Complexity.Language.State.cons
          (τ := .option (.prod kind.toTy (.option (.node kind)))) none ⟨args, heap⟩)
        (by trivial) (.ret (.var .here) _ (by trivial))
  | some ref =>
      obtain ⟨head, tail, found, fits⟩ := readable ref selected
      refine ⟨⟨args, heap⟩, some (kind.toValue head, tail), ?_⟩
      refine .matchSome (entry := ⟨args, heap⟩) (payload := ref)
        (finish := Complexity.Language.State.cons (τ := .node kind) ref ⟨args, heap⟩)
        (value := .var .here) selected (by trivial) ?_
      refine .readNode
        (finish := Complexity.Language.State.cons
          (τ := .prod kind.toTy (.option (.node kind))) (kind.toValue head, tail)
          (Complexity.Language.State.cons (τ := .node kind) ref ⟨args, heap⟩)) found fits ?_
      refine .letPrim (value := .some (.var .here))
        (finish := Complexity.Language.State.cons
          (τ := .option (.prod kind.toTy (.option (.node kind))))
          (some (kind.toValue head, tail))
          (Complexity.Language.State.cons
            (τ := .prod kind.toTy (.option (.node kind))) (kind.toValue head, tail)
            (Complexity.Language.State.cons (τ := .node kind) ref ⟨args, heap⟩))) ?_ ?_
      · exact ⟨tagFits, fits⟩
      · refine .ret (.var .here) _ ?_
        exact ⟨tagFits, fits⟩

/-- Infer one input-independent body certificate from the actual operation
rules. The node read, option payload copy and result fields are all charged. -/
def bodyCost (kind : CellTy) : { bound : Nat //
    ∀ initial : Complexity.Language.State [.option (.node kind)],
      StmtCostBound (program kind) (body kind) initial bound } := ⟨_, by
  intro initial
  apply StmtCostBound.match_max
  · intro selected
    exact StmtCostBound.letPrim _ (StmtCostBound.ret (.var .here) _)
  · intro ref selected
    apply StmtCostBound.readNode_uniform
    intro head tail
    exact StmtCostBound.letPrim _ (StmtCostBound.ret (.var .here) _)⟩

/-- Function accounting includes the existing private-flag initialization. -/
theorem costBound (kind : CellTy) :
    FunctionCostBound (program kind) (entry kind) (fun _ _ => True)
      (fun _ _ => (bodyCost kind).val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => (bodyCost kind).property ⟨args, heap⟩)

/-- Decomposition reads a node but writes no shared heap object. -/
theorem program_noHeapWrites (kind : CellTy) :
    ∀ fn, NoHeapWrites ((program kind).body fn) := by
  intro fn
  refine Fin.cases ?_ (fun index => Fin.elim0 index) fn
  change NoHeapWrites (body kind)
  simp [body, NoHeapWrites]

/-- The existing read-only body bound applies to every actual arena execution.
The bridge checks that this body and all its callees perform no heap writes. -/
theorem arenaCostBound (kind : CellTy) (w heapLimit depth : Nat) :
    FunctionArenaCostBound (program kind) ((program kind).body (entry kind))
      id (fun _ _ => True) w heapLimit depth (fun _ => (bodyCost kind).val + 2) := by
  apply FunctionArenaCostBound.of_stmt
  intro args heap _
  exact StmtArenaCostBound.of_noHeapWrites ((bodyCost kind).property _)
    (program_noHeapWrites kind (entry kind)) (program_noHeapWrites kind)

private theorem readable_of_heapRep {kind : CellTy} {w heapLimit : Nat}
    {heap : Heap} {initial : Source.State w} {placement : Nat → Word w}
    {values : _root_.List (CellValue kind)} {root : Option (NodeRef kind)}
    (memory : HeapRep placement heapLimit heap initial)
    (observed : (Representation.list kind).Rel values root heap) :
    ∀ ref, root = some ref →
      ∃ head tail, heap.node? kind ref.object = some (head, tail) ∧
        ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) := by
  intro ref selected
  have contents : NodeRef.Contents heap (some ref) values := by
    rw [← selected]
    exact observed
  cases contents with
  | cons found tail => exact ⟨_, _, found, memory.node_valueFits found⟩

/-- Ordinary list arguments supply the same actual decomposition and its arena
cost. Existing heap and list representations establish read success and field
ranges; no new lookup or object-identifier bound is required. The cursor and
entire heap are unchanged, and the existing body certificate bounds its count. -/
theorem ready_cost (kind : CellTy) (values : _root_.List (CellValue kind))
    (root : Option (NodeRef kind)) (heap : Heap)
    {w heapLimit depth cursor : Nat} {initial : Source.State w} {placement : Nat → Word w}
    (positive : 0 < w) (memory : HeapRep placement heapLimit heap initial)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ finish value actualSteps,
      ∃ execution : Complexity.Language.Exec (program kind) (body kind)
          ⟨Env.cons (τ := .option (.node kind)) root Env.empty, heap⟩ finish (.returned value),
      ∃ ready : ArenaReady execution w heapLimit depth cursor cursor,
        ArenaExecutionCost ready actualSteps ∧ actualSteps ≤ (bodyCost kind).val ∧
        finish.heap = heap ∧
        (resultRepresentation kind).Rel
          (values.head?.map (fun head => (head, values.tail))) value finish.heap := by
  obtain ⟨finish, value, realized⟩ :=
    (realizable kind positive).mono_depth (Nat.zero_le depth)
      (Env.cons (τ := .option (.node kind)) root Env.empty) heap
      (readable_of_heapRep memory observed)
  obtain ⟨actualSteps, cost⟩ := realized.exists_cost
  have property := (total kind values).postcondition
    (args := Env.cons (τ := .option (.node kind)) root Env.empty) (heap := heap)
    observed realized.erase
  exact ⟨finish, value, actualSteps, realized.erase, realized.arenaReady heapLimit cursor,
    cost.arena heapLimit cursor, (bodyCost kind).property _ realized cost,
    property.2, property.1⟩

/-- The inferred function budget plus the actual outer-call and halt charges. -/
def steps (kind : CellTy) : Nat :=
  LocalCompiler.Function.callSteps (programControl (program kind))
    (lowerFunc (program kind) (entry kind)) ((bodyCost kind).val + 2) + 1

/-- The same halted execution returns the mathematical head and the identical
shared tail, preserving all old heap contents. The input's linked representation
and complete memory representation supply read success and word ranges inside
the bridge; callers need no register-level or tail-traversal premise. -/
theorem execute_le (kind : CellTy) {w heapLimit : Nat}
    (values : _root_.List (CellValue kind)) (root : Option (NodeRef kind))
    (initialHeap : Heap) (initial : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity (program kind) (entry kind) w 0 heapLimit)
    (memory : HeapRep placement heapLimit initialHeap initial)
    (observed : (Representation.list kind).Rel values root initialHeap) :
    ∃ outcome : FunctionExecution (program kind) (entry kind) heapLimit placement
        (Env.cons (τ := .option (.node kind)) root Env.empty) initialHeap initial,
      (resultRepresentation kind).Rel
        (values.head?.map (fun head => (head, values.tail))) outcome.value outcome.heap ∧
      outcome.heap = initialHeap ∧
      Source.State.Observes heapLimit 0 initial outcome.result.state ∧
      outcome.result.steps ≤ steps kind := by
  let args : Env [.option (.node kind)] := Env.cons root Env.empty
  have arguments : EnvFits w args := by
    refine EnvFits.cons (τ := .option (.node kind)) (EnvFits.empty w) root ?_
    cases root with
    | none => trivial
    | some ref => exact ⟨Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive), trivial⟩
  have readable : ∀ ref, args.head = some ref →
      ∃ head tail, initialHeap.node? kind ref.object = some (head, tail) ∧
        ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) := readable_of_heapRep memory observed
  let launch : FunctionLaunch (program kind) (entry kind) 0 heapLimit placement
      args initialHeap initial := ⟨capacity, arguments, memory⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (realizable kind capacity.positive).execute_le
      (total kind values) (costBound kind) launch readable observed trivial
  exact ⟨outcome, property.1, property.2,
    outcome.observes_of_noHeapWrites (program_noHeapWrites kind), bounded⟩

end Ram.LanguageCompiler.List.Uncons
