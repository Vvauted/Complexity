/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources

/-!
# Compiling construction of represented linked lists

The same source constructor allocates one three-word node and returns its root.
Its existing tail is shared, with no validation scan or suffix copy. The source
contract supplies ordinary `List.cons` correctness; arena readiness supplies
word ranges and space for that actual allocation independently of correctness.

The exact body count is proved by the existing allocation, option-construction
and return cost rules. Publication retains the complete halted machine state,
extended placement and updated cursor, so later calls resume the real memory
rather than reinitializing the arena. Input loading and session bootstrap remain
outside this invocation boundary.
-/

namespace Ram.LanguageCompiler.List.Cons

open Complexity.Language
open Complexity.Language.List.Cons

/-- The emitted body length. The theorem below establishes that this particular
straight-line source execution has this same dynamic instruction count. -/
def bodySteps (kind : CellTy) : Nat :=
  sourceCodeSize (LocalCompiler.calleeLocals (lowerProgram (program kind)))
    ((program kind).body (entry kind))

/-- The actual constructor is ready with one three-word allocation. Its exact
count follows the existing cost constructors, not a proposed operation price.
Rootedness is a separate launch condition, not a runtime tail check. -/
theorem body_ready_cost (kind : CellTy)
    (initial : Complexity.Language.State [kind.toTy, .option (.node kind)])
    {w heapLimit depth cursor : Nat} (hw : 0 < w)
    (headFits : ValueFits w initial.locals.head)
    (tailFits : ValueFits w initial.locals.tail.head)
    (capacity : cursor + 3 ≤ heapLimit) :
    ∃ ready : ArenaReady (body_exec (program kind) kind initial)
        w heapLimit depth cursor (cursor + 3),
      ArenaExecutionCost ready (bodySteps kind) := by
  let allocated := initial.heap.cons (kind.ofValue initial.locals.head)
    initial.locals.tail.head
  let withNode : Complexity.Language.State
      [.node kind, kind.toTy, .option (.node kind)] :=
    Complexity.Language.State.cons (τ := .node kind) allocated.1
      ⟨initial.locals, allocated.2⟩
  let received : Complexity.Language.State
      [.option (.node kind), .node kind, kind.toTy, .option (.node kind)] :=
    Complexity.Language.State.cons (τ := .option (.node kind)) (some allocated.1) withNode
  have tagFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have someFits : PrimFits w withNode.locals (.some (.var .here)) := ⟨tagFits, trivial⟩
  have returnedFits : ValueFits w (τ := .option (.node kind)) (some allocated.1) :=
    ⟨tagFits, trivial⟩
  let ready : ArenaReady (body_exec (program kind) kind initial)
      w heapLimit depth cursor (cursor + 3) :=
    .consNode (head := .var .here) (tail := .var (.there .here))
      (continuation := .letPrim (.some (.var .here)) (.ret (.var .here)))
      (entry := initial) (finish := withNode) headFits tailFits capacity
      (.letPrim (value := .some (.var .here)) (entry := withNode) (finish := received)
        someFits (.ret (.var .here) received returnedFits))
  refine ⟨ready, ?_⟩
  exact .consNode (head := .var .here) (tail := .var (.there .here))
    (continuation := .letPrim (.some (.var .here)) (.ret (.var .here)))
    (entry := initial) (finish := withNode)
    (headFits := headFits) (tailFits := tailFits) (capacity := capacity)
    (.letPrim (value := .some (.var .here)) (entry := withNode) (finish := received)
      (fits := someFits) (.ret (.var .here) received (fits := returnedFits)))

/-- Reuse the same measured constructor with ordinary head and tail arguments.
The optional tail's tag fits at every positive word width. -/
theorem ready_cost (kind : CellTy) (head : CellValue kind)
    (tail : Option (NodeRef kind)) (heap : Heap)
    {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (headFits : ValueFits w (τ := kind.toTy) (kind.toValue head))
    (capacity : cursor + 3 ≤ heapLimit) :
    ∃ ready : ArenaReady (body_exec (program kind) kind ⟨args kind head tail, heap⟩)
        w heapLimit depth cursor (cursor + 3),
      ArenaExecutionCost ready (bodySteps kind) := by
  exact body_ready_cost kind ⟨args kind head tail, heap⟩ positive headFits
    (ValueFits.option_node positive tail) capacity

/-- Every actual constructor execution has the same compiler-derived count.
This is a fact about an existing execution, not a termination or capacity claim. -/
theorem cost_eq (kind : CellTy) {w heapLimit depth cursor finalCursor steps : Nat}
    {initial finish : Complexity.Language.State [kind.toTy, .option (.node kind)]}
    {control : Control (.option (.node kind))}
    {execution : Complexity.Language.Exec (program kind) (body kind) initial finish control}
    {ready : ArenaReady execution w heapLimit depth cursor finalCursor}
    (cost : ArenaExecutionCost ready steps) : steps = bodySteps kind := by
  cases cost with
  | consNode next =>
      cases next with
      | letPrim returned =>
          cases returned
          rfl

/-- A reusable bound for the real allocating function, including its private
initialization. Argument ranges and capacity belong to readiness, not its price. -/
theorem arenaCostBound (kind : CellTy) (w heapLimit depth : Nat) :
    FunctionArenaCostBound (program kind) ((program kind).body (entry kind))
      id (fun _ _ => True) w heapLimit depth (fun _ => bodySteps kind + 2) := by
  intro initial heap _ finish value execution cursor finalCursor ready steps cost
  exact Nat.le_of_eq (congrArg (fun n => n + 2) (cost_eq kind cost))

/-- Add the actual private-flag initialization, outer call and final halt to
the proved body count. No additional budget is selected by the caller. -/
def steps (kind : CellTy) : Nat :=
  LocalCompiler.Function.callSteps (programControl (program kind))
    (lowerFunc (program kind) (entry kind)) (bodySteps kind + 2) + 1

/-- Allocate the mathematical cons in the same halted RAM invocation. The result
retains its complete physical memory and extended placement through the existing
typed execution record. The tail's contents supply rootedness internally; the
only new allocation capacity is the actual three-word node. -/
theorem execute_le (kind : CellTy) {w heapLimit cursor : Nat}
    (head : CellValue kind) (values : _root_.List (CellValue kind))
    (tail : Option (NodeRef kind)) (initialHeap : Heap)
    (initial : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity (program kind) (entry kind) w 0 heapLimit)
    (arena : ArenaRep placement cursor heapLimit initialHeap initial)
    (headFits : ValueFits w (kind.toValue head))
    (space : cursor + 3 ≤ heapLimit)
    (observed : (Representation.list kind).Rel values tail initialHeap) :
    ∃ outcome : FunctionArenaExecution (program kind) (entry kind) 0 heapLimit placement
        (Env.cons (τ := kind.toTy) (kind.toValue head)
          (Env.cons (τ := .option (.node kind)) tail Env.empty)) initialHeap initial,
      (Representation.list kind).Rel (head :: values) outcome.value outcome.heap ∧
      outcome.heap = (initialHeap.cons head tail).2 ∧
      outcome.value = some (initialHeap.cons head tail).1 ∧
      initialHeap.ShapeExtends outcome.heap ∧
      outcome.cursor = cursor + 3 ∧
      outcome.result.steps ≤ steps kind := by
  let args : Env [kind.toTy, .option (.node kind)] :=
    Env.cons (τ := kind.toTy) (kind.toValue head)
      (Env.cons (τ := .option (.node kind)) tail Env.empty)
  have tailFits : ValueFits w (τ := .option (.node kind)) tail := by
    cases tail with
    | none => trivial
    | some ref => exact ⟨Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive), trivial⟩
  have arguments : EnvFits w args :=
    EnvFits.cons (τ := kind.toTy)
      (EnvFits.cons (τ := .option (.node kind)) (EnvFits.empty w) tail tailFits)
      (kind.toValue head) headFits
  have rooted : args.Rooted initialHeap :=
    Env.Rooted.cons (τ := kind.toTy)
      (Env.Rooted.cons (τ := .option (.node kind)) (Env.Rooted.empty initialHeap)
        tail (Representation.list_rooted observed))
      (kind.toValue head) (CellTy.toValue_rooted initialHeap kind head)
  let launch : FunctionArenaLaunch (program kind) (entry kind) 0 heapLimit placement
      args initialHeap cursor initial := ⟨capacity, arguments, rooted, arena⟩
  obtain ⟨ready, cost⟩ := body_ready_cost kind ⟨args, initialHeap⟩
    (depth := 0) capacity.positive headFits tailFits space
  obtain ⟨outcome, _, _, cursorEq, bodyEq⟩ := cost.execute launch
  have property := outcome.post (total kind head values)
    ⟨(Representation.cell_rel kind head (kind.toValue head) initialHeap).mpr rfl, observed⟩
  refine ⟨outcome, property.1, property.2.1, property.2.2.1, property.2.2.2, cursorEq, ?_⟩
  rw [outcome.steps_eq, bodyEq]
  exact Nat.le_refl _

end Ram.LanguageCompiler.List.Cons
