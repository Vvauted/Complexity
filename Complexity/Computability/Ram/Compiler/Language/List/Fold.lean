/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Ready
import Complexity.Computability.Ram.Compiler.Language.List.Fold.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution

/-!
# Measured execution of linked-list folding

Readiness reuses the independently proved finite source traversal, while cost
certificates bound that same actual execution. Callback ranges and arena growth
stay separate from the instruction envelope. The published RAM result retains
the actual accumulator, heap and cursor and the ordinary mathematical fold.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- One real node lookup and callback invocation update the two traversal
locals. The callback's actual final heap and cursor are retained; only its own
resource proof checks allocation, mutation and intermediate arithmetic ranges. -/
theorem iteration_measured
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (accumulator : Value accTy) (ref : NodeRef kind)
    (head : CellValue kind) (tail : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w) (allowed : domain mathematical head)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator) (headFits : ValueFits w (kind.toValue head))
    (found : heap.node? kind ref.object = some (head, tail))
    (capacity : cursor + reserve mathematical head ≤ heapLimit) :
    ∃ finalAcc finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.List.Fold.iteration fn same)
        (Complexity.Language.List.Fold.state accumulator (some ref) heap)
        (Complexity.Language.List.Fold.state finalAcc tail finalHeap) .normal,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
        steps ≤ callCost program fn (bound mathematical head) + 2 * fieldCount accTy + 26 ∧
        finalCursor ≤ cursor + reserve mathematical head ∧
        representation.Rel (step mathematical head) finalAcc finalHeap ∧
        ValueFits w finalAcc ∧ heap.ShapeExtends finalHeap := by
  obtain ⟨finalAcc, finalHeap, finalCursor, execution, ready, cursorBound,
      resultRelated, returnedFits, preserved⟩ :=
    iteration_ready correct resources mathematical accumulator ref head tail heap cursor
      positive allowed related accFits headFits found capacity
  obtain ⟨steps, cost⟩ := ready.exists_cost
  exact ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost,
    iteration_costBound bounded mathematical accumulator ref head tail heap
      allowed related found execution ready cost,
    cursorBound, resultRelated, returnedFits, preserved⟩

/-- The actual while loop threads callback returns and arena growth through
the represented suffix. Only proof-side lists index the changing budget;
there is no runtime length read, traversal fuel or recursive fold invocation. -/
theorem loop_measured
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ∃ finalAcc finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.loop fn same)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state finalAcc none finalHeap) .normal,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
        steps ≤ remainingCost program fn accTy step bound mathematical values + 17 ∧
        finalCursor ≤ cursor + accumulated step reserve mathematical values ∧
        ValueFits w finalAcc := by
  obtain ⟨finalAcc, finalHeap, finalCursor, execution, ready, cursorBound, finalFits⟩ :=
    loop_ready correct resources mathematical values accumulator root heap cursor
      positive allowed related accFits headFits capacity observed
  obtain ⟨steps, cost⟩ := ready.exists_cost
  exact ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost,
    loop_costBound correct bounded mathematical values accumulator root heap
      allowed related observed execution ready cost,
    cursorBound, finalFits⟩

/-- Return the actual accumulator produced by the same measured while loop.
The count adds the real sequence check and result fields, with function-entry
initialization still charged separately by the invocation interface. -/
theorem body_measured
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ∃ finalAcc finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.body fn same)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state finalAcc none finalHeap) (.returned finalAcc),
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
        steps ≤ remainingCost program fn accTy step bound mathematical values +
          2 * fieldCount accTy + 21 ∧
        finalCursor ≤ cursor + accumulated step reserve mathematical values := by
  obtain ⟨finalAcc, finalHeap, finalCursor, loopSteps, traversed, loopReady, loopCost,
    loopBound, cursorBound, finalFits⟩ :=
    loop_measured correct resources bounded mathematical values accumulator root heap cursor
      positive allowed related accFits headFits capacity observed
  let finish := Complexity.Language.List.Fold.state finalAcc (none : Option (NodeRef kind)) finalHeap
  let returned := Complexity.Language.Exec.ret (program := program) (.var .here) finish
  let execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.body fn same)
      (Complexity.Language.List.Fold.state accumulator root heap) finish (.returned finalAcc) :=
    .seqNormal traversed returned
  let returnReady : ArenaReady returned w heapLimit (depth + 1) finalCursor finalCursor :=
    .ret (.var .here) finish finalFits
  let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
    .seqNormal loopReady returnReady
  have cost : ArenaExecutionCost ready (loopSteps + 2 + (2 * fieldCount accTy + 2)) :=
    .seqNormal loopCost (.ret (.var .here) finish (fits := finalFits))
  exact ⟨finalAcc, finalHeap, finalCursor, _, execution, ready, cost, by omega, cursorBound⟩

/-- Publish the same halted RAM invocation with its ordinary `List.foldl`
result and actual final heap. Old linked lists survive callback mutation and
allocation by source heap-shape preservation; the arena budget accumulates
only the actual callbacks' supplied reservations along this fold trajectory. -/
theorem execute_le
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract
      sourceProgram fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources sourceProgram fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound sourceProgram fn same representation domain w heapLimit depth bound)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind))
    {heap : Heap} {cursor : Nat} {placement : Nat → Word w} {initial : Source.State w}
    (launch : FunctionArenaLaunch (Complexity.Language.List.Fold.program sourceProgram fn same)
      (Complexity.Language.List.Fold.entry accTy kind signatures) (depth + 1) heapLimit placement
      (foldArgs accumulator root) heap cursor initial)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (observed : (Representation.list kind).Rel values root heap)
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution (Complexity.Language.List.Fold.program sourceProgram fn same)
        (Complexity.Language.List.Fold.entry accTy kind signatures) (depth + 1) heapLimit placement
        (foldArgs accumulator root) heap initial,
      representation.Rel (values.foldl step mathematical) outcome.value outcome.heap ∧
      (Representation.list kind).Rel values root outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.result.steps ≤ invocationBound sourceProgram fn same step bound mathematical values ∧
      outcome.cursor ≤ cursor + accumulated step reserve mathematical values := by
  have embedded := Complexity.Language.List.Fold.program_embeds sourceProgram fn same
  have relocated :
      Complexity.Language.List.Fold.calleeBody
        (Complexity.Language.List.Fold.program sourceProgram fn same)
        (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
        (Complexity.Language.List.Fold.callee_signature same) =
      (Complexity.Language.List.Fold.calleeBody sourceProgram fn same).renameCalls
        (Complexity.Language.List.Fold.calleeMap accTy kind signatures) :=
    Complexity.Language.List.Fold.calleeBody_renameCalls embedded same
  have linkedResources : CalleeResources
      (Complexity.Language.List.Fold.program sourceProgram fn same)
      (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
      (Complexity.Language.List.Fold.callee_signature same)
      representation domain w heapLimit depth reserve := by
    unfold CalleeResources
    rw [relocated]
    exact FunctionArenaResources.renameCalls resources embedded
  have linkedBounded : CalleeCostBound
      (Complexity.Language.List.Fold.program sourceProgram fn same)
      (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
      (Complexity.Language.List.Fold.callee_signature same)
      representation domain w heapLimit depth bound := by
    unfold CalleeCostBound
    rw [relocated]
    exact FunctionArenaCostBound.renameCalls bounded embedded
  have accFits : ValueFits w accumulator := launch.arguments (τ := accTy) .here
  have headFits : ∀ head ∈ values, ValueFits w (kind.toValue head) :=
    contents_valueFits launch.arena.heapRep observed
  have measured := body_measured
    (Complexity.Language.List.Fold.callee_contract sourceProgram fn same correct)
    linkedResources linkedBounded mathematical values accumulator root heap cursor launch.positive
    allowed related accFits headFits capacity observed
  rw [← Complexity.Language.List.Fold.program_body sourceProgram fn same] at measured
  obtain ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost,
    coreBound, cursorBound⟩ := measured
  obtain ⟨outcome, _, _, cursorEq, bodySteps⟩ := cost.execute launch
  have property := outcome.post
    (Complexity.Language.List.Fold.program_total correct mathematical values allowed)
    ⟨related, observed⟩
  refine ⟨outcome, property.1, property.2.1, property.2.2, ?_, ?_⟩
  · rw [outcome.steps_eq, bodySteps]
    unfold invocationBound
    exact Nat.add_le_add_right (LocalCompiler.Function.callSteps_mono _ _ (by omega)) 1
  · simpa only [cursorEq] using cursorBound

end Ram.LanguageCompiler.List.Fold
