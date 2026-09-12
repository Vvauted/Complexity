/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold

/-!
# Resource contracts for calling the shared list fold

The actual entry of `List.Fold.program` has the same reusable arena-resource and
body-cost contracts as its callbacks. Original callback proofs are relocated
through the existing program embedding; the traversal is the already measured
source body, not another implementation. The argument index retains both the
mathematical inputs and their actual source representations.

The precondition includes word ranges and enough total arena capacity for the
accumulated callback reservations. Resource readiness uses the caller's actual
cursor and its stronger remaining-capacity premise. The cost predicate has no
incoming capacity premise, so its proof constructs a comparison witness at
numeric cursor zero and uses cost determinism to reach the caller's actual
execution. This does not reset the running program's cursor, require a physical
heap at address zero, or discard callback heap effects.

Bounds include the fold body's two initialization instructions. Its caller adds
call-frame work separately; a standalone outer invocation also adds halt. These
contracts can be relocated again using `FunctionArenaResources.renameCalls` and
`FunctionArenaCostBound.renameCalls` when the fold is imported by another program.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- The mathematical accumulator and list are ghost indices; only the actual
accumulator and linked root are passed to the source function. -/
def functionArgs
    (input : α × _root_.List (CellValue kind) × Value accTy × Option (NodeRef kind)) :
    Env [accTy, .option (.node kind)] :=
  foldArgs input.2.2.1 input.2.2.2

/-- The shared fold's represented input, callback domain and finite-word
conditions. Total reserved capacity supports a cost witness independent of the
caller's cursor; zero-growth callbacks have zero accumulated reservation. -/
def functionPre (representation : Representation α accTy)
    (step : α → CellValue kind → α) (domain : α → CellValue kind → Prop)
    (w heapLimit : Nat) (reserve : α → CellValue kind → Nat)
    (input : α × _root_.List (CellValue kind) × Value accTy × Option (NodeRef kind))
    (heap : Heap) : Prop :=
  Complexity.Language.List.Fold.Admissible step domain input.1 input.2.1 ∧
    representation.Rel input.1 input.2.2.1 heap ∧
    NodeRef.Contents heap input.2.2.2 input.2.1 ∧
    ValueFits w input.2.2.1 ∧
    (∀ head ∈ input.2.1, ValueFits w (kind.toValue head)) ∧
    accumulated step reserve input.1 input.2.1 ≤ heapLimit

/-- The callable body's envelope includes initialization but not its caller's
frame or halt. Callback charges use their actual relocated function table. -/
def functionBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (mathematical : α) (values : _root_.List (CellValue kind)) : Nat :=
  remainingCost (Complexity.Language.List.Fold.program sourceProgram fn same)
    (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
    accTy step bound mathematical values + 2 * fieldCount accTy + 23

/-- Execute the actual fold entry from ordinary mathematical and source
arguments, reusing the callback's independent correctness and resource proofs.
The result retains the real final accumulator, heap, cursor and exact core count,
together with the compiler-derived bound including body initialization. A caller
can compose this measured execution directly without assembling a resource index
or relocating callback contracts itself. -/
theorem measured
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
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ∃ finalAcc finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec
        (Complexity.Language.List.Fold.program sourceProgram fn same)
        ((Complexity.Language.List.Fold.program sourceProgram fn same).body
          (Complexity.Language.List.Fold.entry accTy kind signatures))
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state finalAcc none finalHeap) (.returned finalAcc),
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
        steps + 2 ≤ functionBound sourceProgram fn same step bound mathematical values ∧
        finalCursor ≤ cursor + accumulated step reserve mathematical values := by
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
  have measured := body_measured
    (Complexity.Language.List.Fold.callee_contract sourceProgram fn same correct)
    linkedResources linkedBounded mathematical values accumulator root heap cursor positive
    allowed related accFits headFits capacity observed
  rw [← Complexity.Language.List.Fold.program_body sourceProgram fn same] at measured
  obtain ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost,
    coreBound, cursorBound⟩ := measured
  refine ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost, ?_, cursorBound⟩
  unfold functionBound
  omega

/-- The actual fold entry is reusable as an arena callee. Its retained cursor
bound is the accumulated callback reservation; readiness starts at the actual
caller's cursor and uses the capacity supplied by the shared resource contract. -/
theorem functionResources
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract
      sourceProgram fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources sourceProgram fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound sourceProgram fn same representation domain w heapLimit depth bound)
    (positive : 0 < w) :
    FunctionArenaResources (Complexity.Language.List.Fold.program sourceProgram fn same)
      ((Complexity.Language.List.Fold.program sourceProgram fn same).body
        (Complexity.Language.List.Fold.entry accTy kind signatures))
      functionArgs (functionPre representation step domain w heapLimit reserve)
      w heapLimit (depth + 1) (fun input => accumulated step reserve input.1 input.2.1) := by
  rintro ⟨mathematical, values, accumulator, root⟩ heap cursor input _ capacity
    finish value execution
  rcases input with ⟨allowed, related, observed, accFits, headFits, _⟩
  obtain ⟨finalAcc, finalHeap, finalCursor, steps, measured, ready, cost,
    coreBound, cursorBound⟩ :=
    measured correct resources bounded mathematical values accumulator root heap cursor
      positive allowed related accFits headFits capacity observed
  obtain ⟨rfl, sameControl⟩ := measured.deterministic execution
  cases Control.returned.inj sameControl
  exact ⟨finalCursor, ready, cursorBound⟩

/-- The actual fold entry inherits its measured body bound for every supplied
arena execution. The cursor-zero witness is used only to compare compiler
counts, never to change the caller's cursor, final heap or actual execution. -/
theorem functionCostBound
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract
      sourceProgram fn same representation step domain)
    {w heapLimit depth : Nat} {reserve bound : α → CellValue kind → Nat}
    (resources : CalleeResources sourceProgram fn same representation domain w heapLimit depth reserve)
    (bounded : CalleeCostBound sourceProgram fn same representation domain w heapLimit depth bound)
    (positive : 0 < w) :
    FunctionArenaCostBound (Complexity.Language.List.Fold.program sourceProgram fn same)
      ((Complexity.Language.List.Fold.program sourceProgram fn same).body
        (Complexity.Language.List.Fold.entry accTy kind signatures))
      functionArgs (functionPre representation step domain w heapLimit reserve)
      w heapLimit (depth + 1)
      (fun input => functionBound sourceProgram fn same step bound input.1 input.2.1) := by
  rintro ⟨mathematical, values, accumulator, root⟩ heap input finish value execution
    cursor finalCursor ready steps cost
  rcases input with ⟨allowed, related, observed, accFits, headFits, capacity⟩
  obtain ⟨finalAcc, finalHeap, measuredCursor, measuredSteps, measured, measuredReady,
    measuredCost, coreBound, _⟩ :=
    measured correct resources bounded mathematical values accumulator root heap 0
      positive allowed related accFits headFits (by simpa only [Nat.zero_add] using capacity) observed
  have sameSteps : steps = measuredSteps := cost.deterministic measuredCost
  simpa only [sameSteps] using coreBound

end Ram.LanguageCompiler.List.Fold
