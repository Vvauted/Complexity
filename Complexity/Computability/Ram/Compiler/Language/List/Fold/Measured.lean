/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Resources
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured

/-!
# Composing the measured list-fold entry

`arenaMeasured_of_ready` exposes the existing ordinary-parameter fold readiness
through the shared structural composition interface, without a proposed callback
time bound. Its result, heap, cursor and exact count belong to the same source
execution supplied by `ready`; the observation retains the cursor reservation.
Callers can compose this certificate without unpacking and reconstructing
execution and readiness.

`arenaMeasured` additionally applies the independent callback cost contract to
that same execution. Its body bound includes initialization once; the existing
call rules add the actual caller overhead. Mathematical result specifications
remain independent source contracts and can be attached to either certificate
with `ArenaMeasured.with_spec`.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- Compose the actual fold entry from its resource readiness, without a
callback time bound. The cost witness counts this same execution; only its
cursor reservation is retained as an observation. -/
theorem arenaMeasured_of_ready
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract
      sourceProgram fn same representation step domain)
    {w heapLimit depth : Nat} {reserve : α → CellValue kind → Nat}
    (resources : CalleeResources sourceProgram fn same representation domain w heapLimit depth reserve)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ArenaMeasured (Complexity.Language.List.Fold.program sourceProgram fn same)
      w heapLimit (depth + 1)
      ((Complexity.Language.List.Fold.program sourceProgram fn same).body
        (Complexity.Language.List.Fold.entry accTy kind signatures))
      (fun _ control finalCursor _ => ∃ value, control = .returned value ∧
        finalCursor ≤ cursor + accumulated step reserve mathematical values)
      (Complexity.Language.List.Fold.state accumulator root heap) cursor := by
  obtain ⟨finalAcc, finalHeap, finalCursor, execution, ready, cursorBound⟩ :=
    ready correct resources mathematical values accumulator root heap cursor
      positive allowed related accFits headFits capacity observed
  obtain ⟨steps, cost⟩ := ready.exists_cost
  exact ⟨Complexity.Language.List.Fold.state finalAcc none finalHeap, .returned finalAcc,
    finalCursor, steps, execution, ready, cost, finalAcc, rfl, cursorBound⟩

/-- Compose the actual fold entry from ordinary mathematical and source
arguments. This packages the existing measured execution and its bounds; it
does not construct another traversal or infer a mathematical list from a root. -/
theorem arenaMeasured
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
    ArenaMeasured (Complexity.Language.List.Fold.program sourceProgram fn same)
      w heapLimit (depth + 1)
      ((Complexity.Language.List.Fold.program sourceProgram fn same).body
        (Complexity.Language.List.Fold.entry accTy kind signatures))
      (fun _ control finalCursor steps => ∃ value, control = .returned value ∧
        steps + 2 ≤ functionBound sourceProgram fn same step bound mathematical values ∧
        finalCursor ≤ cursor + accumulated step reserve mathematical values)
      (Complexity.Language.List.Fold.state accumulator root heap) cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost,
      value, rfl, cursorBound⟩ :=
    arenaMeasured_of_ready correct resources mathematical values accumulator root heap cursor
      positive allowed related accFits headFits capacity observed
  exact ⟨finish, .returned value, finalCursor, steps, execution, ready, cost, value, rfl,
    functionCostBound_of_actual correct bounded (mathematical, values, accumulator, root) heap
      ⟨allowed, related, observed⟩ finish value execution ready cost, cursorBound⟩

end Ram.LanguageCompiler.List.Fold
