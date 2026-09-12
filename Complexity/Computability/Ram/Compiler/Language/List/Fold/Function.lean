/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold

/-!
# Callable list-fold arguments and bounds

The resource and cost contracts share the actual source arguments and the
compiler-derived body envelope. Mathematical inputs remain ghost indices.
`functionPre` retains the resource interface's finite-word and capacity
conditions; `functionCostPre` contains only the represented input and callback
domain needed to bound an already supplied execution.
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
conditions, together with its existing total-reservation envelope.
Zero-growth callbacks have zero accumulated reservation. -/
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

/-- Cost analysis needs only the represented mathematical input and callback
domain, not enough capacity to construct another ready execution. -/
def functionCostPre (representation : Representation α accTy)
    (step : α → CellValue kind → α) (domain : α → CellValue kind → Prop)
    (input : α × _root_.List (CellValue kind) × Value accTy × Option (NodeRef kind))
    (heap : Heap) : Prop :=
  Complexity.Language.List.Fold.Admissible step domain input.1 input.2.1 ∧
    representation.Rel input.1 input.2.2.1 heap ∧ NodeRef.Contents heap input.2.2.2 input.2.1

end Ram.LanguageCompiler.List.Fold
