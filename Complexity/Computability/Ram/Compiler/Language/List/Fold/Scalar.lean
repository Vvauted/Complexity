/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources.Finite

/-!
# Reusing nonallocating function proofs in linked-list folds

The original callback's `FunctionRealizable` and `FunctionCostBound` proofs
already provide the range and cost facts needed by a fold. These adapters only
connect its two actual arguments to the fold's mathematical precondition and
bound. The accumulator may have any existing representation; only the node
head is scalar. No host-side decoder, heap-identity condition or second callback
execution is required.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- Reuse the selected callback's existing range proof with zero arena growth.
The ordinary domain and heap-indexed accumulator relation imply its original
function precondition; no representation is required to be uniquely encoded. -/
theorem CalleeResources.of_functionRealizable
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {domain : α → CellValue kind → Prop}
    {functionPre : Env signatures[fn].params → Heap → Prop}
    {w heapLimit depth : Nat}
    (realizable : FunctionRealizable program w depth fn functionPre)
    (input : ∀ a actual head heap, domain a head → representation.Rel a actual heap →
      functionPre (cast (congrArg (fun s => Env s.params) same.symm)
        (Complexity.Language.List.Fold.calleeArgs actual head)) heap) :
    CalleeResources program fn same representation domain w heapLimit depth (fun _ _ => 0) := by
  refine FunctionArenaResources.of_functionRealizable same realizable ?_
  intro x heap allowed
  exact input x.1 x.2.1 x.2.2 heap allowed.1 allowed.2

/-- Reuse the original two-argument callback's cost proof for the fold's same
source execution. Its mathematical bound can depend on the current accumulator
and head, while its original bound may also inspect actual arguments and heap. -/
theorem CalleeCostBound.of_functionCostBound
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {domain : α → CellValue kind → Prop}
    {realizationPre costPre : Env signatures[fn].params → Heap → Prop}
    {functionBound : Env signatures[fn].params → Heap → Nat}
    {bound : α → CellValue kind → Nat} {w heapLimit depth : Nat}
    (realizable : FunctionRealizable program w depth fn realizationPre)
    (bounded : FunctionCostBound program fn costPre functionBound)
    (realizationInput : ∀ a actual head heap,
      domain a head → representation.Rel a actual heap →
      realizationPre (cast (congrArg (fun s => Env s.params) same.symm)
        (Complexity.Language.List.Fold.calleeArgs actual head)) heap)
    (costInput : ∀ a actual head heap,
      domain a head → representation.Rel a actual heap →
      costPre (cast (congrArg (fun s => Env s.params) same.symm)
        (Complexity.Language.List.Fold.calleeArgs actual head)) heap)
    (bound_le : ∀ a actual head heap,
      domain a head → representation.Rel a actual heap →
      functionBound (cast (congrArg (fun s => Env s.params) same.symm)
        (Complexity.Language.List.Fold.calleeArgs actual head)) heap ≤ bound a head) :
    CalleeCostBound program fn same representation domain w heapLimit depth bound := by
  refine FunctionArenaCostBound.of_functionCostBound same realizable bounded ?_ ?_ ?_
  · intro x heap allowed
    exact realizationInput x.1 x.2.1 x.2.2 heap allowed.1 allowed.2
  · intro x heap allowed
    exact costInput x.1 x.2.1 x.2.2 heap allowed.1 allowed.2
  · intro x heap allowed
    exact bound_le x.1 x.2.1 x.2.2 heap allowed.1 allowed.2

end Ram.LanguageCompiler.List.Fold
