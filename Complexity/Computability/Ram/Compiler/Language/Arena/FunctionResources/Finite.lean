/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources

/-!
# Reusing finite-word function proofs as arena contracts

An existing `FunctionRealizable` proof supplies zero-growth arena readiness for
the same source invocation. Its independent `FunctionCostBound` transfers along
the equality of the existing compiler cost observations. No new execution or
cost model is introduced, and heap writes remain permitted.

The argument index is arbitrary. It can retain mathematical values and their
actual heap representations without selecting a unique encoding. Whole-signature
transport connects the selected body to the original function's proofs, including
functions whose range and cost preconditions differ.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- Reuse an existing function realization for an indexed family of actual
arguments. Determinism identifies the supplied source invocation; the arena
cursor is unchanged, without requiring the heap itself to be unchanged. -/
theorem FunctionArenaResources.of_functionRealizable
    {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {selected : Signature} (same : signatures[fn] = selected)
    {args : X → Env selected.params} {pre : X → Heap → Prop}
    {functionPre : Env signatures[fn].params → Heap → Prop}
    {w heapLimit depth : Nat}
    (realizable : FunctionRealizable program w depth fn functionPre)
    (input : ∀ x heap, pre x heap → functionPre
      (cast (congrArg (fun s => Env s.params) same.symm) (args x)) heap) :
    FunctionArenaResources program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) args pre w heapLimit depth (fun _ => 0) := by
  cases same
  intro x heap cursor allowed _ _ finish value execution
  obtain ⟨otherFinish, otherValue, realized⟩ :=
    realizable (args x) heap (input x heap allowed)
  obtain ⟨rfl, sameControl⟩ := realized.erase.deterministic execution
  cases Control.returned.inj sameControl
  exact ⟨cursor, realized.arenaReady heapLimit cursor, Nat.le_refl _⟩

/-- Transfer the original function's cost bound to the same arena execution.
Realizability and cost may use different preconditions, and a bound on concrete
arguments may be compared with the caller's mathematical indexed bound. -/
theorem FunctionArenaCostBound.of_functionCostBound
    {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {selected : Signature} (same : signatures[fn] = selected)
    {args : X → Env selected.params} {pre : X → Heap → Prop}
    {realizationPre costPre : Env signatures[fn].params → Heap → Prop}
    {functionBound : Env signatures[fn].params → Heap → Nat} {bound : X → Nat}
    {w heapLimit depth : Nat}
    (realizable : FunctionRealizable program w depth fn realizationPre)
    (bounded : FunctionCostBound program fn costPre functionBound)
    (realizationInput : ∀ x heap, pre x heap → realizationPre
      (cast (congrArg (fun s => Env s.params) same.symm) (args x)) heap)
    (costInput : ∀ x heap, pre x heap → costPre
      (cast (congrArg (fun s => Env s.params) same.symm) (args x)) heap)
    (bound_le : ∀ x heap, pre x heap → functionBound
      (cast (congrArg (fun s => Env s.params) same.symm) (args x)) heap ≤ bound x) :
    FunctionArenaCostBound program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) args pre w heapLimit depth bound := by
  cases same
  intro x heap allowed finish value execution cursor finalCursor ready steps cost
  obtain ⟨otherFinish, otherValue, realized⟩ :=
    realizable (args x) heap (realizationInput x heap allowed)
  obtain ⟨otherSteps, otherCost⟩ := realized.exists_cost
  have stepEq : steps = otherSteps := cost.deterministic (otherCost.arena heapLimit cursor)
  have stepBound := bounded (args x) heap (costInput x heap allowed) realized otherCost
  simpa only [stepEq] using stepBound.trans (bound_le x heap allowed)

end Ram.LanguageCompiler
