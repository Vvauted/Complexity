/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Function
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Models
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Node
import Complexity.Language.List.Fold.Native

/-!
# Bounding the actual list-fold execution

Callback cost certificates bound the already supplied arena execution. Unlike
constructing a ready execution, this implication needs no callback resources,
head ranges, positive word width or spare allocation capacity. Its mathematical
inputs retain the existing accumulator representation, list contents and domain.

The shared loop rule carries the mathematical accumulator and remaining list as
a ghost index. Existing source correctness supplies each transition's represented
result at the actual new heap. There is no decoder, comparison execution at a
different cursor, or second induction over the traversal.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- The guard's existing two branch counts bound its supplied execution without
constructing readiness or imposing a word-width hypothesis. -/
theorem guard_costBound (program : Complexity.Language.Program signatures)
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    {w heapLimit depth : Nat} :
    StmtArenaCostBound program w heapLimit depth (Complexity.Language.List.Fold.guard accTy kind)
      (Complexity.Language.List.Fold.state accumulator root heap)
      (if root.isSome then 9 else 6) := by
  cases root with
  | none => exact StmtArenaCostBound.match_none rfl (StmtArenaCostBound.ret (.bool false) _)
  | some ref =>
      exact StmtArenaCostBound.match_some (payload := ref) rfl
        (StmtArenaCostBound.ret (.bool true) _)

/-- Bound one actual node read, callback and local update using only the
callback's cost contract at the represented input. No callback execution is
constructed, and allocation readiness is already part of the observed cost. -/
theorem iteration_costBound
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {domain : α → CellValue kind → Prop}
    {w heapLimit depth : Nat} {bound : α → CellValue kind → Nat}
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (accumulator : Value accTy) (ref : NodeRef kind)
    (head : CellValue kind) (tail : Option (NodeRef kind)) (heap : Heap)
    (allowed : domain mathematical head)
    (related : representation.Rel mathematical accumulator heap)
    (found : heap.node? kind ref.object = some (head, tail)) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.iteration fn same)
      (Complexity.Language.List.Fold.state accumulator (some ref) heap)
      (callCost program fn (bound mathematical head) + 2 * fieldCount accTy + 26) := by
  let derived : { steps : Nat // StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.iteration fn same)
      (Complexity.Language.List.Fold.state accumulator (some ref) heap) steps } := ⟨_, by
    apply StmtArenaCostBound.match_some rfl
    apply StmtArenaCostBound.readNode_of_success
    intro actualHead actualTail actualFound
    change heap.node? kind ref.object = some (actualHead, actualTail) at actualFound
    have identified := Prod.mk.inj (Option.some.inj (actualFound.symm.trans found))
    rcases identified with ⟨headEq, tailEq⟩
    subst actualHead
    subst actualTail
    apply StmtArenaCostBound.letPrim
    apply StmtArenaCostBound.call_at_of_eq same bounded (mathematical, accumulator, head)
      rfl ⟨allowed, related⟩
    intro returned finalHeap
    apply StmtArenaCostBound.seq
    · exact StmtArenaCostBound.assign _ _ _
    · intro middle
      exact StmtArenaCostBound.assign _ _ _⟩
  apply StmtArenaCostBound.mono derived.property
  have scalarWidth : fieldCount kind.toTy = 1 := by cases kind <;> rfl
  dsimp only [derived]
  simp only [primCodeSize, readNodeCodeSize, scalarWidth, fieldCount]
  omega

/-- The shared potential rule follows the actual loop and its changing heap.
Existing iteration correctness updates the ghost accumulator and suffix;
the cost argument does not repeat the list or execution induction. -/
theorem loop_costBound
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {bound : α → CellValue kind → Nat}
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (observed : NodeRef.Contents heap root values) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.loop fn same)
      (Complexity.Language.List.Fold.state accumulator root heap)
      (remainingCost program fn accTy step bound mathematical values + 17) := by
  refine StmtArenaCostBound.while_model
    (model := (mathematical, values)) (locals := (accumulator, root)) (heap := heap)
    Complexity.Language.List.Fold.loopView program
    (Complexity.Language.List.Fold.guard accTy kind)
    (Complexity.Language.List.Fold.iteration fn same)
    (Complexity.Language.List.Fold.loopModelRel representation step domain)
    Complexity.Language.List.Fold.loopTest (Complexity.Language.List.Fold.loopNext step)
    (Complexity.Language.List.Fold.guard_model_contract program representation step domain)
    (Complexity.Language.List.Fold.iteration_model_contract correct)
    (fun _ => True) (fun _ _ _ => trivial)
    (fun index => if index.2.isEmpty then 6 else 9)
    (fun index => match index.2 with
      | [] => 0
      | head :: _ => callCost program fn (bound index.1 head) + 2 * fieldCount accTy + 26)
    (fun index => remainingCost program fn accTy step bound index.1 index.2 + 17)
    ?_ ?_ ?_ ?_ trivial ⟨allowed, related, observed⟩
  · rintro ⟨initial, rest⟩ ⟨acc, current⟩ currentHeap _ ⟨_, _, contents⟩
    cases contents with
    | nil => exact guard_costBound program acc none currentHeap
    | cons found contents => exact guard_costBound program acc _ currentHeap
  · rintro ⟨initial, rest⟩ ⟨acc, current⟩ currentHeap _ active
      ⟨admissible, related, contents⟩
    cases contents with
    | nil => simp [Complexity.Language.List.Fold.loopTest] at active
    | @cons ref head tail rest found contents =>
        exact iteration_costBound bounded initial acc ref head tail currentHeap
          ((Complexity.Language.List.Fold.admissible_cons step domain initial head rest).mp
            admissible).1 related found
  · rintro ⟨initial, rest⟩ _ stopped
    cases rest with
    | nil => exact Nat.le_refl _
    | cons head rest => simp [Complexity.Language.List.Fold.loopTest] at stopped
  · rintro ⟨initial, rest⟩ _ active
    cases rest with
    | nil => simp [Complexity.Language.List.Fold.loopTest] at active
    | cons head rest =>
        change 9 + (callCost program fn (bound initial head) + 2 * fieldCount accTy + 26) +
            (remainingCost program fn accTy step bound (step initial head) rest + 17) + 10 ≤
          remainingCost program fn accTy step bound initial (head :: rest) + 17
        simp only [remainingCost, accumulated]
        omega

/-- Returning the actual accumulated value adds only the existing sequence
check and return copies to the loop certificate. -/
theorem body_costBound
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {bound : α → CellValue kind → Nat}
    (bounded : CalleeCostBound program fn same representation domain w heapLimit depth bound)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (observed : NodeRef.Contents heap root values) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.body fn same)
      (Complexity.Language.List.Fold.state accumulator root heap)
      (remainingCost program fn accTy step bound mathematical values + 2 * fieldCount accTy + 21) := by
  have loopBound : StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.loop fn same)
      (Complexity.Language.List.Fold.state accumulator root heap)
      (remainingCost program fn accTy step bound mathematical values + 17) := by
    intro finish control execution cursor finalCursor ready steps cost
    exact loop_costBound correct bounded mathematical values accumulator root heap
      allowed related observed execution ready cost
  have seqBound : StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.body fn same)
      (Complexity.Language.List.Fold.state accumulator root heap)
      (remainingCost program fn accTy step bound mathematical values + 17 +
        max (2 + (2 * fieldCount accTy + 2)) 3) := by
    exact StmtArenaCostBound.seq loopBound
      (fun middle => StmtArenaCostBound.ret (.var .here) middle)
  intro finish control execution cursor finalCursor ready steps cost
  exact Nat.le_trans (seqBound execution ready cost) (by omega)

/-- The callable fold's existing bound follows from the supplied actual
execution and callback costs. Allocation resources, finite-word ranges and
initial capacity are absent from this independent cost contract. -/
theorem functionCostBound_of_actual
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract
      sourceProgram fn same representation step domain)
    {w heapLimit depth : Nat} {bound : α → CellValue kind → Nat}
    (bounded : CalleeCostBound sourceProgram fn same representation domain w heapLimit depth bound) :
    FunctionArenaCostBound (Complexity.Language.List.Fold.program sourceProgram fn same)
      ((Complexity.Language.List.Fold.program sourceProgram fn same).body
        (Complexity.Language.List.Fold.entry accTy kind signatures))
      functionArgs (functionCostPre representation step domain) w heapLimit (depth + 1)
      (fun input => functionBound sourceProgram fn same step bound input.1 input.2.1) := by
  have embedded := Complexity.Language.List.Fold.program_embeds sourceProgram fn same
  have relocated :
      Complexity.Language.List.Fold.calleeBody
        (Complexity.Language.List.Fold.program sourceProgram fn same)
        (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
        (Complexity.Language.List.Fold.callee_signature same) =
      (Complexity.Language.List.Fold.calleeBody sourceProgram fn same).renameCalls
        (Complexity.Language.List.Fold.calleeMap accTy kind signatures) :=
    Complexity.Language.List.Fold.calleeBody_renameCalls embedded same
  have linkedBounded : CalleeCostBound
      (Complexity.Language.List.Fold.program sourceProgram fn same)
      (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
      (Complexity.Language.List.Fold.callee_signature same)
      representation domain w heapLimit depth bound := by
    unfold CalleeCostBound
    rw [relocated]
    exact FunctionArenaCostBound.renameCalls bounded embedded
  rintro ⟨mathematical, values, accumulator, root⟩ heap ⟨allowed, related, observed⟩
    finish value execution cursor finalCursor ready steps cost
  have bodyBound : StmtArenaCostBound
      (Complexity.Language.List.Fold.program sourceProgram fn same) w heapLimit (depth + 1)
      (Complexity.Language.List.Fold.body
        (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
        (Complexity.Language.List.Fold.callee_signature same))
      (Complexity.Language.List.Fold.state accumulator root heap)
      (remainingCost (Complexity.Language.List.Fold.program sourceProgram fn same)
        (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
        accTy step bound mathematical values + 2 * fieldCount accTy + 21) := by
    intro finish control execution cursor finalCursor ready steps cost
    exact body_costBound
      (Complexity.Language.List.Fold.callee_contract sourceProgram fn same correct)
      linkedBounded mathematical values accumulator root heap allowed related observed
      execution ready cost
  rw [← Complexity.Language.List.Fold.program_body sourceProgram fn same] at bodyBound
  have actualBound := bodyBound execution ready cost
  change steps + 2 ≤ functionBound sourceProgram fn same step bound mathematical values
  unfold functionBound
  omega

end Ram.LanguageCompiler.List.Fold
