/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedList
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Resources
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Asymptotics
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic

/-!
# Allocating native list folds on RAM

The actual native `reverseAppend` calls the shared fold with the actual native
`ListReducer.push` callback. Each callback calls the shared list constructor and
retains three arena words. The existing source refinement supplies ordinary
`values.reverse ++ tail`; the existing fold resource theorem supplies traversal,
callback and allocation bounds for that same source implementation.

The complete invocation retains its real final memory, placement and cursor.
Original list roots remain observable, including shared tails. The reservation
bounds retained arena growth; it is not a claim about exact peak live space.
-/

namespace Complexity.Language.Examples.LinkedList

open Ram.LanguageCompiler

/-- The actual constructor call and native callback return, before the callback's
two initialization instructions. No cost is assigned to native list notation. -/
def pushBodySteps : Nat :=
  callCost ListReducer.Source.program
    (ListReducer.Source.imports.ListReducer.Operations.consNat.map.toFun
      ListReducer.Operations.consNat.consId)
    (Ram.LanguageCompiler.List.Cons.bodySteps .nat + 2) +
      (2 * fieldCount (.option (.node .nat)) + 2)

/-- The native callback reuses the constructor-call rule with its two arguments
in callback order. Its result shares the original tail in the actual new heap. -/
theorem push_ready_cost {w heapLimit cursor : Nat}
    (accumulator : Option (NodeRef .nat)) (head : Nat) (heap : Heap)
    (positive : 0 < w) (headFits : head < 2 ^ w)
    (space : cursor + 3 ≤ heapLimit) :
    ∃ execution : Exec ListReducer.Source.program
        (ListReducer.Source.program.body ListReducer.Source.pushId)
        ⟨ListReducer.Source.push_args accumulator head, heap⟩
        ⟨ListReducer.Source.push_args accumulator head, (heap.cons head accumulator).2⟩
        (.returned (some (heap.cons head accumulator).1)),
      ∃ ready : ArenaReady execution w heapLimit 1 cursor (cursor + 3),
        ArenaExecutionCost ready pushBodySteps := by
  obtain ⟨_, originalCost⟩ := Ram.LanguageCompiler.List.Cons.ready_cost
    .nat head accumulator heap (depth := 0) positive headFits space
  have measured : ArenaMeasured ListReducer.Source.program w heapLimit 1
      (ListReducer.Source.program.body ListReducer.Source.pushId)
      (fun finish control finalCursor steps =>
        finish = ⟨ListReducer.Source.push_args accumulator head,
          (heap.cons head accumulator).2⟩ ∧
        control = .returned (some (heap.cons head accumulator).1) ∧
        finalCursor = cursor + 3 ∧ steps = pushBodySteps)
      ⟨ListReducer.Source.push_args accumulator head, heap⟩ cursor := by
    ram_source_arena_call exact using originalCost
      via ListReducer.Source.imports.ListReducer.Operations.consNat.embedding
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨_, _, _, _, execution, ready, cost, rfl, rfl, rfl, rfl⟩ := measured
  exact ⟨execution, ready, cost⟩

/-- Each actual push reserves three words, independently of the length or sharing
of the represented accumulator. Its mathematical domain imposes no heap limit. -/
theorem push_fold_resources {w heapLimit : Nat} (positive : 0 < w) :
    Ram.LanguageCompiler.List.Fold.CalleeResources (kind := .nat)
      ListReducer.Source.program ListReducer.Source.pushId rfl
      (Representation.list .nat) (fun _ _ => True)
      w heapLimit 1 (fun _ _ => 3) := by
  rintro ⟨mathematical, accumulator, head⟩ heap cursor _ arguments space
    finish value execution
  obtain ⟨measured, ready, _⟩ :=
    push_ready_cost accumulator head heap positive (arguments (.there .here)) space
  obtain ⟨rfl, sameControl⟩ := measured.deterministic execution
  cases Control.returned.inj sameControl
  exact ⟨cursor + 3, ready, Nat.le_refl _⟩

/-- The callback's bound observes its existing call, allocation, copy and return
rules. It includes initialization once and needs no comparison heap or capacity
assumption beyond the readiness already supplied for the observed execution. -/
theorem push_fold_costBound (w heapLimit : Nat) :
    Ram.LanguageCompiler.List.Fold.CalleeCostBound (kind := .nat)
      ListReducer.Source.program ListReducer.Source.pushId rfl
      (Representation.list .nat) (fun _ _ => True)
      w heapLimit 1 (fun _ _ => pushBodySteps + 2) := by
  rintro ⟨mathematical, accumulator, head⟩ heap _ finish value execution
    cursor finalCursor ready steps cost
  cases cost with
  | callReturn calleeCost returnCost =>
      cases returnCost
      cases calleeCost with
      | consNode someCost =>
          cases someCost with
          | letPrim resultCost =>
              cases resultCost
              exact Nat.le_refl _

/-- The fold's complete callable-body bound is affine in the traversed list
length. Its coefficient uses the actual relocated callback and compiler costs. -/
def reverseAppendFoldBound (length : Nat) : Nat :=
  length * (pushBodySteps + 2 +
    callCost NativeLists.Operations.fold0.program
      (List.Fold.calleeEntry (.option (.node .nat)) .nat ListReducer.Source.pushId) 0 +
        2 * fieldCount (.option (.node .nat)) + 45) +
    (2 * fieldCount (.option (.node .nat)) + 23)

/-- Constant callback costs specialize the shared fold bound without proving
another traversal or pricing a native `List.foldl` operation. -/
theorem reverseAppendFoldBound_eq (initial values : List Nat) :
    Ram.LanguageCompiler.List.Fold.functionBound
      ListReducer.Source.program ListReducer.Source.pushId
      NativeLists.Operations.fold0.callback_signature ListReducer.push
      (fun _ _ => pushBodySteps + 2) initial values =
        reverseAppendFoldBound values.length := by
  simp only [Ram.LanguageCompiler.List.Fold.functionBound,
    Ram.LanguageCompiler.List.Fold.remainingCost_eq_sum,
    Ram.LanguageCompiler.List.Fold.accumulated_const, reverseAppendFoldBound,
    NativeLists.Operations.fold0.program, Nat.mul_add]
  omega

/-- The native wrapper pays its actual imported fold call and its own return. -/
def reverseAppendBodyBound (length : Nat) : Nat :=
  callCost NativeLists.Source.program
    (NativeLists.Source.imports.NativeLists.Operations.fold0.map.toFun
      NativeLists.Operations.fold0.foldId)
    (reverseAppendFoldBound length) + (2 * fieldCount (.option (.node .nat)) + 2)

/-- The complete native invocation adds its own initialization, outer call and
halt exactly once. The fold and callback bounds already include their own calls. -/
def reverseAppendInvocationBound (length : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl NativeLists.Source.program)
    (lowerFunc NativeLists.Source.program NativeLists.Source.reverseAppendId)
    (reverseAppendBodyBound length + 2) + 1

/-- The full invocation bound is affine, with a coefficient derived from the
actual callback body, linked call frame and shared fold traversal. -/
theorem reverseAppendInvocationBound_affine (length : Nat) :
    reverseAppendInvocationBound length =
      length * (pushBodySteps + 2 +
        callCost NativeLists.Operations.fold0.program
          (List.Fold.calleeEntry (.option (.node .nat)) .nat ListReducer.Source.pushId) 0 +
            2 * fieldCount (.option (.node .nat)) + 45) +
        reverseAppendInvocationBound 0 := by
  simp only [reverseAppendInvocationBound, reverseAppendBodyBound,
    reverseAppendFoldBound, callCost, Ram.LocalCompiler.Function.callSteps_eq,
    Nat.zero_mul]
  omega

/-- The actual generated caller composes the independently specified allocating
fold with its return. Readiness begins at the real current cursor, and the cost
and cursor bounds retain the same source execution throughout. -/
theorem reverseAppend_ready_cost {w heapLimit cursor : Nat}
    (values tailValues : List Nat) (root tail : Option (NodeRef .nat)) (heap : Heap)
    (positive : 0 < w)
    (observed : (Representation.list .nat).Rel values root heap)
    (tailObserved : (Representation.list .nat).Rel tailValues tail heap)
    (headFits : ∀ head ∈ values, head < 2 ^ w)
    (space : cursor + 3 * values.length ≤ heapLimit) :
    ∃ finish value finalCursor steps,
      ∃ execution : Exec NativeLists.Source.program
          (NativeLists.Source.program.body NativeLists.Source.reverseAppendId)
          ⟨NativeLists.Source.reverseAppend_args root tail, heap⟩ finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit 3 cursor finalCursor,
          ArenaExecutionCost ready steps ∧
          steps ≤ reverseAppendBodyBound values.length ∧
          finalCursor ≤ cursor + 3 * values.length := by
  have admissible : List.Fold.Admissible (kind := .nat) ListReducer.push
      (fun _ _ => True) tailValues values := by
    intro processed head suffix partition
    trivial
  have capacity : cursor + Ram.LanguageCompiler.List.Fold.accumulated (kind := .nat)
      ListReducer.push (fun _ _ => 3) tailValues values ≤ heapLimit := by
    rw [Ram.LanguageCompiler.List.Fold.accumulated_const]
    omega
  obtain ⟨finalAcc, finalHeap, finalCursor, steps, execution, ready, cost,
      coreBound, cursorBound⟩ := Ram.LanguageCompiler.List.Fold.measured
    NativeLists.Operations.fold0.callback_contract
    (push_fold_resources positive) (push_fold_costBound w heapLimit)
    tailValues values tail root heap cursor positive admissible tailObserved
    (ValueFits.option_node positive tail) headFits capacity observed
  rw [reverseAppendFoldBound_eq] at coreBound
  rw [Ram.LanguageCompiler.List.Fold.accumulated_const,
    Nat.mul_comm values.length 3] at cursorBound
  apply ArenaMeasured.exists_returned_iff.mp
  ram_source_arena_call exact using cost
    via NativeLists.Source.imports.NativeLists.Operations.fold0.embedding
  exact ⟨_, rfl, Nat.add_le_add_right (callCost_mono _ _ coreBound) _, cursorBound⟩

/-- The actual native `reverseAppend` halts with its ordinary mathematical
result. The original lists remain observable in the same extended heap, and the
returned execution carries the complete final RAM memory for subsequent calls.
No copying of the original tail or disjointness of the two input roots is needed.

Finite-word ranges of traversed heads come from the actual launch heap. The only
additional arena allowance is three words per traversed element; the full time
bound includes all three internal call levels and the final outer halt. -/
theorem reverseAppend_execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (values tailValues : List Nat) (root tail : Option (NodeRef .nat)) {heap : Heap}
    (observed : (Representation.list .nat).Rel values root heap)
    (tailObserved : (Representation.list .nat).Rel tailValues tail heap)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch NativeLists.Source.program NativeLists.Source.reverseAppendId
      3 heapLimit placement (NativeLists.Source.reverseAppend_args root tail) heap cursor entry)
    (space : cursor + 3 * values.length ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution NativeLists.Source.program
        NativeLists.Source.reverseAppendId 3 heapLimit placement
        (NativeLists.Source.reverseAppend_args root tail) heap entry,
      (Representation.list .nat).Rel (values.reverse ++ tailValues) outcome.value outcome.heap ∧
      (Representation.list .nat).Rel values root outcome.heap ∧
      (Representation.list .nat).Rel tailValues tail outcome.heap ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.cursor ≤ cursor + 3 * values.length ∧
      outcome.bodySteps ≤ reverseAppendBodyBound values.length + 2 ∧
      outcome.result.steps ≤ reverseAppendInvocationBound values.length := by
  have headFits := Ram.LanguageCompiler.List.Fold.contents_valueFits
    launch.arena.heapRep observed
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, stepBound, cursorBound⟩ :=
    reverseAppend_ready_cost values tailValues root tail heap launch.positive
      observed tailObserved headFits space
  obtain ⟨outcome, _, heapEq, cursorEq, bodyEq⟩ :=
    cost.execute (fn := NativeLists.Source.reverseAppendId) launch
  have represented := outcome.post
    (NativeLists.reverseAppend_refines (values, tailValues) trivial) ⟨observed, tailObserved⟩
  have result : (Representation.list .nat).Rel (values.reverse ++ tailValues)
      outcome.value outcome.heap := by
    change (Representation.list .nat).Rel (NativeLists.reverseAppend values tailValues)
      outcome.value outcome.heap at represented
    simpa only [reverseAppend_eq] using represented
  have shape : heap.ShapeExtends outcome.heap := by
    rw [heapEq]
    exact execution.heap_shapeExtends
  have bodyBound : outcome.bodySteps ≤ reverseAppendBodyBound values.length + 2 := by
    rw [bodyEq]
    exact Nat.add_le_add_right stepBound 2
  refine ⟨outcome, result, Representation.list_mono observed shape,
    Representation.list_mono tailObserved shape, shape, ?_, bodyBound, ?_⟩
  · simpa only [cursorEq] using cursorBound
  · rw [outcome.steps_eq]
    exact Nat.add_le_add_right
      (Ram.LocalCompiler.Function.callSteps_mono _ _ bodyBound) 1

end Complexity.Language.Examples.LinkedList
