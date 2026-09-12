/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedList
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Resources
import Complexity.Computability.Ram.Compiler.Language.List.Fold.CostBound
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Asymptotics
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.FunctionExecution

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

/-- Infer the actual callback's constructor call and return costs from its body,
using the constructor's independent cost certificate. -/
def pushCost : { bound : Nat // ∀ w heapLimit initial,
    StmtArenaCostBound ListReducer.Source.program w heapLimit 1
      (ListReducer.Source.program.body ListReducer.Source.pushId) initial bound } := by
  ram_source_arena_cost [(Ram.LanguageCompiler.List.Cons.arenaCostBound .nat _ _ 0)
    via ListReducer.Source.imports.ListReducer.Operations.consNat.embedding]

/-- The callback's inferred body count, before its two initialization instructions.
Its exact equality is established by the measured execution below. -/
def pushBodySteps : Nat := pushCost.val

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
  exact Nat.add_le_add_right (pushCost.property w heapLimit _ execution ready cost) 2

/-- The fold's complete callable-body bound is affine in the traversed list
length. Its coefficient uses the actual relocated callback and compiler costs. -/
def reverseAppendFoldBound (length : Nat) : Nat :=
  Ram.LanguageCompiler.List.Fold.linearFunctionBound
    ListReducer.Source.program ListReducer.Source.pushId
    NativeLists.Operations.fold0.callback_signature (pushBodySteps + 2) length

/-- Constant callback costs specialize the shared fold bound without proving
another traversal or pricing a native `List.foldl` operation. -/
theorem reverseAppendFoldBound_eq (initial values : List Nat) :
    Ram.LanguageCompiler.List.Fold.functionBound
      ListReducer.Source.program ListReducer.Source.pushId
      NativeLists.Operations.fold0.callback_signature ListReducer.push
      (fun _ _ => pushBodySteps + 2) initial values =
        reverseAppendFoldBound values.length := by
  exact Ram.LanguageCompiler.List.Fold.functionBound_const
    ListReducer.Source.program ListReducer.Source.pushId
    NativeLists.Operations.fold0.callback_signature ListReducer.push
    (pushBodySteps + 2) initial values

/-- The fold's existing affine bound at a fixed mathematical input length.
Only the represented input and callback domain occur in its precondition;
readiness and spare capacity are not needed to bound an already given execution. -/
theorem reverseAppendFold_costBound (w heapLimit length : Nat) :
    FunctionArenaCostBound NativeLists.Operations.fold0.program
      (NativeLists.Operations.fold0.program.body NativeLists.Operations.fold0.foldId)
      List.Fold.functionArgs
      (fun input heap =>
        List.Fold.functionCostPre (Representation.list .nat) ListReducer.push
          (fun _ _ => True) input heap ∧ input.2.1.length = length)
      w heapLimit 2 (fun _ => reverseAppendFoldBound length) := by
  intro input heap allowed finish value execution cursor finalCursor ready steps cost
  have bounded := List.Fold.functionCostBound_of_actual
    NativeLists.Operations.fold0.callback_contract (push_fold_costBound w heapLimit)
    input heap allowed.1 finish value execution ready cost
  dsimp only at bounded
  rw [reverseAppendFoldBound_eq, allowed.2] at bounded
  exact bounded

/-- Infer the native wrapper's bound from a length-indexed fold certificate.
The mathematical inputs select that certificate; only the two roots are passed
to the real source function. No wrapper call-table or field-count formula is supplied. -/
def reverseAppendCost (length : Nat) : { bound : Nat //
    ∀ w heapLimit (values tailValues : List Nat) (root tail : Option (NodeRef .nat)) (heap : Heap),
      values.length = length → (Representation.list .nat).Rel values root heap →
      (Representation.list .nat).Rel tailValues tail heap →
      StmtArenaCostBound NativeLists.Source.program w heapLimit 3
        (NativeLists.Source.program.body NativeLists.Source.reverseAppendId)
        ⟨NativeLists.Source.reverseAppend_args root tail, heap⟩ bound } :=
  ⟨_, by
    intro w heapLimit values tailValues root tail heap lengthEq observed tailObserved
    have allowed :
        List.Fold.functionCostPre (kind := .nat) (Representation.list .nat) ListReducer.push
          (fun _ _ => True) (tailValues, values, tail, root) heap ∧ values.length = length :=
      ⟨⟨fun _ _ _ _ => trivial, tailObserved, observed⟩, lengthEq⟩
    ram_source_arena_cost [(reverseAppendFold_costBound w heapLimit length)
      at (tailValues, values, tail, root)
      via NativeLists.Source.imports.NativeLists.Operations.fold0.embedding]⟩

/-- The native wrapper's inferred length-dependent body bound. -/
def reverseAppendBodyBound (length : Nat) : Nat := (reverseAppendCost length).val

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
    reverseAppendCost, reverseAppendFoldBound, Ram.LanguageCompiler.List.Fold.linearFunctionBound,
    NativeLists.Operations.fold0.program, callCost, Ram.LocalCompiler.Function.callSteps_eq,
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
      _coreBound, cursorBound⟩ := Ram.LanguageCompiler.List.Fold.measured
    NativeLists.Operations.fold0.callback_contract
    (push_fold_resources positive) (push_fold_costBound w heapLimit)
    tailValues values tail root heap cursor positive admissible tailObserved
    (ValueFits.option_node positive tail) headFits capacity observed
  rw [Ram.LanguageCompiler.List.Fold.accumulated_const,
    Nat.mul_comm values.length 3] at cursorBound
  have measured : ArenaMeasured NativeLists.Source.program w heapLimit 3
      (NativeLists.Source.program.body NativeLists.Source.reverseAppendId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor ≤ cursor + 3 * values.length)
      ⟨NativeLists.Source.reverseAppend_args root tail, heap⟩ cursor := by
    ram_source_arena_call exact using cost
      via NativeLists.Source.imports.NativeLists.Operations.fold0.embedding
    exact ⟨_, rfl, cursorBound⟩
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, cursorBound⟩ :=
    ArenaMeasured.exists_returned_iff.mp measured
  exact ⟨finish, value, finalCursor, steps, execution, ready, cost,
    (reverseAppendCost values.length).property w heapLimit values tailValues root tail heap
      rfl observed tailObserved execution ready cost, cursorBound⟩

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
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, _stepBound, cursorBound⟩ :=
    reverseAppend_ready_cost values tailValues root tail heap launch.positive
      observed tailObserved headFits space
  have measured : ArenaMeasured NativeLists.Source.program w heapLimit 3
      (NativeLists.Source.program.body NativeLists.Source.reverseAppendId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor ≤ cursor + 3 * values.length)
      ⟨NativeLists.Source.reverseAppend_args root tail, heap⟩ cursor :=
    ArenaMeasured.exists_returned_iff.mpr
      ⟨finish, value, finalCursor, steps, execution, ready, cost, cursorBound⟩
  obtain ⟨outcome, cursorBound, represented, shape, bodyBound, stepsBound⟩ :=
    measured.execute_le (P := fun _ _ finalCursor => finalCursor ≤ cursor + 3 * values.length)
      ((reverseAppendCost values.length).property w heapLimit values tailValues root tail heap
        rfl observed tailObserved)
      (NativeLists.reverseAppend_refines (values, tailValues) trivial) launch
      ⟨observed, tailObserved⟩
  have result : (Representation.list .nat).Rel (values.reverse ++ tailValues)
      outcome.value outcome.heap := by
    change (Representation.list .nat).Rel (NativeLists.reverseAppend values tailValues)
      outcome.value outcome.heap at represented
    simpa only [reverseAppend_eq] using represented
  exact ⟨outcome, result, Representation.list_mono observed shape,
    Representation.list_mono tailObserved shape, shape, cursorBound, bodyBound, stepsBound⟩

/-- Reuse the actual reverse/append wrapper's inferred bound as a callable
certificate. Only its mathematical input length and current list observations
select the certificate; the arguments remain the two actual roots. -/
theorem reverseAppend_costBound (w heapLimit length : Nat) :
    FunctionArenaCostBound NativeLists.Source.program
      (NativeLists.Source.program.body NativeLists.Source.reverseAppendId)
      (fun input : List Nat × List Nat × Option (NodeRef .nat) × Option (NodeRef .nat) =>
        NativeLists.Source.reverseAppend_args input.2.2.1 input.2.2.2)
      (fun input heap => input.1.length = length ∧
        (Representation.list .nat).Rel input.1 input.2.2.1 heap ∧
        (Representation.list .nat).Rel input.2.1 input.2.2.2 heap)
      w heapLimit 3 (fun _ => reverseAppendBodyBound length + 2) := by
  rintro ⟨values, tailValues, root, tail⟩ heap ⟨lengthEq, observed, tailObserved⟩
    finish value execution cursor finalCursor ready steps cost
  exact Nat.add_le_add_right
    ((reverseAppendCost length).property w heapLimit values tailValues root tail heap
      lengthEq observed tailObserved execution ready cost) 2

/-- Infer the actual `reverse` wrapper's body bound from its call to
`reverseAppend`. Constructing its empty tail, returning the result and the
existing call-frame work are all supplied by structural compiler rules. -/
def reverseCost (length : Nat) : { bound : Nat //
    ∀ w heapLimit (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap),
      values.length = length → (Representation.list .nat).Rel values root heap →
      StmtArenaCostBound NativeLists.Source.program w heapLimit 4
        (NativeLists.Source.program.body NativeLists.Source.reverseId)
        ⟨NativeLists.Source.reverse_args root, heap⟩ bound } :=
  ⟨_, by
    intro w heapLimit values root heap lengthEq observed
    have allowed : values.length = length ∧
        (Representation.list .nat).Rel values root heap ∧
        (Representation.list .nat).Rel [] none heap :=
      ⟨lengthEq, observed, Representation.list_nil .nat heap⟩
    ram_source_arena_cost [(reverseAppend_costBound w heapLimit length)
      at (values, [], root, none)]⟩

/-- The existing native `reverse` is available to later source calls through
its inferred length-dependent bound, including initialization exactly once. -/
theorem reverse_costBound (w heapLimit length : Nat) :
    FunctionArenaCostBound NativeLists.Source.program
      (NativeLists.Source.program.body NativeLists.Source.reverseId)
      (fun input : List Nat × Option (NodeRef .nat) =>
        NativeLists.Source.reverse_args input.2)
      (fun input heap => input.1.length = length ∧
        (Representation.list .nat).Rel input.1 input.2 heap)
      w heapLimit 4 (fun _ => (reverseCost length).val + 2) := by
  rintro ⟨values, root⟩ heap ⟨lengthEq, observed⟩
    finish value execution cursor finalCursor ready steps cost
  exact Nat.add_le_add_right
    ((reverseCost length).property w heapLimit values root heap lengthEq observed
      execution ready cost) 2

/-- Execute the actual native `reverse` around the already measured
reverse/append call. The real result, final heap and cursor are available to a
subsequent caller; no list traversal or source-correctness proof is repeated. -/
theorem reverse_ready_cost {w heapLimit cursor : Nat}
    (values : List Nat) (root : Option (NodeRef .nat)) (heap : Heap)
    (positive : 0 < w)
    (observed : (Representation.list .nat).Rel values root heap)
    (headFits : ∀ head ∈ values, head < 2 ^ w)
    (space : cursor + 3 * values.length ≤ heapLimit) :
    ∃ finish value finalCursor steps,
      ∃ execution : Exec NativeLists.Source.program
          (NativeLists.Source.program.body NativeLists.Source.reverseId)
          ⟨NativeLists.Source.reverse_args root, heap⟩ finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit 4 cursor finalCursor,
          ArenaExecutionCost ready steps ∧ steps ≤ (reverseCost values.length).val ∧
          finalCursor ≤ cursor + 3 * values.length := by
  obtain ⟨_, _, _, _, _, _, cost, _, cursorBound⟩ :=
    reverseAppend_ready_cost values [] root none heap positive observed
      (Representation.list_nil .nat heap) headFits space
  have measured : ArenaMeasured NativeLists.Source.program w heapLimit 4
      (NativeLists.Source.program.body NativeLists.Source.reverseId)
      (fun _ control finalCursor _ =>
        ∃ value, control = .returned value ∧ finalCursor ≤ cursor + 3 * values.length)
      ⟨NativeLists.Source.reverse_args root, heap⟩ cursor := by
    ram_source_arena_step
    ram_source_arena_call exact using cost
    exact ⟨_, rfl, cursorBound⟩
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, cursorBound⟩ :=
    ArenaMeasured.exists_returned_iff.mp measured
  exact ⟨finish, value, finalCursor, steps, execution, ready, cost,
    (reverseCost values.length).property w heapLimit values root heap rfl observed
      execution ready cost, cursorBound⟩

end Complexity.Language.Examples.LinkedList
