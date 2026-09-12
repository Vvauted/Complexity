/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop

/-!
# Arena readiness of linked-list folding

The source fold already supplies a finite execution. The shared indexed loop
rule lifts that execution while threading callback allocations, represented
accumulators and immutable suffixes through the actual intermediate heaps.
Readiness requires the callbacks' resource certificates, not instruction bounds
or a second termination proof. Cost certificates can subsequently bound this
same execution.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- One actual read and callback invocation preserve the captured tail and
thread the callback's real accumulator, heap and arena cursor. -/
theorem iteration_ready
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (mathematical : α) (accumulator : Value accTy) (ref : NodeRef kind)
    (head : CellValue kind) (tail : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w) (allowed : domain mathematical head)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator) (headFits : ValueFits w (kind.toValue head))
    (found : heap.node? kind ref.object = some (head, tail))
    (capacity : cursor + reserve mathematical head ≤ heapLimit) :
    ∃ finalAcc finalHeap finalCursor,
      ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.List.Fold.iteration fn same)
        (Complexity.Language.List.Fold.state accumulator (some ref) heap)
        (Complexity.Language.List.Fold.state finalAcc tail finalHeap) .normal,
      ∃ _ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        finalCursor ≤ cursor + reserve mathematical head ∧
        representation.Rel (step mathematical head) finalAcc finalHeap ∧
        ValueFits w finalAcc ∧ heap.ShapeExtends finalHeap := by
  obtain ⟨calleeFinish, returned, invocation, resultRelated, preserved⟩ :=
    correct.invocation mathematical accumulator head heap allowed related
  have arguments : EnvFits w (calleeArgs (mathematical, accumulator, head)) :=
    EnvFits.cons (τ := accTy)
      (EnvFits.cons (τ := kind.toTy) (EnvFits.empty w) (kind.toValue head) headFits)
      accumulator accFits
  obtain ⟨finalCursor, calleeReady, cursorBound⟩ :=
    resources (mathematical, accumulator, head) heap cursor ⟨allowed, related⟩
      arguments capacity _ _ invocation
  have returnedFits : ValueFits w returned := calleeReady.outcome_fits
  have tailFits : ValueFits w (τ := .option (.node kind)) tail := by
    cases tail with
    | none => trivial
    | some next => exact ⟨Nat.one_lt_two_pow (Nat.ne_of_gt positive), trivial⟩
  have pairFits : ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail) := ⟨headFits, tailFits⟩
  let initial := Complexity.Language.List.Fold.state accumulator (some ref) heap
  let beforeRead := Complexity.Language.State.cons (τ := .node kind) ref initial
  let afterRead := Complexity.Language.State.cons
    (τ := .prod kind.toTy (.option (.node kind))) (kind.toValue head, tail) beforeRead
  let beforeCall := Complexity.Language.State.cons (τ := kind.toTy) (kind.toValue head) afterRead
  let afterCall := Complexity.Language.State.cons (τ := accTy) returned
    ⟨beforeCall.locals, calleeFinish.heap⟩
  let accVar : Var [accTy, kind.toTy, .prod kind.toTy (.option (.node kind)),
      .node kind, accTy, .option (.node kind)] accTy :=
    .there (.there (.there (.there .here)))
  let rootVar : Var [accTy, kind.toTy, .prod kind.toTy (.option (.node kind)),
      .node kind, accTy, .option (.node kind)] (.option (.node kind)) :=
    .there (.there (.there (.there (.there .here))))
  let store := Complexity.Language.Exec.assign (program := program) (result := accTy)
    accVar (.atom (.var .here)) afterCall
  let afterStore := afterCall.set accVar returned
  let advance := Complexity.Language.Exec.assign (program := program) (result := accTy)
    rootVar (.snd (.var (.there (.there .here)))) afterStore
  let execution : Complexity.Language.Exec program
      (Complexity.Language.List.Fold.iteration fn same)
      (Complexity.Language.List.Fold.state accumulator (some ref) heap)
      (Complexity.Language.List.Fold.state returned tail calleeFinish.heap) .normal :=
    .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref) rfl
      (.readNode (entry := beforeRead) (ref := .var .here) found
        (.letPrim (entry := afterRead) (value := .fst (.var .here))
          (Complexity.Language.Exec.callReturnOfEq same (entry := beforeCall)
            (args := .cons (.var (.there (.there (.there .here)))) (.cons (.var .here) .nil))
            invocation (.seqNormal store advance))))
  let storeReady : ArenaReady store w heapLimit (depth + 1) finalCursor finalCursor :=
    .assign accVar (.atom (.var .here)) afterCall returnedFits
  let advanceReady : ArenaReady advance w heapLimit (depth + 1) finalCursor finalCursor :=
    .assign rootVar (.snd (.var (.there (.there .here)))) afterStore pairFits
  let continuationReady := ArenaReady.seqNormal storeReady advanceReady
  let callReady := ArenaReady.callReturnOfEq same (entry := beforeCall)
    (args := .cons (.var (.there (.there (.there .here)))) (.cons (.var .here) .nil))
    arguments calleeReady continuationReady
  let headReady := ArenaReady.letPrim (entry := afterRead) (value := .fst (.var .here))
    pairFits callReady
  let readReady := ArenaReady.readNode (entry := beforeRead) (ref := .var .here)
    (found := found) pairFits headReady
  have refFits : ValueFits w (τ := .node kind) ref := trivial
  let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
    .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
      (selected := rfl) refFits readReady
  exact ⟨returned, calleeFinish.heap, finalCursor, execution, ready,
    cursorBound, resultRelated, returnedFits, preserved⟩

private def readyInvariant (representation : Representation α accTy)
    (step : α → CellValue kind → α) (domain : α → CellValue kind → Prop)
    (w : Nat) (reserve : α → CellValue kind → Nat) (limit : Nat)
    (index : α × _root_.List (CellValue kind))
    (entry : Complexity.Language.State [accTy, .option (.node kind)]) (cursor : Nat) : Prop :=
  ∃ accumulator root heap,
    entry = Complexity.Language.List.Fold.state accumulator root heap ∧
    Complexity.Language.List.Fold.Admissible step domain index.1 index.2 ∧
    representation.Rel index.1 accumulator heap ∧ NodeRef.Contents heap root index.2 ∧
    ValueFits w accumulator ∧
    (∀ head ∈ index.2, ValueFits w (kind.toValue head)) ∧
    cursor + accumulated step reserve index.1 index.2 ≤ limit

/-- Lift the independently proved finite source loop with a ghost accumulator
and suffix. The reservation envelope follows the actual callback cursors and
keeps every later node observation at the callback's actual final heap. -/
theorem loop_ready
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ∃ finalAcc finalHeap finalCursor,
      ∃ execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.loop fn same)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state finalAcc none finalHeap) .normal,
      ∃ _ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        finalCursor ≤ cursor + accumulated step reserve mathematical values ∧
        ValueFits w finalAcc := by
  obtain ⟨finish, control, execution, result⟩ :=
    Complexity.Language.List.Fold.loop_total correct mathematical values accumulator root heap
      allowed related observed
  cases control with
  | fault fault => exact False.elim result
  | returned value => exact False.elim result
  | normal =>
      obtain ⟨finalAcc, finalHeap, rfl, _finalRelated, _preserved⟩ := result
      have lifted : ∃ finalCursor,
          ArenaReady execution w heapLimit (depth + 1) cursor finalCursor ∧
          finalCursor ≤ cursor + accumulated step reserve mathematical values ∧
          ValueFits w finalAcc := by
        apply ArenaReady.while_of_exec_indexed
          (X := α × _root_.List (CellValue kind))
          (invariant := readyInvariant representation step domain w reserve
            (cursor + accumulated step reserve mathematical values))
          (guardPost := fun index state decision currentCursor =>
            readyInvariant representation step domain w reserve
              (cursor + accumulated step reserve mathematical values) index state currentCursor ∧
            decision = state.locals.tail.head.isSome)
          (post := fun state _ finalCursor =>
            finalCursor ≤ cursor + accumulated step reserve mathematical values ∧
            ValueFits w state.locals.head)
          (initialIndex := (mathematical, values)) execution
        · rintro ⟨initial, rest⟩ state currentCursor
            ⟨acc, current, currentHeap, rfl, admissible, accRelated, contents,
              currentFits, restFits, cursorBound⟩ afterGuard decision tested
          obtain ⟨guardExec, guardReady, _guardCost⟩ :=
            guard_measured program acc current currentHeap
              (depth := depth + 1) (cursor := currentCursor) positive
          obtain ⟨sameState, sameControl⟩ := guardExec.deterministic tested
          cases sameState
          cases Control.returned.inj sameControl
          refine ⟨currentCursor, guardReady, ?_, rfl⟩
          exact ⟨acc, current, currentHeap, rfl, admissible, accRelated, contents,
            currentFits, restFits, cursorBound⟩
        · rintro ⟨initial, rest⟩ state currentCursor
            ⟨⟨acc, current, currentHeap, rfl, admissible, accRelated, contents,
              currentFits, restFits, cursorBound⟩, selected⟩ afterBody outcome iterated
          change true = current.isSome at selected
          cases contents with
          | nil => simp at selected
          | @cons ref head tail rest found contents =>
              obtain ⟨headAllowed, restAllowed⟩ :=
                (Complexity.Language.List.Fold.admissible_cons step domain initial head rest).mp
                  admissible
              have currentCapacity : currentCursor + reserve initial head ≤ heapLimit := by
                have available := cursorBound.trans capacity
                change currentCursor +
                  (reserve initial head + accumulated step reserve (step initial head) rest) ≤
                    heapLimit at available
                omega
              obtain ⟨nextAcc, nextHeap, nextCursor, actual, nextReady,
                  nextBound, nextRelated, nextFits, preserved⟩ :=
                iteration_ready correct resources initial acc ref head tail currentHeap currentCursor
                  positive headAllowed accRelated currentFits
                  (restFits head (by simp)) found currentCapacity
              obtain ⟨sameState, sameControl⟩ := actual.deterministic iterated
              cases sameState
              cases sameControl
              refine ⟨nextCursor, nextReady, (step initial head, rest),
                nextAcc, tail, nextHeap, rfl, restAllowed, nextRelated,
                contents.mono preserved, nextFits, ?_, ?_⟩
              · intro value member
                exact restFits value (_root_.List.mem_cons_of_mem head member)
              · change currentCursor +
                  (reserve initial head + accumulated step reserve (step initial head) rest) ≤
                    cursor + accumulated step reserve mathematical values at cursorBound
                change nextCursor + accumulated step reserve (step initial head) rest ≤
                  cursor + accumulated step reserve mathematical values
                omega
        · rintro ⟨initial, rest⟩ state currentCursor
            ⟨⟨acc, current, currentHeap, rfl, _admissible, _accRelated, _contents,
              currentFits, _restFits, cursorBound⟩, _selected⟩
          exact ⟨by omega, currentFits⟩
        · exact ⟨accumulator, root, heap, rfl, allowed, related, observed,
            accFits, headFits, Nat.le_refl _⟩
        · trivial
      obtain ⟨finalCursor, ready, cursorBound, finalFits⟩ := lifted
      exact ⟨finalAcc, finalHeap, finalCursor, execution, ready, cursorBound, finalFits⟩

/-- Return the accumulator of the same ready traversal, without imposing a
time budget on either the callback or the surrounding function. -/
theorem body_ready
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract program fn same representation step domain)
    {w heapLimit depth : Nat} {reserve : α → CellValue kind → Nat}
    (resources : CalleeResources program fn same representation domain w heapLimit depth reserve)
    (mathematical : α) (values : _root_.List (CellValue kind))
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (related : representation.Rel mathematical accumulator heap)
    (accFits : ValueFits w accumulator)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head))
    (capacity : cursor + accumulated step reserve mathematical values ≤ heapLimit)
    (observed : NodeRef.Contents heap root values) :
    ∃ finalAcc finalHeap finalCursor,
      ∃ execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.body fn same)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state finalAcc none finalHeap) (.returned finalAcc),
      ∃ _ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        finalCursor ≤ cursor + accumulated step reserve mathematical values := by
  obtain ⟨finalAcc, finalHeap, finalCursor, traversed, loopReady, cursorBound, finalFits⟩ :=
    loop_ready correct resources mathematical values accumulator root heap cursor
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
  exact ⟨finalAcc, finalHeap, finalCursor, execution, ready, cursorBound⟩

end Ram.LanguageCompiler.List.Fold
