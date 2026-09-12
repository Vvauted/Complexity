/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Program
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.MeasuredNode

/-!
# Resource bounds for linked-list folding

The callback operates on an arbitrary represented accumulator and a scalar node
head. Its actual source body, heap effects, return value and arena cursor are
retained through the existing function-resource and measured-execution interfaces.
The linked traversal adds only its emitted branch, read, assignment and loop work.

Mathematical list lengths and accumulator-dependent sums describe the budget;
they are not runtime counters or executable callbacks. The source loop follows
actual stored links. Its independent correctness contract supplies ordinary
`List.foldl` behavior, while the resource proof accounts for the same execution.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- Mathematical charge accumulated along the ordinary fold trajectory.
This is an envelope on supplied bounds, not a source execution or cost model. -/
def accumulated (step : α → CellValue kind → α) (charge : α → CellValue kind → Nat) :
    α → _root_.List (CellValue kind) → Nat
  | _, [] => 0
  | accumulator, head :: tail =>
      charge accumulator head + accumulated step charge (step accumulator head) tail

/-- A fixed per-element overhead separates from the accumulator-dependent
callback charges without changing which accumulator supplies each bound. -/
theorem accumulated_add_const (step : α → CellValue kind → α)
    (charge : α → CellValue kind → Nat) (overhead : Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) :
    accumulated step (fun a head => charge a head + overhead) accumulator values =
      accumulated step charge accumulator values + values.length * overhead := by
  induction values generalizing accumulator with
  | nil => simp only [accumulated, _root_.List.length_nil, Nat.zero_mul, Nat.add_zero]
  | cons head tail ih =>
      simp only [accumulated, _root_.List.length_cons, ih, Nat.add_mul, Nat.one_mul]
      omega

/-- Each index keeps the mathematical accumulator and its actual source value;
heap representations need not choose a unique runtime encoding. -/
def calleeArgs (input : α × Value accTy × CellValue kind) : Env [accTy, kind.toTy] :=
  Env.cons (τ := accTy) input.2.1
    (Env.cons (τ := kind.toTy) (kind.toValue input.2.2) Env.empty)

/-- The callback domain and accumulator observation are checked at the actual
entry heap, rather than turning the representation into a host-side decoder. -/
def calleePre (representation : Representation α accTy)
    (domain : α → CellValue kind → Prop)
    (input : α × Value accTy × CellValue kind) (heap : Heap) : Prop :=
  domain input.1 input.2.2 ∧ representation.Rel input.1 input.2.1 heap

/-- Fold specializes the shared resource interface to the selected callback;
the reservation depends on the mathematical accumulator and current head. -/
abbrev CalleeResources (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (representation : Representation α accTy) (domain : α → CellValue kind → Prop)
    (w heapLimit depth : Nat) (reserve : α → CellValue kind → Nat) : Prop :=
  FunctionArenaResources program (Complexity.Language.List.Fold.calleeBody program fn same)
    calleeArgs (calleePre representation domain) w heapLimit depth
    (fun input => reserve input.1 input.2.2)

/-- Callback bounds retain the shared convention: actual core steps plus the
two function-initialization instructions, before the caller adds its frame work. -/
abbrev CalleeCostBound (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (representation : Representation α accTy) (domain : α → CellValue kind → Prop)
    (w heapLimit depth : Nat) (bound : α → CellValue kind → Nat) : Prop :=
  FunctionArenaCostBound program (Complexity.Language.List.Fold.calleeBody program fn same)
    calleeArgs (calleePre representation domain) w heapLimit depth
    (fun input => bound input.1 input.2.2)

/-- The emitted call overhead and one round of actual linked traversal are
added to the callback's independently supplied bound at each accumulator. -/
def remainingCost (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (accTy : Ty)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) : Nat :=
  accumulated step
    (fun a head => callCost program fn (bound a head) + 2 * fieldCount accTy + 45)
    accumulator values

/-- Callback charges along the ordinary fold trajectory separate from the
compiler's linear traversal and actual calling-convention overhead. -/
theorem remainingCost_eq_sum (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (accTy : Ty)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) :
    remainingCost program fn accTy step bound accumulator values =
      accumulated step bound accumulator values +
        values.length * (callCost program fn 0 + 2 * fieldCount accTy + 45) := by
  have charges :
      (fun a head => callCost program fn (bound a head) + 2 * fieldCount accTy + 45) =
        (fun a head => bound a head +
          (callCost program fn 0 + 2 * fieldCount accTy + 45)) := by
    funext a head
    rw [callCost_eq_add]
    omega
  rw [remainingCost, charges, accumulated_add_const]

/-- Every represented list head already has its scalar range in the actual
initial memory. Later callbacks retain these immutable stored heads. -/
theorem contents_valueFits {w heapLimit : Nat} {placement : Nat → Word w}
    {heap : Heap} {initial : Source.State w} {root : Option (NodeRef kind)}
    {values : _root_.List (CellValue kind)}
    (memory : HeapRep placement heapLimit heap initial)
    (observed : NodeRef.Contents heap root values) :
    ∀ head ∈ values, ValueFits w (kind.toValue head) := by
  induction observed with
  | nil => simp only [_root_.List.not_mem_nil, false_implies, implies_true]
  | @cons ref head tail rest found contents ih =>
      intro value member
      rcases _root_.List.mem_cons.mp member with rfl | member
      · exact (memory.node_valueFits found).1
      · exact ih value member

/-- The actual guard tests only the optional root and preserves both locals
and heap. Its two branches have their existing, distinct emitted counts. -/
theorem guard_measured (program : Complexity.Language.Program signatures)
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    {w heapLimit depth cursor : Nat} (positive : 0 < w) :
    ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.List.Fold.guard accTy kind)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state accumulator root heap) (.returned root.isSome),
      ∃ ready : ArenaReady execution w heapLimit depth cursor cursor,
        ArenaExecutionCost ready (if root.isSome then 9 else 6) := by
  cases root with
  | none =>
      let initial := Complexity.Language.List.Fold.state accumulator (none : Option (NodeRef kind)) heap
      have falseFits : ValueFits w (τ := .bool) false := Nat.two_pow_pos w
      let execution : Complexity.Language.Exec program
          (Complexity.Language.List.Fold.guard accTy kind)
          initial initial (.returned false) :=
        .matchNone rfl (.ret (.bool false) _)
      let returnReady : ArenaReady (Complexity.Language.Exec.ret (program := program)
          (.bool false) initial) w heapLimit depth cursor cursor :=
        .ret (.bool false) initial falseFits
      let ready : ArenaReady execution w heapLimit depth cursor cursor :=
        .matchNone (entry := initial) (value := .var (.there .here))
          (selected := rfl) returnReady
      exact ⟨execution, ready,
        .matchNone (entry := initial) (value := .var (.there .here))
          (selected := rfl) (ready := returnReady)
          (.ret (.bool false) initial (fits := falseFits))⟩
  | some ref =>
      let initial := Complexity.Language.List.Fold.state accumulator (some ref) heap
      let scopedState := Complexity.Language.State.cons (τ := .node kind) ref initial
      have trueFits : ValueFits w (τ := .bool) true :=
        Nat.one_lt_two_pow (Nat.ne_of_gt positive)
      have refFits : ValueFits w (τ := .node kind) ref := trivial
      let execution : Complexity.Language.Exec program
          (Complexity.Language.List.Fold.guard accTy kind)
          initial initial (.returned true) :=
        .matchSome (finish := scopedState) rfl (.ret (.bool true) scopedState)
      let returnReady : ArenaReady (Complexity.Language.Exec.ret (program := program)
          (.bool true) scopedState) w heapLimit depth cursor cursor :=
        .ret (.bool true) scopedState trueFits
      let ready : ArenaReady execution w heapLimit depth cursor cursor :=
        .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
          (selected := rfl) refFits returnReady
      exact ⟨execution, ready,
        .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
          (selected := rfl) (payloadFits := refFits) (ready := returnReady)
          (.ret (.bool true) scopedState (fits := trueFits))⟩

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
  obtain ⟨calleeFinish, returned, invocation, resultRelated, preserved⟩ :=
    correct.invocation mathematical accumulator head heap allowed related
  have arguments : EnvFits w (calleeArgs (mathematical, accumulator, head)) :=
    EnvFits.cons (τ := accTy)
      (EnvFits.cons (τ := kind.toTy) (EnvFits.empty w) (kind.toValue head) headFits)
      accumulator accFits
  obtain ⟨finalCursor, calleeReady, cursorBound⟩ :=
    resources (mathematical, accumulator, head) heap cursor ⟨allowed, related⟩
      arguments capacity _ _ invocation
  obtain ⟨calleeSteps, calleeCost⟩ := calleeReady.exists_cost
  have calleeBound := bounded (mathematical, accumulator, head) heap ⟨allowed, related⟩
    _ _ invocation calleeReady calleeCost
  change calleeSteps + 2 ≤ bound mathematical head at calleeBound
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
  have cost : ArenaExecutionCost ready
      (2 + (13 + (2 * fieldCount kind.toTy +
        (callCost program fn (calleeSteps + 2) + (2 * fieldCount accTy + 2 + 4)))) + 3) :=
    .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
      (selected := rfl) (payloadFits := refFits) (ready := readReady)
      (.readNode (entry := beforeRead) (ref := .var .here) (found := found)
        (valueFits := pairFits) (ready := headReady)
        (.letPrim (entry := afterRead) (value := .fst (.var .here)) (fits := pairFits)
          (ready := callReady)
          (ArenaExecutionCost.callReturnOfEq same (entry := beforeCall)
            (args := .cons (.var (.there (.there (.there .here)))) (.cons (.var .here) .nil))
            (arguments := arguments) (calleeReady := calleeReady) (bodyReady := continuationReady)
            calleeCost
            (.seqNormal (headReady := storeReady) (tailReady := advanceReady)
              (.assign accVar (.atom (.var .here)) afterCall (fits := returnedFits))
              (.assign rootVar (.snd (.var (.there (.there .here)))) afterStore
                (fits := pairFits))))))
  refine ⟨returned, calleeFinish.heap, finalCursor, _, execution, ready, cost, ?_,
    cursorBound, resultRelated, returnedFits, preserved⟩
  have callBound := callCost_mono program fn calleeBound
  have scalarWidth : fieldCount kind.toTy = 1 := by cases kind <;> rfl
  rw [scalarWidth]
  omega

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
  induction values generalizing mathematical accumulator root heap cursor with
  | nil =>
      cases observed
      obtain ⟨test, testReady, testCost⟩ := guard_measured program accumulator
        (none : Option (NodeRef kind)) heap (depth := depth + 1)
        (heapLimit := heapLimit) (cursor := cursor) positive
      let execution : Complexity.Language.Exec program (Complexity.Language.List.Fold.loop fn same)
          (Complexity.Language.List.Fold.state accumulator (none : Option (NodeRef kind)) heap)
          (Complexity.Language.List.Fold.state accumulator (none : Option (NodeRef kind)) heap)
          .normal := .whileFalse test
      let ready : ArenaReady execution w heapLimit (depth + 1) cursor cursor :=
        .whileFalse testReady
      exact ⟨accumulator, heap, cursor, 17, execution, ready, .whileFalse testCost,
        Nat.le_refl _, Nat.le_refl _, accFits⟩
  | cons head rest ih =>
      obtain ⟨headAllowed, restAllowed⟩ :=
        (Complexity.Language.List.Fold.admissible_cons step domain mathematical head rest).mp allowed
      cases observed with
      | @cons ref _ tail _ found contents =>
          obtain ⟨test, testReady, testCost⟩ := guard_measured program accumulator
            (some ref) heap (depth := depth + 1) (heapLimit := heapLimit)
            (cursor := cursor) positive
          have roundCapacity : cursor + reserve mathematical head ≤ heapLimit := by
            simp only [accumulated] at capacity
            omega
          obtain ⟨middleAcc, middleHeap, middleCursor, roundSteps, iterated, iterationReady,
            iterationCost, roundBound, cursorBound, middleRelated, middleFits, preserved⟩ :=
            iteration_measured correct resources bounded mathematical accumulator ref head tail heap
              cursor positive headAllowed related accFits (headFits head (by simp)) found roundCapacity
          have nextCapacity : middleCursor +
              accumulated step reserve (step mathematical head) rest ≤ heapLimit := by
            simp only [accumulated] at capacity
            omega
          obtain ⟨finalAcc, finalHeap, finalCursor, restSteps, remaining, remainingReady,
            remainingCostProof, remainingBound, finalCursorBound, finalFits⟩ :=
            ih (mathematical := step mathematical head) (accumulator := middleAcc)
              (root := tail) (heap := middleHeap) (cursor := middleCursor)
              restAllowed middleRelated middleFits
              (fun value member => headFits value (_root_.List.mem_cons_of_mem head member))
              nextCapacity (contents.mono preserved)
          let execution : Complexity.Language.Exec program
              (Complexity.Language.List.Fold.loop fn same)
              (Complexity.Language.List.Fold.state accumulator (some ref) heap)
              (Complexity.Language.List.Fold.state finalAcc none finalHeap) .normal :=
            .whileTrue test iterated remaining
          let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
            .whileTrue testReady iterationReady remainingReady
          have cost : ArenaExecutionCost ready (9 + roundSteps + restSteps + 10) :=
            .whileTrue testCost iterationCost remainingCostProof
          refine ⟨finalAcc, finalHeap, finalCursor, _, execution, ready, cost, ?_, ?_, finalFits⟩
          · simp only [remainingCost, accumulated] at remainingBound ⊢
            omega
          · simp only [accumulated]
            omega

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

/-- The source invocation receives the original represented accumulator and
linked root. These are existing source arguments, not a host-side list loader. -/
def foldArgs (accumulator : Value accTy) (root : Option (NodeRef kind)) :
    Env [accTy, .option (.node kind)] :=
  Env.cons (τ := accTy) accumulator (Env.cons (τ := .option (.node kind)) root Env.empty)

/-- The complete invocation envelope includes the actual relocated callback
frames, source-body initialization, outer invocation and final halt. -/
def invocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (mathematical : α) (values : _root_.List (CellValue kind)) : Nat :=
  let folded := Complexity.Language.List.Fold.program sourceProgram fn same
  LocalCompiler.Function.callSteps (programControl folded)
    (lowerFunc folded (Complexity.Language.List.Fold.entry accTy kind signatures))
    (remainingCost folded (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
      accTy step bound mathematical values + 2 * fieldCount accTy + 23) + 1

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
