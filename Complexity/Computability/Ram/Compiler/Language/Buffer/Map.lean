/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Map.Program
import Complexity.Computability.Ram.Compiler.Language.Arena.Linking
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Realizing the shared source buffer map

The mathematical callback contract belongs to `Complexity.Language.Buffer.Map`.
The resource interfaces here concern the same selected source body: word ranges,
call nesting, actual arena reservation and its existing `ArenaExecutionCost`.
No Lean function is accepted as an executable callback, and proposed bounds do
not determine execution or termination.

The caller may use a scalar predicate to restrict callback arguments, for example
to the elements of its input array. Arena growth and instruction bounds remain
separate obligations; a callback can allocate scratch or retained objects when
its actual readiness proof accounts for them.
-/

namespace Ram.LanguageCompiler.BufferMap

open Complexity.Language

variable {signatures : List Signature} {inputKind outputKind : CellTy}

/-- The actual selected body, transported only along its complete signature. -/
def calleeBody (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind) :
    Complexity.Language.Stmt signatures [inputKind.toTy] outputKind.toTy :=
  cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
    (program.body fn)

/-- The one actual scalar argument installed at the source call boundary. -/
def calleeArgs (value : CellValue inputKind) : Env [inputKind.toTy] :=
  Env.cons (τ := inputKind.toTy) (inputKind.toValue value) Env.empty

/-- Conditional range, nesting and arena facts for an actual scalar invocation.
The mathematical contract supplies termination separately. The reserved amount
must suffice for every admitted entry cursor and bounds retained arena growth;
intermediate scratch capacity is checked by the existing readiness proof. -/
def CalleeResources (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (w heapLimit depth reserve : Nat) (admissible : CellValue inputKind → Prop) : Prop :=
  ∀ value heap cursor, admissible value →
    ValueFits w (inputKind.toValue value) → cursor + reserve ≤ heapLimit →
    ∀ finish result,
      ∀ execution : Complexity.Language.Exec program (calleeBody program fn same)
        ⟨calleeArgs value, heap⟩ finish (.returned result),
        ∃ finalCursor, ∃ _ready : ArenaReady execution w heapLimit depth cursor finalCursor,
          finalCursor ≤ cursor + reserve

/-- A separate bound on the compiler's observation of that same callee body.
The two body-initialization instructions are included here exactly once, as in
`FunctionCostBound`; call-frame work is subsequently added by `callCost`. -/
def CalleeCostBound (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (w heapLimit depth : Nat) (bound : CellValue inputKind → Nat)
    (admissible : CellValue inputKind → Prop) : Prop :=
  ∀ value heap, admissible value → ∀ finish result,
    ∀ execution : Complexity.Language.Exec program (calleeBody program fn same)
      ⟨calleeArgs value, heap⟩ finish (.returned result),
      ∀ {cursor finalCursor} (ready : ArenaReady execution w heapLimit depth cursor finalCursor)
        {steps}, ArenaExecutionCost ready steps → steps + 2 ≤ bound value

/-- The scalar callback resource contract is the singleton-argument instance
of the shared heap-indexed interface. Its reserved amount is constant and its
precondition does not inspect the entry heap. -/
theorem calleeResources_iff_functionArenaResources
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (w heapLimit depth reserve : Nat) (admissible : CellValue inputKind → Prop) :
    CalleeResources program fn same w heapLimit depth reserve admissible ↔
      FunctionArenaResources program (calleeBody program fn same)
        (calleeArgs (inputKind := inputKind)) (fun value _ => admissible value)
        w heapLimit depth (fun _ => reserve) := by
  constructor
  · intro resources value heap cursor allowed fits capacity finish result execution
    exact resources value heap cursor allowed (fits .here) capacity finish result execution
  · intro resources value heap cursor allowed fits capacity finish result execution
    exact resources value heap cursor allowed
      (EnvFits.cons (τ := inputKind.toTy) (EnvFits.empty w) (inputKind.toValue value) fits)
      capacity finish result execution

/-- The callback bound already measures precisely the same execution and body
initialization as the general function-resource interface. -/
theorem calleeCostBound_iff_functionArenaCostBound
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (w heapLimit depth : Nat) (bound : CellValue inputKind → Nat)
    (admissible : CellValue inputKind → Prop) :
    CalleeCostBound program fn same w heapLimit depth bound admissible ↔
      FunctionArenaCostBound program (calleeBody program fn same)
        (calleeArgs (inputKind := inputKind)) (fun value _ => admissible value)
        w heapLimit depth bound := Iff.rfl

/-- Relocating the actual callback commutes with its signature transport. -/
theorem calleeBody_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    (fn : Fin source.length)
    (same : source[fn] = Buffer.Map.signature inputKind outputKind) :
    (calleeBody sourceProgram fn same).renameCalls map =
      calleeBody targetProgram (map.toFun fn) ((map.signature_eq fn).trans same) := by
  unfold calleeBody
  calc
    _ = cast (congrArg (fun s => Complexity.Language.Stmt target s.params s.result) same)
        ((sourceProgram.body fn).renameCalls map) :=
      Complexity.Language.Stmt.renameCalls_cast map same (sourceProgram.body fn)
    _ = _ := by
      rw [← embedded fn]
      simp only [SignatureMap.body, cast_cast]

/-- Existing callback ranges and arena bounds survive actual table relocation;
the map consumer need not re-prove its scalar implementation's resources. -/
theorem CalleeResources.renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target} {fn : Fin source.length}
    {same : source[fn] = Buffer.Map.signature inputKind outputKind}
    {w heapLimit depth reserve : Nat} {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources sourceProgram fn same w heapLimit depth reserve admissible)
    (embedded : sourceProgram.Embeds map targetProgram) :
    CalleeResources targetProgram (map.toFun fn) ((map.signature_eq fn).trans same)
      w heapLimit depth reserve admissible := by
  unfold CalleeResources
  rw [← calleeBody_renameCalls embedded fn same]
  intro value heap cursor allowed fits capacity finish result execution
  obtain ⟨finalCursor, ready, bound⟩ :=
    resources value heap cursor allowed fits capacity finish result
      (execution.of_renameCalls embedded)
  exact ⟨finalCursor, ready.renameCalls embedded, bound⟩

/-- The same compiled callback count is preserved, including recursive calls.
Neither its per-element bound nor its two body-wrapper instructions change. -/
theorem CalleeCostBound.renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target} {fn : Fin source.length}
    {same : source[fn] = Buffer.Map.signature inputKind outputKind}
    {w heapLimit depth : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (bounded : CalleeCostBound sourceProgram fn same w heapLimit depth bound admissible)
    (embedded : sourceProgram.Embeds map targetProgram) :
    CalleeCostBound targetProgram (map.toFun fn) ((map.signature_eq fn).trans same)
      w heapLimit depth bound admissible := by
  unfold CalleeCostBound
  rw [← calleeBody_renameCalls embedded fn same]
  intro value heap allowed finish result execution cursor finalCursor ready steps cost
  exact bounded value heap allowed finish result (execution.of_renameCalls embedded)
    (ready.of_renameCalls embedded) (cost.of_renameCalls embedded)

private def cursorState {Γ : List Ty} (locals : Env Γ) (index : Nat) (heap : Heap) :
    Complexity.Language.State (.nat :: Γ) :=
  Complexity.Language.State.cons index ⟨locals, heap⟩

/-- The shared guard executes its actual length read, comparison and return.
The two temporary bindings leave the caller's locals and heap unchanged. -/
theorem guard_execution {Γ : List Ty}
    (program : Complexity.Language.Program signatures)
    (source : Var Γ (.buffer inputKind)) (locals : Env Γ) (index : Nat) (heap : Heap) :
    Complexity.Language.Exec program (Buffer.Map.guard source)
      (cursorState locals index heap) (cursorState locals index heap)
      (.returned (decide (index < (locals.get source).length))) :=
  .letPrim (.letPrim (.ret (.var .here) _))

/-- The guard's count follows the existing primitive and return rules. It does
not depend on either buffer contents or a proposed callback cost. -/
theorem guard_measured {Γ : List Ty}
    (program : Complexity.Language.Program signatures)
    (source : Var Γ (.buffer inputKind)) (locals : Env Γ) (index : Nat) (heap : Heap)
    {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (indexFits : index < 2 ^ w) (sourceFits : (locals.get source).length < 2 ^ w) :
    ∃ ready : ArenaReady (guard_execution program source locals index heap)
        w heapLimit depth cursor cursor,
      ArenaExecutionCost ready 10 := by
  have decisionFits : ValueFits w (τ := .bool)
      (decide (index < (locals.get source).length)) := by
    have oneFits := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
    simp only [ValueFits]
    split <;> omega
  let ready : ArenaReady (guard_execution program source locals index heap)
      w heapLimit depth cursor cursor :=
    .letPrim (value := .length (.var (.there source)))
      (entry := cursorState locals index heap) sourceFits
      (.letPrim (value := .lt (.var (.there .here)) (.var .here))
        (entry := Complexity.Language.State.cons (τ := .nat) (locals.get source).length
          (cursorState locals index heap)) ⟨indexFits, sourceFits⟩
        (.ret (.var .here) _ decisionFits))
  refine ⟨ready, ?_⟩
  exact .letPrim (value := .length (.var (.there source)))
    (entry := cursorState locals index heap) (fits := sourceFits)
    (.letPrim (value := .lt (.var (.there .here)) (.var .here))
      (entry := Complexity.Language.State.cons (τ := .nat) (locals.get source).length
        (cursorState locals index heap)) (fits := ⟨indexFits, sourceFits⟩)
      (.ret (.var .here) _ (fits := decisionFits)))

/-- One complete map iteration reuses the actual callee execution, its arena
readiness and its independently proved cost. Only the traversal's emitted
read/write/advance work is added. No array-map correctness proof is repeated. -/
theorem iteration_measured {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (correct : Buffer.Map.Contract program fn same f)
    {w heapLimit depth reserve : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources program fn same w heapLimit depth reserve admissible)
    (bounded : CalleeCostBound program fn same w heapLimit depth bound admissible)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind)) (index : Nat) (heap : Heap)
    {cursor : Nat} (positive : 0 < w)
    (sourceFits : (locals.get source).length < 2 ^ w)
    (targetFits : (locals.get target).length < 2 ^ w)
    (available : index < input.size)
    (allowed : admissible input[index])
    (inputFits : ValueFits w (inputKind.toValue input[index]))
    (capacity : cursor + reserve ≤ heapLimit)
    (extent : input.size ≤ (locals.get target).length)
    (observed : (locals.get source).Contents heap input)
    (targetValid : (locals.get target).Valid heap)
    (separated : (locals.get target).Disjoint (locals.get source)) :
    ∃ finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program
        (Buffer.Map.iteration (result := result) fn same source target)
        (cursorState locals index heap) (cursorState locals (index + 1) finalHeap) .normal,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧ steps ≤ callCost program fn (bound input[index]) + 16 ∧
          finalCursor ≤ cursor + reserve ∧
          (locals.get source).Contents finalHeap input ∧
          (locals.get target).Valid finalHeap := by
  obtain ⟨calleeFinish, returned, invocation, _, preserved⟩ :=
    correct.invocation input[index] heap
  obtain ⟨finalCursor, calleeReady, cursorBound⟩ :=
    resources input[index] heap cursor allowed inputFits capacity _ _ invocation
  obtain ⟨calleeSteps, calleeCost⟩ := calleeReady.exists_cost
  have calleeBound := bounded input[index] heap allowed _ _ invocation calleeReady calleeCost
  have indexFits : index < 2 ^ w := by
    rw [observed.size_eq] at available
    omega
  have nextFits : index + 1 < 2 ^ w := by
    have available' : index < (locals.get source).length := by
      simpa only [observed.size_eq] using available
    omega
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  obtain ⟨output, targetContents⟩ := targetValid.contents
  have targetNow := preserved (locals.get target) output targetContents
  have targetBound : index < output.size := by
    rw [targetContents.size_eq]
    omega
  obtain ⟨finalHeap, written, updated⟩ :=
    targetNow.write_exists targetBound (outputKind.ofValue returned)
  let afterCall : Complexity.Language.State
      (outputKind.toTy :: inputKind.toTy :: .nat :: Γ) :=
    Complexity.Language.State.cons returned
      (Complexity.Language.State.cons (inputKind.toValue input[index])
        (cursorState locals index calleeFinish.heap))
  let afterWrite : Complexity.Language.State
      (outputKind.toTy :: inputKind.toTy :: .nat :: Γ) :=
    ⟨afterCall.locals, finalHeap⟩
  let store : Complexity.Language.Exec program
      (.write (.var (.there (.there (.there target))))
        (.var (.there (.there .here))) (.var .here) :
        Complexity.Language.Stmt signatures
          (outputKind.toTy :: inputKind.toTy :: .nat :: Γ) result)
      afterCall afterWrite .normal := .write written
  let advance := Complexity.Language.Exec.assign (program := program) (result := result)
    (.there (.there .here)) (.add (.var (.there (.there .here))) (.nat 1)) afterWrite
  let execution : Complexity.Language.Exec program
      (Buffer.Map.iteration (result := result) fn same source target)
      (cursorState locals index heap) (cursorState locals (index + 1) finalHeap) .normal :=
    .read (buffer := .var (.there source)) (index := .var .here)
      (entry := cursorState locals index heap) (observed.read available)
      (Complexity.Language.Exec.callReturnOfEq same
        (entry := Complexity.Language.State.cons (τ := inputKind.toTy)
          (inputKind.toValue input[index]) (cursorState locals index heap))
        (args := .cons (.var .here) .nil) invocation (.seqNormal store advance))
  have arguments : EnvFits w (calleeArgs input[index]) :=
    EnvFits.cons (τ := inputKind.toTy) (EnvFits.empty w)
      (inputKind.toValue input[index]) inputFits
  let storeReady : ArenaReady store w heapLimit (depth + 1) finalCursor finalCursor :=
    .write (written := written) targetFits indexFits calleeReady.outcome_fits
  let advanceReady : ArenaReady advance w heapLimit (depth + 1) finalCursor finalCursor :=
    .assign _ _ _ ⟨indexFits, oneFits, nextFits⟩
  let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
    .read (buffer := .var (.there source)) (index := .var .here)
      (entry := cursorState locals index heap) (loaded := observed.read available)
      sourceFits indexFits inputFits
      (ArenaReady.callReturnOfEq same
        (entry := Complexity.Language.State.cons (τ := inputKind.toTy)
          (inputKind.toValue input[index]) (cursorState locals index heap))
        (args := .cons (.var .here) .nil) arguments calleeReady
        (.seqNormal storeReady advanceReady))
  have cost : ArenaExecutionCost ready
      (5 + (callCost program fn (calleeSteps + 2) + (5 + 2 + 4))) :=
    .read (buffer := .var (.there source)) (index := .var .here)
      (entry := cursorState locals index heap) (bufferFits := sourceFits)
      (indexFits := indexFits) (loaded := observed.read available) (valueFits := inputFits)
      (ArenaExecutionCost.callReturnOfEq same
        (entry := Complexity.Language.State.cons (τ := inputKind.toTy)
          (inputKind.toValue input[index]) (cursorState locals index heap))
        (args := .cons (.var .here) .nil) (arguments := @arguments) calleeCost
        (.seqNormal
          (.write (buffer := .var (.there (.there (.there target))))
            (index := .var (.there (.there .here))) (value := .var .here)
            (entry := afterCall) (written := written) (bufferFits := targetFits)
            (indexFits := indexFits) (valueFits := calleeReady.outcome_fits))
          (.assign (.there (.there .here)) (.add (.var (.there (.there .here))) (.nat 1))
            afterWrite (fits := ⟨indexFits, oneFits, nextFits⟩))))
  refine ⟨finalHeap, finalCursor, _, execution, ready, cost, ?_, cursorBound,
    (preserved (locals.get source) input observed).write_of_disjoint written separated,
    updated.valid⟩
  have callBound := callCost_mono program fn calleeBound
  omega

private theorem guard_measured_of_eq {Γ : List Ty}
    (program : Complexity.Language.Program signatures)
    (source : Var Γ (.buffer inputKind)) (locals : Env Γ) (index : Nat) (heap : Heap)
    {w heapLimit depth cursor : Nat} (positive : 0 < w)
    (indexFits : index < 2 ^ w) (sourceFits : (locals.get source).length < 2 ^ w)
    (decision : Bool) (selected : decide (index < (locals.get source).length) = decision) :
    ∃ execution : Complexity.Language.Exec program (Buffer.Map.guard source)
        (cursorState locals index heap) (cursorState locals index heap) (.returned decision),
      ∃ ready : ArenaReady execution w heapLimit depth cursor cursor,
        ArenaExecutionCost ready 10 := by
  subst decision
  exact ⟨guard_execution program source locals index heap,
    guard_measured program source locals index heap positive indexFits sourceFits⟩

/-- An ordinary list sum of callback upper bounds plus the compiler-derived
round overhead. This is a proposed mathematical envelope, not an evaluator. -/
def remainingCost (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (bound : CellValue inputKind → Nat)
    (input : Array (CellValue inputKind)) (index : Nat) : Nat :=
  ((input.toList.drop index).map (fun value => callCost program fn (bound value) + 36)).sum

/-- The traversal envelope is the sum of the actual elements' callback bounds
plus linear, compiler-derived traversal and calling-convention overhead. -/
theorem remainingCost_eq_sum (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (bound : CellValue inputKind → Nat)
    (input : Array (CellValue inputKind)) (index : Nat) :
    remainingCost program fn bound input index =
      ((input.toList.drop index).map bound).sum +
        (input.size - index) * (callCost program fn 0 + 36) := by
  have charge (value : CellValue inputKind) :
      callCost program fn (bound value) + 36 = bound value + (callCost program fn 0 + 36) := by
    rw [callCost_eq_add]
    exact Nat.add_assoc _ _ _
  simp only [remainingCost, charge, List.sum_map_add, List.map_const',
    List.sum_replicate_nat, List.length_drop, Array.length_toList]

private theorem remainingCost_step (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (bound : CellValue inputKind → Nat)
    (input : Array (CellValue inputKind)) (index : Nat) (available : index < input.size) :
    remainingCost program fn bound input index =
      callCost program fn (bound input[index]) + 36 +
        remainingCost program fn bound input (index + 1) := by
  unfold remainingCost
  rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using available)]
  simp only [List.map_cons, List.sum_cons, Array.getElem_toList]

@[simp] theorem remainingCost_done (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (bound : CellValue inputKind → Nat)
    (input : Array (CellValue inputKind)) :
    remainingCost program fn bound input input.size = 0 := by
  simp [remainingCost, List.drop_eq_nil_of_le]

/-- A full traversal threads the actual arena cursor through every call.
The invariant uses only source contents and target validity; the independent
source map theorem supplies the final `Array.map` equality. -/
theorem loop_measured {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (correct : Buffer.Map.Contract program fn same f)
    {w heapLimit depth reserve : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources program fn same w heapLimit depth reserve admissible)
    (bounded : CalleeCostBound program fn same w heapLimit depth bound admissible)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind))
    (positive : 0 < w) (sourceFits : (locals.get source).length < 2 ^ w)
    (targetFits : (locals.get target).length < 2 ^ w)
    (allowed : ∀ i (hi : i < input.size), admissible input[i])
    (inputFits : ∀ i (hi : i < input.size), ValueFits w (inputKind.toValue input[i]))
    (extent : input.size ≤ (locals.get target).length)
    (separated : (locals.get target).Disjoint (locals.get source))
    (index : Nat) (heap : Heap) (cursor : Nat) (indexBound : index ≤ input.size)
    (capacity : cursor + (input.size - index) * reserve ≤ heapLimit)
    (observed : (locals.get source).Contents heap input)
    (targetValid : (locals.get target).Valid heap) :
    ∃ finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program
        (Buffer.Map.loop (result := result) fn same source target)
        (cursorState locals index heap) (cursorState locals input.size finalHeap) .normal,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
          steps ≤ remainingCost program fn bound input index + 21 ∧
          finalCursor ≤ cursor + (input.size - index) * reserve ∧
          (locals.get source).Contents finalHeap input ∧
          (locals.get target).Valid finalHeap := by
  generalize remainingEq : input.size - index = remaining at capacity ⊢
  induction remaining using Nat.strong_induction_on generalizing index heap cursor with
  | h remaining ih =>
    have indexFits : index < 2 ^ w :=
      lt_of_le_of_lt (indexBound.trans_eq observed.size_eq) sourceFits
    by_cases active : index < input.size
    · have selected : decide (index < (locals.get source).length) = true := by
        simpa only [← observed.size_eq, decide_eq_true_eq] using active
      obtain ⟨test, testReady, testCost⟩ :=
        guard_measured_of_eq program source locals index heap
          (depth := depth + 1) (heapLimit := heapLimit) (cursor := cursor)
          positive indexFits sourceFits true selected
      have remainingStep : remaining = (input.size - (index + 1)) + 1 := by omega
      have roundCapacity : cursor + reserve ≤ heapLimit := by
        rw [remainingStep, Nat.add_mul, Nat.one_mul] at capacity
        omega
      obtain ⟨middleHeap, middleCursor, roundSteps, iterated, iterationReady, iterationCost,
        roundBound, cursorBound, sourceKept, targetKept⟩ :=
        iteration_measured correct resources bounded source target locals input index heap
          positive sourceFits targetFits active (allowed index active) (inputFits index active)
          roundCapacity extent observed targetValid separated
      have nextCapacity : middleCursor + (input.size - (index + 1)) * reserve ≤ heapLimit := by
        rw [remainingStep, Nat.add_mul, Nat.one_mul] at capacity
        omega
      obtain ⟨finalHeap, finalCursor, restSteps, rest, restReady, restCost,
        restBound, finalCursorBound, sourceFinal, targetFinal⟩ :=
        ih (input.size - (index + 1)) (by omega)
          (index := index + 1) (heap := middleHeap) (cursor := middleCursor)
          (capacity := nextCapacity) (observed := sourceKept) (targetValid := targetKept)
          (indexBound := by omega) (remainingEq := rfl)
      let execution : Complexity.Language.Exec program
          (Buffer.Map.loop (result := result) fn same source target)
          (cursorState locals index heap) (cursorState locals input.size finalHeap) .normal :=
        .whileTrue test iterated rest
      let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
        .whileTrue testReady iterationReady restReady
      have cost : ArenaExecutionCost ready (10 + roundSteps + restSteps + 10) :=
        .whileTrue testCost iterationCost restCost
      refine ⟨finalHeap, finalCursor, _, execution, ready, cost, ?_, ?_, sourceFinal, targetFinal⟩
      · rw [remainingCost_step program fn bound input index active]
        omega
      · rw [remainingStep, Nat.add_mul, Nat.one_mul]
        omega
    · have complete : index = input.size := by omega
      have selected : decide (index < (locals.get source).length) = false := by
        simpa only [← observed.size_eq, decide_eq_false_iff_not] using active
      obtain ⟨test, testReady, testCost⟩ :=
        guard_measured_of_eq program source locals index heap
          (depth := depth + 1) (heapLimit := heapLimit) (cursor := cursor)
          positive indexFits sourceFits false selected
      subst index
      have noRemaining : remaining = 0 := by omega
      subst remaining
      let execution : Complexity.Language.Exec program
          (Buffer.Map.loop (result := result) fn same source target)
          (cursorState locals input.size heap) (cursorState locals input.size heap) .normal :=
        .whileFalse test
      let ready : ArenaReady execution w heapLimit (depth + 1) cursor cursor :=
        .whileFalse testReady
      exact ⟨heap, cursor, 21, execution, ready, .whileFalse testCost,
        by simp only [remainingCost_done]; omega, by omega, observed, targetValid⟩

/-- The scoped cursor adds only its actual initialization. Caller locals are
restored, while the real final heap and callback arena growth are retained. -/
theorem into_measured {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (correct : Buffer.Map.Contract program fn same f)
    {w heapLimit depth reserve : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources program fn same w heapLimit depth reserve admissible)
    (bounded : CalleeCostBound program fn same w heapLimit depth bound admissible)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind)) (heap : Heap) (cursor : Nat)
    (positive : 0 < w) (sourceFits : (locals.get source).length < 2 ^ w)
    (targetFits : (locals.get target).length < 2 ^ w)
    (allowed : ∀ i (hi : i < input.size), admissible input[i])
    (inputFits : ∀ i (hi : i < input.size), ValueFits w (inputKind.toValue input[i]))
    (extent : input.size ≤ (locals.get target).length)
    (separated : (locals.get target).Disjoint (locals.get source))
    (capacity : cursor + input.size * reserve ≤ heapLimit)
    (observed : (locals.get source).Contents heap input)
    (targetValid : (locals.get target).Valid heap) :
    ∃ finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program
        (Buffer.Map.into (result := result) fn same source target)
        ⟨locals, heap⟩ ⟨locals, finalHeap⟩ .normal,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧ steps ≤ remainingCost program fn bound input 0 + 23 ∧
          finalCursor ≤ cursor + input.size * reserve ∧
          (locals.get source).Contents finalHeap input ∧
          (locals.get target).Valid finalHeap := by
  obtain ⟨finalHeap, finalCursor, loopSteps, iterated, loopReady, loopCost,
    loopBound, cursorBound, sourceFinal, targetFinal⟩ :=
    loop_measured (result := result) correct resources bounded source target locals input
      positive sourceFits targetFits allowed inputFits extent separated 0 heap cursor
      (Nat.zero_le _) capacity observed targetValid
  let execution : Complexity.Language.Exec program
      (Buffer.Map.into (result := result) fn same source target)
      ⟨locals, heap⟩ ⟨locals, finalHeap⟩ .normal :=
    .letPrim (value := .atom (.nat 0)) (entry := ⟨locals, heap⟩) iterated
  let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
    .letPrim (value := .atom (.nat 0)) (entry := ⟨locals, heap⟩)
      (Nat.two_pow_pos w) loopReady
  have cost : ArenaExecutionCost ready (2 + loopSteps) :=
    .letPrim (value := .atom (.nat 0)) (entry := ⟨locals, heap⟩)
      (fits := Nat.two_pow_pos w) loopCost
  exact ⟨finalHeap, finalCursor, _, execution, ready, cost,
    by omega, cursorBound, sourceFinal, targetFinal⟩

end Ram.LanguageCompiler.BufferMap
