/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map
import Complexity.Computability.Ram.Compiler.Language.Realization.Finite

/-!
# Running the allocating buffer map with its original callback contracts

The shared traversal executes after a real initialized allocation. Its scalar
calls retain the original program's correctness, range, arena and cost proofs
through the existing typed embedding. Allocation, traversal and the final
return are measured in the same source execution and published through the
existing allocation-aware RAM result.

The numerical bound includes initialized output storage and every actual scalar
call. The callback may retain arena storage; its per-invocation reservation is
accounted for cumulatively. This is a sufficient arena bound, not a reachable
live-space measure or an implemented out-of-memory result.
-/

namespace Ram.LanguageCompiler.BufferMap

open Complexity.Language

variable {signatures : List Signature} {inputKind outputKind : CellTy}

/-- The allocating map's actual source arguments: its input view and initializer. -/
def mapArgs (source : Buffer inputKind) (initial : CellValue outputKind) :
    Env [.buffer inputKind, outputKind.toTy] :=
  Env.cons (τ := .buffer inputKind) source
    (Env.cons (τ := outputKind.toTy) (outputKind.toValue initial) Env.empty)

/-- Allocate initialized output, execute the shared traversal and return the
actual fresh handle. This adds the allocation's linear instruction count and
retained storage to the same measured loop, without another array-map proof. -/
theorem body_measured
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (correct : Buffer.Map.Contract program fn same f)
    {w heapLimit depth reserve : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources program fn same w heapLimit depth reserve admissible)
    (bounded : CalleeCostBound program fn same w heapLimit depth bound admissible)
    (source : Buffer inputKind) (input : Array (CellValue inputKind))
    (initial : CellValue outputKind) (heap : Heap) (cursor : Nat)
    (positive : 0 < w) (sourceFits : source.length < 2 ^ w)
    (initialFits : ValueFits w (outputKind.toValue initial))
    (allowed : ∀ i (hi : i < input.size), admissible input[i])
    (inputFits : ∀ i (hi : i < input.size), ValueFits w (inputKind.toValue input[i]))
    (capacity : cursor + input.size + input.size * reserve ≤ heapLimit)
    (observed : source.Contents heap input) :
    ∃ finalHeap finalCursor steps,
      ∃ execution : Complexity.Language.Exec program (Buffer.Map.body fn same)
        ⟨mapArgs source initial, heap⟩ ⟨mapArgs source initial, finalHeap⟩
        (.returned (heap.alloc source.length initial).1),
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
          steps ≤ 14 * input.size + remainingCost program fn bound input 0 + 51 ∧
          finalCursor ≤ cursor + input.size + input.size * reserve := by
  let allocation := heap.alloc (τ := outputKind) source.length
    (outputKind.ofValue (outputKind.toValue initial))
  let args : Env [.buffer inputKind, outputKind.toTy] := mapArgs source initial
  let locals : Env [.buffer outputKind, .nat, .buffer inputKind, outputKind.toTy] :=
    Env.cons (τ := .buffer outputKind) allocation.1
      (Env.cons (τ := .nat) source.length args)
  have sourceNow : source.Contents allocation.2 input := observed.alloc _ _
  have targetNow : allocation.1.Valid allocation.2 := heap.alloc_valid _ _
  have separated : allocation.1.Disjoint source := observed.valid.rooted.disjoint_alloc _ _
  have nextCapacity : cursor + source.length + input.size * reserve ≤ heapLimit := by
    simpa only [observed.size_eq] using capacity
  have allocationCapacity : cursor + source.length ≤ heapLimit := by omega
  obtain ⟨finalHeap, finalCursor, loopSteps, traversed, traversalReady, traversalCost,
    loopBound, cursorBound, _, _⟩ :=
    into_measured (result := .buffer outputKind) correct resources bounded
      (.there (.there .here)) .here locals input allocation.2 (cursor + source.length)
      positive sourceFits sourceFits allowed inputFits observed.size_eq.le
      separated nextCapacity sourceNow targetNow
  let finish : Complexity.Language.State
      [.buffer outputKind, .nat, .buffer inputKind, outputKind.toTy] :=
    ⟨locals, finalHeap⟩
  let returned : Complexity.Language.Exec program (.ret (.var .here))
      finish finish (.returned allocation.1) :=
    .ret (.var .here) finish
  let returnReady : ArenaReady returned w heapLimit (depth + 1) finalCursor finalCursor :=
    .ret (.var .here) finish sourceFits
  have returnCost : ArenaExecutionCost returnReady 6 :=
    .ret (.var .here) finish (fits := sourceFits)
  let sequence := Complexity.Language.Exec.seqNormal traversed returned
  let allocationExec := Complexity.Language.Exec.alloc (kind := outputKind)
    (length := .var .here) (initial := .var (.there (.there .here)))
    (entry := ⟨Env.cons (τ := .nat) source.length args, heap⟩) sequence
  let execution : Complexity.Language.Exec program (Buffer.Map.body fn same)
      ⟨mapArgs source initial, heap⟩ ⟨mapArgs source initial, finalHeap⟩
      (.returned (heap.alloc source.length initial).1) :=
    .letPrim (value := .length (.var .here))
      (entry := ⟨mapArgs source initial, heap⟩) allocationExec
  let ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor :=
    .letPrim (value := .length (.var .here))
      (entry := ⟨mapArgs source initial, heap⟩) sourceFits
      (.alloc (kind := outputKind) (length := .var .here)
        (initial := .var (.there (.there .here)))
        (entry := ⟨Env.cons (τ := .nat) source.length args, heap⟩)
        initialFits allocationCapacity (.seqNormal traversalReady returnReady))
  have cost : ArenaExecutionCost ready (2 + (14 * source.length + 18 + (loopSteps + 2 + 6))) :=
    .letPrim (value := .length (.var .here))
      (entry := ⟨mapArgs source initial, heap⟩)
      (fits := sourceFits)
      (.alloc (kind := outputKind) (length := .var .here)
        (initial := .var (.there (.there .here)))
        (entry := ⟨Env.cons (τ := .nat) source.length args, heap⟩)
        (initialFits := initialFits) (capacity := allocationCapacity)
        (.seqNormal traversalCost returnCost))
  refine ⟨finalHeap, finalCursor, _, execution, ready, cost, ?_, ?_⟩
  · have sizeEq := observed.size_eq
    omega
  · simpa only [observed.size_eq] using cursorBound

/-- The complete mapped invocation bound, including output initialization,
all selected scalar calls, two body-initialization instructions and outer call/halt work. -/
def invocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (bound : CellValue inputKind → Nat) (input : Array (CellValue inputKind)) : Nat :=
  let mapped := Buffer.Map.program sourceProgram fn same
  LocalCompiler.Function.callSteps (programControl mapped)
    (lowerFunc mapped (Buffer.Map.entry inputKind outputKind signatures))
    (14 * input.size +
      remainingCost mapped (Buffer.Map.calleeEntry inputKind outputKind fn) bound input 0 + 53) + 1

/-- Separate the mathematical sum of callback bounds from the compiler-derived
linear traversal overhead and fixed outer invocation work. -/
theorem invocationBound_eq_sum (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (bound : CellValue inputKind → Nat) (input : Array (CellValue inputKind)) :
    invocationBound sourceProgram fn same bound input =
      (input.toList.map bound).sum + input.size *
        (14 + callCost (Buffer.Map.program sourceProgram fn same)
          (Buffer.Map.calleeEntry inputKind outputKind fn) 0 + 36) +
        LocalCompiler.Function.callSteps (programControl (Buffer.Map.program sourceProgram fn same))
          (lowerFunc (Buffer.Map.program sourceProgram fn same)
            (Buffer.Map.entry inputKind outputKind signatures)) 53 + 1 := by
  simp only [invocationBound, remainingCost_eq_sum, List.drop_zero, Nat.sub_zero,
    Nat.mul_add, LocalCompiler.Function.callSteps_eq]
  omega

/-- The size-only bound for a callback with a uniform per-element bound.
All other coefficients come from the selected map and callback implementation. -/
def linearInvocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (perElement length : Nat) : Nat :=
  let mapped := Buffer.Map.program sourceProgram fn same
  length * (perElement + 14 + callCost mapped (Buffer.Map.calleeEntry inputKind outputKind fn) 0 + 36) +
    LocalCompiler.Function.callSteps (programControl mapped)
      (lowerFunc mapped (Buffer.Map.entry inputKind outputKind signatures)) 53 + 1

/-- Uniform callback costs yield a proved affine bound in the input length,
without another loop proof or a price assigned to native `Array.map`. -/
theorem invocationBound_const (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (perElement : Nat) (input : Array (CellValue inputKind)) :
    invocationBound sourceProgram fn same (fun _ => perElement) input =
      linearInvocationBound sourceProgram fn same perElement input.size := by
  rw [invocationBound_eq_sum]
  simp only [linearInvocationBound, List.map_const', List.sum_replicate_nat,
    Array.length_toList, Nat.mul_add]
  omega

/-- Run the shared allocating map using the original scalar implementation's
proofs. The typed result retains the actual RAM state, mapped contents and arena
growth; no relocated callee proof or per-program runner adapter is required. -/
theorem execute
    {sourceProgram : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (correct : Buffer.Map.Contract sourceProgram fn same f)
    {w heapLimit depth reserve : Nat} {bound : CellValue inputKind → Nat}
    {admissible : CellValue inputKind → Prop}
    (resources : CalleeResources sourceProgram fn same w heapLimit depth reserve admissible)
    (bounded : CalleeCostBound sourceProgram fn same w heapLimit depth bound admissible)
    (source : Buffer inputKind) (input : Array (CellValue inputKind))
    (initial : CellValue outputKind) {heap : Heap} {cursor : Nat}
    {placement : Nat → Word w} {entry : Source.State w}
    (launch : FunctionArenaLaunch (Buffer.Map.program sourceProgram fn same)
      (Buffer.Map.entry inputKind outputKind signatures) (depth + 1) heapLimit placement
      (mapArgs source initial) heap cursor entry)
    (observed : source.Contents heap input)
    (allowed : ∀ i (hi : i < input.size), admissible input[i])
    (capacity : cursor + input.size + input.size * reserve ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution (Buffer.Map.program sourceProgram fn same)
        (Buffer.Map.entry inputKind outputKind signatures) (depth + 1) heapLimit placement
        (mapArgs source initial) heap entry,
      outcome.value.Contents outcome.heap (input.map f) ∧
        outcome.value.object = heap.objects.size ∧ Buffer.PreservesContents heap outcome.heap ∧
        outcome.result.steps ≤ invocationBound sourceProgram fn same bound input ∧
        outcome.cursor ≤ cursor + input.size + input.size * reserve := by
  have sourceFits : source.length < 2 ^ w :=
    launch.arguments (τ := .buffer inputKind) .here
  have initialFits : ValueFits w (outputKind.toValue initial) :=
    launch.arguments (τ := outputKind.toTy) (.there .here)
  have inputFits (i : Nat) (hi : i < input.size) :
      ValueFits w (inputKind.toValue input[i]) :=
    (valueFits_cell_iff inputKind input[i]).mpr
      (@HeapFits.read w heap (HeapRep.heapFits launch.arena.heapRep)
        inputKind source i input[i] (observed.read hi))
  have embedded := Buffer.Map.program_embeds sourceProgram fn same
  have measured := body_measured (Buffer.Map.callee_contract sourceProgram fn same correct)
    (resources.renameCalls embedded) (bounded.renameCalls embedded)
    source input initial heap cursor launch.positive sourceFits initialFits
    allowed inputFits capacity observed
  rw [← Buffer.Map.program_body sourceProgram fn same] at measured
  obtain ⟨finalHeap, finalCursor, steps, execution, ready, cost, coreBound, cursorBound⟩ := measured
  obtain ⟨outcome, _, _, cursorEq, bodySteps⟩ := cost.execute launch
  have property := outcome.post (Buffer.Map.program_total correct input) observed
  refine ⟨outcome, property.1, property.2.1, property.2.2, ?_, ?_⟩
  · rw [outcome.steps_eq, bodySteps]
    unfold invocationBound
    exact Nat.add_le_add_right (LocalCompiler.Function.callSteps_mono _ _ (by omega)) 1
  · simpa only [cursorEq] using cursorBound

end Ram.LanguageCompiler.BufferMap
