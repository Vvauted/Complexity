/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Compiled
import Examples.Language.Splay.Amortized
import Complexity.Computability.Ram.Compiler.Language.Heap.Observation

/-!
# Amortized bounds for consecutive actual RAM splay calls

The history records equations of the existing unbounded function runner. Each
next invocation uses the previous result's entire actual memory and I/O state,
including private stack contents, and the returned mathematical root. It is
not a second interpreter or a sum of independently reset executions.

The sequence theorem constructs this history from shared typed execution
outcomes. Its instruction bounds are conclusions of those actual calls, not an
assumed price for mathematical rotations. Telescoping retains the initial and
final logarithmic potentials. The fixed stack capacity is a conservative bound
uniform over all trees with the initial node count. This is a sufficient launch
condition, not a separate theorem about exact peak or reachable live storage.

The invocation boundary is the existing preloaded function trampoline. Every
call includes its call/return and halt instructions. Host scheduling, supplying
query words and initial data loading remain outside that boundary; no memory
copy or hidden heap reset is performed by the state projection.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree Ram.LanguageCompiler

/-- A sufficient address envelope for every access to a tree of this size.
The nesting allowance follows two-level recursive descent, independently of
the instruction bound. It is not a bit-space or exact live-storage bound. -/
def splaySequenceCapacity (heapLimit nodes : Nat) : Nat :=
  heapLimit + (nodes / 2 + 1) *
    Ram.ABI.frameSize (programControl Implementation.program)

/-- Witnesses of actual calls, with source meaning and target state linked at
every index. The functions beyond `count` carry no execution requirement.
This is a record of existing runner equations, not an execution semantics. -/
structure SplayRunHistory {w : Nat} (heapLimit : Nat) (placement : Nat → Ram.Word w)
    (key : Nat → Nat) (keys left right : Buffer .nat) (queries : Nat → Nat) (count : Nat)
    (initialTree : Tree Nat) (initialHeap : Heap) (initialEntry : Ram.Source.State w) where
  /-- Mathematical trees represented by the actual heap states. -/
  trees : Nat → Tree Nat
  /-- Source heaps at the successive call boundaries. -/
  heaps : Nat → Heap
  /-- Actual data used to launch each existing function trampoline. -/
  entries : Nat → Ram.Source.State w
  /-- Actual halted RAM states returned by the runner. -/
  targets : Nat → Ram.State w
  /-- Actual complete invocation counts returned by that same runner. -/
  steps : Nat → Nat
  initial_tree : trees 0 = initialTree
  initial_heap : heaps 0 = initialHeap
  initial_entry : entries 0 = initialEntry
  represented : ∀ i, i ≤ count → Rep key keys left right (heaps i) (trees i)
  memory : ∀ i, i ≤ count → HeapRep placement heapLimit (heaps i) (entries i)
  inorder : ∀ i, i ≤ count → (trees i).inorder = initialTree.inorder
  source : ∀ i, i < count →
    Implementation.splay keys left right (root (trees i)) (queries i) (heaps i) =
      Part.some (.ok (root (trees (i + 1))), heaps (i + 1))
  trace : ∀ i, i < count →
    SplayTrace (searchFocus key (queries i) (trees i)) (trees i) (trees (i + 1))
      (searchDepth key (queries i) (trees i))
  frame : ∀ i, i < count →
    Heap.PreservesOutside (linkCells left right (trees i)) (heaps i) (heaps (i + 1))
  run : ∀ i, i < count →
    Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
        (lowerProgram Implementation.program) Implementation.splayId.val
        (contextSize
          (Implementation.signatures[Implementation.splayId.val]' Implementation.splayId.isLt).params)
        heapLimit
        (envWords placement
          (Implementation.splay_args keys left right (root (trees i)) (queries i))) (entries i) =
      some ⟨targets i, steps i, .halted⟩
  returned : ∀ i, i < count →
    Ram.LocalCompiler.Function.returnedValues 1 (targets i) =
      valueWords placement (τ := .nat) (root (trees (i + 1)))
  resumed : ∀ i, i < count → entries (i + 1) = Ram.Source.State.ofRam (targets i)
  instruction_bound : ∀ i, i < count →
    steps i ≤ splayInstructionFactor * (searchDepth key (queries i) (trees i) + 1)

/-- Consecutive actual runner invocations admit the logarithmic amortized
bound. Only initial representation and explicit word/code/stack capacities are
assumed; every per-access instruction bound is proved by `splay_execute`.
The initial potential is charged and final potential retained, including for
empty trees and zero accesses. -/
theorem splay_sequence_runUntil {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (key : Nat → Nat) (keys left right : Buffer .nat)
    (queries : Nat → Nat) (count : Nat) (initialTree : Tree Nat) {initialHeap : Heap}
    (input : Input key keys left right initialTree initialHeap)
    (capacity : FunctionCapacity Implementation.program Implementation.splayId w
      (initialTree.numNodes / 2) heapLimit)
    (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queriesFit : ∀ i, i < count → queries i < 2 ^ w)
    (initialEntry : Ram.Source.State w)
    (memory : HeapRep placement heapLimit initialHeap initialEntry) :
    ∃ history : SplayRunHistory heapLimit placement key keys left right queries count
        initialTree initialHeap initialEntry,
      ((∑ i ∈ Finset.range count, history.steps i : Nat) : ℝ) +
          (splayInstructionFactor : ℝ) * potential (history.trees count) ≤
        (splayInstructionFactor : ℝ) * ((count : ℝ) *
          (3 * Real.logb 2 ((initialTree.numNodes + 1 : Nat) : ℝ) + 2) +
          potential initialTree) := by
  classical
  let Data := Tree Nat × Heap × Ram.Source.State w
  let valid : Data → Prop := fun state =>
    Input key keys left right state.1 state.2.1 ∧
      HeapRep placement heapLimit state.2.1 state.2.2 ∧
      state.1.inorder = initialTree.inorder ∧ state.1.numNodes = initialTree.numNodes
  let advances (i : Nat) (before after : Data)
      (outcome : FunctionExecution Implementation.program Implementation.splayId heapLimit placement
        (Implementation.splay_args keys left right (root before.1) (queries i))
        before.2.1 before.2.2) : Prop :=
    outcome.value = root after.1 ∧ outcome.heap = after.2.1 ∧
      after.2.2 = outcome.nextEntry ∧
      SplayTrace (searchFocus key (queries i) before.1) before.1 after.1
        (searchDepth key (queries i) before.1) ∧
      Heap.PreservesOutside (linkCells left right before.1) before.2.1 after.2.1 ∧
      outcome.result.steps ≤ splayInstructionFactor * (searchDepth key (queries i) before.1 + 1)
  have nextExists (i : Nat) (hi : i < count) (before : Data) (current : valid before) :
      ∃ after : Data, valid after ∧
        ∃ outcome : FunctionExecution Implementation.program Implementation.splayId heapLimit placement
          (Implementation.splay_args keys left right (root before.1) (queries i))
          before.2.1 before.2.2,
        advances i before after outcome := by
    have depthBound : splayDepthBound before.1 ≤ initialTree.numNodes / 2 :=
      (splayDepthBound_le_numNodes before.1).trans_eq
        (congrArg (fun nodes => nodes / 2) current.2.2.2)
    let launch : FunctionLaunch Implementation.program Implementation.splayId
        (splayDepthBound before.1) heapLimit placement
        (Implementation.splay_args keys left right (root before.1) (queries i))
        before.2.1 before.2.2 := {
      toFunctionCapacity := capacity.mono_depth depthBound
      arguments := splay_args_fits current.1.represented keysFit leftFit rightFit (queriesFit i hi)
      memory := current.2.1 }
    obtain ⟨outcome, ⟨final, valueEq, finalRep, trace, frame⟩, _, bounded⟩ :=
      splay_execute key keys left right (queries i) before.1 current.1 launch
    refine ⟨(final, outcome.heap, outcome.nextEntry), ?_, outcome,
      valueEq, rfl, rfl, trace, frame, bounded⟩
    exact ⟨⟨finalRep, trace.inorder_eq.symm ▸ current.1.unique,
        input.keysLeft, input.keysRight, input.leftRight⟩, outcome.memory,
      trace.inorder_eq.trans current.2.2.1, trace.numNodes_eq.trans current.2.2.2⟩
  let initial : {state : Data // valid state} :=
    ⟨(initialTree, initialHeap, initialEntry), input, memory, rfl, rfl⟩
  -- Choice selects witnesses of already proved runner equations; it does not
  -- define an evaluator or extract a runtime count from a proposed bound.
  let advance (i : Nat) (before : {state : Data // valid state}) :
      {state : Data // valid state} :=
    if hi : i < count then
      ⟨Classical.choose (nextExists i hi before.val before.property),
        (Classical.choose_spec (nextExists i hi before.val before.property)).1⟩
    else before
  let states : Nat → {state : Data // valid state} := Nat.rec initial advance
  have states_succ (i : Nat) : states (i + 1) = advance i (states i) := rfl
  have next_state (i : Nat) (hi : i < count) :
      (states (i + 1)).val = Classical.choose
        (nextExists i hi (states i).val (states i).property) := by
    rw [states_succ]
    simp only [advance, dif_pos hi]
  have transitions (i : Nat) (hi : i < count) :
      ∃ outcome : FunctionExecution Implementation.program Implementation.splayId heapLimit placement
        (Implementation.splay_args keys left right (root (states i).val.1) (queries i))
        (states i).val.2.1 (states i).val.2.2,
        advances i (states i).val (states (i + 1)).val outcome := by
    rw [next_state i hi]
    exact (Classical.choose_spec (nextExists i hi (states i).val (states i).property)).2
  let invocations (i : Nat) (hi : i < count) := Classical.choose (transitions i hi)
  let outcomes (i : Nat) : Ram.RunResult (Ram.State w) :=
    if hi : i < count then (invocations i hi).result else ⟨Ram.State.initial [], 0, .halted⟩
  have outcomeEq (i : Nat) (hi : i < count) : outcomes i = (invocations i hi).result := by
    simp only [outcomes, dif_pos hi]
  have properties (i : Nat) (hi : i < count) :
      advances i (states i).val (states (i + 1)).val (invocations i hi) :=
    Classical.choose_spec (transitions i hi)
  let history : SplayRunHistory heapLimit placement key keys left right queries count
      initialTree initialHeap initialEntry := {
    trees := fun i => (states i).val.1
    heaps := fun i => (states i).val.2.1
    entries := fun i => (states i).val.2.2
    targets := fun i => (outcomes i).state
    steps := fun i => (outcomes i).steps
    initial_tree := rfl
    initial_heap := rfl
    initial_entry := rfl
    represented := fun i _ => (states i).property.1.represented
    memory := fun i _ => (states i).property.2.1
    inorder := fun i _ => (states i).property.2.2.1
    source := fun i hi => by
      simpa only [Implementation.splay, Implementation.splay_args,
        (properties i hi).1, (properties i hi).2.1] using (invocations i hi).source
    trace := fun i hi => (properties i hi).2.2.2.1
    frame := fun i hi => (properties i hi).2.2.2.2.1
    run := fun i hi => by
      simpa only [outcomeEq i hi] using (invocations i hi).run_halted
    returned := fun i hi => by
      simpa only [outcomeEq i hi, (properties i hi).1] using (invocations i hi).returned
    resumed := fun i hi => by
      simpa only [FunctionExecution.nextEntry, outcomeEq i hi] using (properties i hi).2.2.1
    instruction_bound := fun i hi => by
      simpa only [outcomeEq i hi] using (properties i hi).2.2.2.2.2 }
  refine ⟨history, ?_⟩
  have bound := sum_steps_add_potential_le
    (trees := history.trees)
    (focus := fun i => searchFocus key (queries i) (history.trees i))
    (rotations := fun i => searchDepth key (queries i) (history.trees i))
    (steps := history.steps) (m := count) (K := splayInstructionFactor)
    history.trace history.instruction_bound
  simpa only [history.initial_tree] using bound

/-- A shape-uniform total instruction bound for the constructed actual RAM
history. The initial tree contributes its `n log₂ (n + 1)` credit; final credit
is nonnegative and discarded. No per-call cost assumption is an input. -/
theorem splay_sequence_runUntil_log {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (key : Nat → Nat) (keys left right : Buffer .nat)
    (queries : Nat → Nat) (count : Nat) (initialTree : Tree Nat) {initialHeap : Heap}
    (input : Input key keys left right initialTree initialHeap)
    (capacity : FunctionCapacity Implementation.program Implementation.splayId w
      (initialTree.numNodes / 2) heapLimit)
    (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queriesFit : ∀ i, i < count → queries i < 2 ^ w)
    (initialEntry : Ram.Source.State w)
    (memory : HeapRep placement heapLimit initialHeap initialEntry) :
    ∃ history : SplayRunHistory heapLimit placement key keys left right queries count
        initialTree initialHeap initialEntry,
      ((∑ i ∈ Finset.range count, history.steps i : Nat) : ℝ) ≤
        (splayInstructionFactor : ℝ) * ((count : ℝ) *
          (3 * Real.logb 2 ((initialTree.numNodes + 1 : Nat) : ℝ) + 2) +
          (initialTree.numNodes : ℝ) *
            Real.logb 2 ((initialTree.numNodes + 1 : Nat) : ℝ)) := by
  obtain ⟨history, _⟩ := splay_sequence_runUntil key keys left right queries count initialTree
    input capacity keysFit leftFit rightFit queriesFit initialEntry memory
  refine ⟨history, ?_⟩
  have bound := sum_steps_le_log
    (trees := history.trees)
    (focus := fun i => searchFocus key (queries i) (history.trees i))
    (rotations := fun i => searchDepth key (queries i) (history.trees i))
    (steps := history.steps) (m := count) (K := splayInstructionFactor)
    history.trace history.instruction_bound
  simpa only [history.initial_tree] using bound

end Complexity.Language.Examples.Splay
