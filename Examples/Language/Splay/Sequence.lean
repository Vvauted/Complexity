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

The sequence theorem constructs this history from the verified single-access
theorem. Its instruction bounds are conclusions of those actual calls, not an
assumed price for mathematical rotations. Telescoping retains the initial and
final logarithmic potentials. The fixed stack capacity is a conservative bound
uniform over all trees with the initial node count.

The invocation boundary is the existing preloaded function trampoline. Every
call includes its call/return and halt instructions. Host scheduling, supplying
query words and initial data loading remain outside that boundary; no memory
copy or hidden heap reset is performed by the state projection.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree Ram.LanguageCompiler

/-- A sufficient address envelope for every access to a tree of this size.
The instruction-derived nesting allowance is conservative, not an exact stack
peak or a bit-space bound. It does not depend on the number of accesses. -/
def splaySequenceCapacity (heapLimit nodes : Nat) : Nat :=
  heapLimit + (splayLayerBound * (nodes + 1) + 3) *
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
        (envWords placement (splayArgs keys left right (root (trees i)) (queries i))) (entries i) =
      some ⟨targets i, steps i, .halted⟩
  returned : ∀ i, i < count →
    Ram.LocalCompiler.Function.returnedValues 1 (targets i) =
      valueWords placement (τ := .nat) (root (trees (i + 1)))
  resumed : ∀ i, i < count → entries (i + 1) = Ram.Source.State.ofRam (targets i)
  instruction_bound : ∀ i, i < count →
    steps i ≤ splayInstructionFactor * (searchDepth key (queries i) (trees i) + 1)

/-- Consecutive actual runner invocations admit the logarithmic amortized
bound. Only initial representation and explicit word/code/stack capacities are
assumed; every per-access instruction bound is proved by `splay_runUntil`.
The initial potential is charged and final potential retained, including for
empty trees and zero accesses. -/
theorem splay_sequence_runUntil {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (hw : 0 < w) (key : Nat → Nat) (keys left right : Buffer .nat)
    (queries : Nat → Nat) (count : Nat) (initialTree : Tree Nat) {initialHeap : Heap}
    (represented : Rep key keys left right initialHeap initialTree)
    (unique : initialTree.inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right)
    (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queriesFit : ∀ i, i < count → queries i < 2 ^ w)
    (initialEntry : Ram.Source.State w)
    (memory : HeapRep placement heapLimit initialHeap initialEntry)
    (codeCapacity : (lowerCode Implementation.program Implementation.splayId).length < 2 ^ w)
    (stackCapacity : splaySequenceCapacity heapLimit initialTree.numNodes < 2 ^ w) :
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
    Rep key keys left right state.2.1 state.1 ∧
      HeapRep placement heapLimit state.2.1 state.2.2 ∧
      state.1.inorder = initialTree.inorder ∧ state.1.numNodes = initialTree.numNodes
  let advances (i : Nat) (before after : Data) (outcome : Ram.State w × Nat) : Prop :=
    Implementation.splay keys left right (root before.1) (queries i) before.2.1 =
        Part.some (.ok (root after.1), after.2.1) ∧
      SplayTrace (searchFocus key (queries i) before.1) before.1 after.1
        (searchDepth key (queries i) before.1) ∧
      Heap.PreservesOutside (linkCells left right before.1) before.2.1 after.2.1 ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.splayId.val
          (contextSize
            (Implementation.signatures[Implementation.splayId.val]' Implementation.splayId.isLt).params)
          heapLimit
          (envWords placement (splayArgs keys left right (root before.1) (queries i))) before.2.2 =
        some ⟨outcome.1, outcome.2, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 outcome.1 =
        valueWords placement (τ := .nat) (root after.1) ∧
      after.2.2 = Ram.Source.State.ofRam outcome.1 ∧
      outcome.2 ≤ splayInstructionFactor * (searchDepth key (queries i) before.1 + 1)
  have nextExists (i : Nat) (hi : i < count) (before : Data) (current : valid before) :
      ∃ after : Data, valid after ∧ ∃ outcome : Ram.State w × Nat,
        advances i before after outcome := by
    have treeUnique : before.1.inorder.Nodup := current.2.2.1.symm ▸ unique
    have depthBound : searchDepth key (queries i) before.1 ≤ initialTree.numNodes :=
      (searchDepth_le_numNodes key (queries i) before.1).trans_eq current.2.2.2
    have bodyBound : splayBodyBound key (queries i) before.1 ≤
        splayLayerBound * (initialTree.numNodes + 1) + 2 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left splayLayerBound (Nat.add_le_add_right depthBound 1)) 2
    have enough : heapLimit + (splayBodyBound key (queries i) before.1 + 1) *
        Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w := by
      apply lt_of_le_of_lt _ stackCapacity
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right bodyBound 1)) heapLimit
    obtain ⟨final, finish, sourceFinish, steps, target, source, finalRep, trace, frame,
      finalMemory, run, returned, observed, _, bounded⟩ :=
      splay_runUntil hw key keys left right (queries i) before.1 current.1 treeUnique
        keysLeft keysRight leftRight keysFit leftFit rightFit (queriesFit i hi)
        before.2.2 current.2.1 codeCapacity enough
    refine ⟨(final, finish, Ram.Source.State.ofRam target), ?_, (target, steps),
      source, trace, frame, run, returned, rfl, bounded⟩
    exact ⟨finalRep, finalMemory.of_observes observed,
      trace.inorder_eq.trans current.2.2.1, trace.numNodes_eq.trans current.2.2.2⟩
  let initial : {state : Data // valid state} :=
    ⟨(initialTree, initialHeap, initialEntry), represented, memory, rfl, rfl⟩
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
      ∃ outcome : Ram.State w × Nat, advances i (states i).val (states (i + 1)).val outcome := by
    rw [next_state i hi]
    exact (Classical.choose_spec (nextExists i hi (states i).val (states i).property)).2
  let outcomes (i : Nat) : Ram.State w × Nat :=
    if hi : i < count then Classical.choose (transitions i hi) else (Ram.State.initial [], 0)
  have properties (i : Nat) (hi : i < count) :
      advances i (states i).val (states (i + 1)).val (outcomes i) := by
    simpa only [outcomes, dif_pos hi] using Classical.choose_spec (transitions i hi)
  let history : SplayRunHistory heapLimit placement key keys left right queries count
      initialTree initialHeap initialEntry := {
    trees := fun i => (states i).val.1
    heaps := fun i => (states i).val.2.1
    entries := fun i => (states i).val.2.2
    targets := fun i => (outcomes i).1
    steps := fun i => (outcomes i).2
    initial_tree := rfl
    initial_heap := rfl
    initial_entry := rfl
    represented := fun i _ => (states i).property.1
    memory := fun i _ => (states i).property.2.1
    inorder := fun i _ => (states i).property.2.2.1
    source := fun i hi => (properties i hi).1
    trace := fun i hi => (properties i hi).2.1
    frame := fun i hi => (properties i hi).2.2.1
    run := fun i hi => (properties i hi).2.2.2.1
    returned := fun i hi => (properties i hi).2.2.2.2.1
    resumed := fun i hi => (properties i hi).2.2.2.2.2.1
    instruction_bound := fun i hi => (properties i hi).2.2.2.2.2.2 }
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
    (hw : 0 < w) (key : Nat → Nat) (keys left right : Buffer .nat)
    (queries : Nat → Nat) (count : Nat) (initialTree : Tree Nat) {initialHeap : Heap}
    (represented : Rep key keys left right initialHeap initialTree)
    (unique : initialTree.inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right)
    (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queriesFit : ∀ i, i < count → queries i < 2 ^ w)
    (initialEntry : Ram.Source.State w)
    (memory : HeapRep placement heapLimit initialHeap initialEntry)
    (codeCapacity : (lowerCode Implementation.program Implementation.splayId).length < 2 ^ w)
    (stackCapacity : splaySequenceCapacity heapLimit initialTree.numNodes < 2 ^ w) :
    ∃ history : SplayRunHistory heapLimit placement key keys left right queries count
        initialTree initialHeap initialEntry,
      ((∑ i ∈ Finset.range count, history.steps i : Nat) : ℝ) ≤
        (splayInstructionFactor : ℝ) * ((count : ℝ) *
          (3 * Real.logb 2 ((initialTree.numNodes + 1 : Nat) : ℝ) + 2) +
          (initialTree.numNodes : ℝ) *
            Real.logb 2 ((initialTree.numNodes + 1 : Nat) : ℝ)) := by
  obtain ⟨history, _⟩ := splay_sequence_runUntil hw key keys left right queries count initialTree
    represented unique keysLeft keysRight leftRight keysFit leftFit rightFit queriesFit
    initialEntry memory codeCapacity stackCapacity
  refine ⟨history, ?_⟩
  have bound := sum_steps_le_log
    (trees := history.trees)
    (focus := fun i => searchFocus key (queries i) (history.trees i))
    (rotations := fun i => searchDepth key (queries i) (history.trees i))
    (steps := history.steps) (m := count) (K := splayInstructionFactor)
    history.trace history.instruction_bound
  simpa only [history.initial_tree] using bound

end Complexity.Language.Examples.Splay
