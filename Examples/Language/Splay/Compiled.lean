/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Correctness
import Examples.Language.Splay.Cost
import Examples.Language.Splay.Depth
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Realization.Finite

/-!
# Executing the verified splay source on the word RAM

The source proof establishes successful termination and the mathematical tree
result independently of resources. The program only copies or compares stored
words, so the shared range-preserving-fragment theorem supplies realization
without a second proof of the algorithm or an algorithm-specific register adapter.

Input representation, word ranges, emitted-code capacity and stack capacity
remain explicit. The input arrays are preloaded; their loading and external
serialization are outside this invocation boundary.
-/

namespace Complexity.Language.Examples.Splay

open BufferTree Ram.LanguageCompiler

set_option maxRecDepth 2048 in
/-- Every declared splay function belongs to the checked copy/compare/read/write
fragment. Recursive bodies are checked once, not unfolded along an execution. -/
theorem program_rangePreserving (w : Nat) :
    ∀ fn, RangePreserving w (Implementation.program.body fn) := by
  intro fn
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j =>
    Fin.cases ?_ (fun k => Fin.elim0 k) j) i) fn
  · change RangePreserving w Implementation.rotateRightBody
    simp [Implementation.rotateRightBody, RangePreserving, AtomBounded]
  · change RangePreserving w Implementation.rotateLeftBody
    simp [Implementation.rotateLeftBody, RangePreserving, AtomBounded]
  · change RangePreserving w Implementation.splayBody
    simp [Implementation.splayBody, RangePreserving, PrimBounded, AtomBounded, ArgsBounded]

/-- A represented root fits whenever its field arrays do; empty input uses the
fitting zero sentinel. Node-index safety comes from `Rep`, not a new hypothesis. -/
theorem root_fits {w : Nat} {key : Nat → Nat} {keys left right : Buffer .nat}
    {heap : Heap} {tree : Tree Nat} (represented : Rep key keys left right heap tree)
    (keysFit : keys.length < 2 ^ w) : root tree < 2 ^ w := by
  cases tree with
  | nil => exact Nat.two_pow_pos w
  | node id a b =>
      exact Nat.lt_of_lt_of_le (represented.index_lt (by simp)).1 (Nat.le_of_lt keysFit)

/-- The ordinary buffer lengths and query range suffice for the generated
argument environment; root range is inherited from the represented input. -/
theorem splay_args_fits {w : Nat} {key : Nat → Nat} {keys left right : Buffer .nat}
    {heap : Heap} {tree : Tree Nat} (represented : Rep key keys left right heap tree)
    {query : Nat} (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queryFit : query < 2 ^ w) :
    EnvFits w (Implementation.splay_args keys left right (root tree) query) := by
  simp only [Implementation.splay_args, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty,
    keysFit, leftFit, rightFit, root_fits represented keysFit, queryFit, and_self]

/-- A convenient name for the independently proved full function-body bound. -/
def splayBodyBound (key : Nat → Nat) (query : Nat) (tree : Tree Nat) : Nat :=
  splayLayerBound * (searchDepth key query tree + 1) + 2

/-- The source domain together with word ranges. The heap range is already a
field of the target representation; alias restrictions are those of splay itself. -/
def splayFeasible (w : Nat) (key : Nat → Nat) (query : Nat) (tree : Tree Nat)
    (args : Env Implementation.signatures[Implementation.splayId].params) (heap : Heap) : Prop :=
  args.tail.tail.tail.head = root tree ∧ args.tail.tail.tail.tail.head = query ∧
    Input key args.head args.tail.head args.tail.tail.head tree heap ∧
    EnvFits w args ∧ HeapFits w heap

/-- The shared finite-execution rule supplies realization without another tree
correctness induction. The separate nesting bound follows recursive calls, not
the instruction count, and is not fuel for source termination. -/
theorem splay_realizable {w : Nat} (hw : 0 < w) (key : Nat → Nat) (query : Nat)
    (tree : Tree Nat) :
    FunctionRealizable Implementation.program w (splayDepthBound tree)
      Implementation.splayId (splayFeasible w key query tree) := by
  have lifted := FunctionRealizable.of_rangePreserving_depth hw (program_rangePreserving w)
    (splay_total key query tree) (splay_depthBound_at key query tree)
    (depth := splayDepthBound tree) (fun _ _ _ _ => Nat.le_refl _)
  intro args heap input
  rcases input with ⟨rootEq, queryEq, input, arguments, cells⟩
  exact lifted args heap
    ⟨⟨rootEq, queryEq, input⟩, ⟨rootEq, queryEq, input.represented⟩, arguments, cells⟩

/-- The complete invocation bound includes the actual outer call and halt. -/
def splayInvocationBound (key : Nat → Nat) (query : Nat) (tree : Tree Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.splayId)
    (splayBodyBound key query tree) + 1

/-- A fixed compiler-derived coefficient for charging each search edge and
the initial invocation. This includes the empty-tree and final-halt overhead. -/
def splayInstructionFactor : Nat :=
  splayLayerBound + 2 +
    Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
      (lowerFunc Implementation.program Implementation.splayId) 0 + 1

/-- Absorb the actual fixed invocation overhead into one charge per search
edge, retaining one charge when the input tree is empty. -/
theorem splayInvocationBound_le (key : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    splayInvocationBound key query tree ≤
      splayInstructionFactor * (searchDepth key query tree + 1) := by
  have overhead := Nat.mul_le_mul_left
    (2 + Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
      (lowerFunc Implementation.program Implementation.splayId) 0 + 1)
    (Nat.succ_le_succ (Nat.zero_le (searchDepth key query tree)))
  simp only [Nat.succ_eq_add_one, Nat.mul_one] at overhead
  simp only [splayInvocationBound, splayBodyBound, splayInstructionFactor,
    Ram.LocalCompiler.Function.callSteps_eq, Nat.add_mul] at overhead ⊢
  omega

/-- Execute the verified access with the shared typed RAM publication interface.
The outcome owns the actual halted runner result, source result and final memory;
the mathematical tree postcondition and independent step bounds describe it.
Launch conditions expose word ranges and code/stack capacity, not a time budget.
The preloaded-call boundary includes the call, return and final halt. -/
theorem splay_execute {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (key : Nat → Nat) (keys left right : Buffer .nat) (query : Nat) (tree : Tree Nat)
    {heap : Heap} (input : Input key keys left right tree heap) {entry : Ram.Source.State w}
    (launch : FunctionLaunch Implementation.program Implementation.splayId
      (splayDepthBound tree) heapLimit placement
      (Implementation.splay_args keys left right (root tree) query) heap entry) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.splayId heapLimit placement
        (Implementation.splay_args keys left right (root tree) query) heap entry,
      Post key keys left right query tree heap outcome.value outcome.heap ∧
      outcome.result.steps ≤ splayInvocationBound key query tree ∧
      outcome.result.steps ≤ splayInstructionFactor * (searchDepth key query tree + 1) := by
  have priced : splayCostPre key query tree
      (Implementation.splay_args keys left right (root tree) query) heap :=
    ⟨rfl, rfl, input.represented⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (splay_realizable launch.positive key query tree).execute_le
      (splay_total key query tree) (splay_costBound_at key query tree) launch
      ⟨rfl, rfl, input, launch.arguments, launch.memory.heapFits⟩ ⟨rfl, rfl, input⟩ priced
  exact ⟨outcome, property, bounded, bounded.trans (splayInvocationBound_le key query tree)⟩

end Complexity.Language.Examples.Splay
