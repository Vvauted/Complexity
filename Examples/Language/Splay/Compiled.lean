/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Correctness
import Examples.Language.Splay.Cost
import Complexity.Computability.Ram.Compiler.Language.CostExecution
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
theorem splayArgs_fits {w : Nat} {key : Nat → Nat} {keys left right : Buffer .nat}
    {heap : Heap} {tree : Tree Nat} (represented : Rep key keys left right heap tree)
    {query : Nat} (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queryFit : query < 2 ^ w) :
    EnvFits w (splayArgs keys left right (root tree) query) := by
  simp only [splayArgs, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty,
    keysFit, leftFit, rightFit, root_fits represented keysFit, queryFit, and_self]

/-- A convenient name for the independently proved full function-body bound. -/
def splayBodyBound (key : Nat → Nat) (query : Nat) (tree : Tree Nat) : Nat :=
  splayLayerBound * (searchDepth key query tree + 1) + 2

/-- The source domain together with word ranges. The heap range is already a
field of the target representation; alias restrictions are those of splay itself. -/
def splayFeasible (w : Nat) (key : Nat → Nat) (query : Nat) (tree : Tree Nat)
    (args : Env Implementation.signatures[Implementation.splayId].params) (heap : Heap) : Prop :=
  splayCostPre key query tree args heap ∧
    args.head.Disjoint args.tail.head ∧ args.head.Disjoint args.tail.tail.head ∧
    args.tail.head.Disjoint args.tail.tail.head ∧ EnvFits w args ∧ HeapFits w heap

/-- The shared finite-execution rule supplies realization without another tree
induction. The established instruction bound is a conservative stack capacity,
not a fuel argument used to prove source termination. -/
theorem splay_realizable {w : Nat} (hw : 0 < w) (key : Nat → Nat) (query : Nat)
    (tree : Tree Nat) (unique : tree.inorder.Nodup) :
    FunctionRealizable Implementation.program w (splayBodyBound key query tree)
      Implementation.splayId (splayFeasible w key query tree) := by
  have lifted := FunctionRealizable.of_rangePreserving hw (program_rangePreserving w)
    (splay_total key query tree unique) (splay_costBound_at key query tree)
    (depth := splayBodyBound key query tree) (fun _ _ _ _ => Nat.le_refl _)
  intro args heap input
  rcases input with ⟨priced, keysLeft, keysRight, leftRight, arguments, cells⟩
  exact lifted args heap
    ⟨⟨priced.1, priced.2.1, priced.2.2, keysLeft, keysRight, leftRight⟩,
      priced, arguments, cells⟩

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

/-- Execute the same verified access on the word RAM. The returned count is
the actual halted runner's count, including calls, returns and the final halt.
The tree certificate and memory frame concern that execution's actual result.
Storage is preloaded; source termination has no resource premise, while this
finite-word realization requires the stated ranges and code/stack capacity. -/
theorem splay_runUntil {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (hw : 0 < w) (key : Nat → Nat) (keys left right : Buffer .nat)
    (query : Nat) (tree : Tree Nat) {heap : Heap}
    (represented : Rep key keys left right heap tree) (unique : tree.inorder.Nodup)
    (keysLeft : keys.Disjoint left) (keysRight : keys.Disjoint right)
    (leftRight : left.Disjoint right)
    (keysFit : keys.length < 2 ^ w) (leftFit : left.length < 2 ^ w)
    (rightFit : right.length < 2 ^ w) (queryFit : query < 2 ^ w)
    (entry : Ram.Source.State w) (memory : HeapRep placement heapLimit heap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.splayId).length < 2 ^ w)
    (stackCapacity : heapLimit + (splayBodyBound key query tree + 1) *
      Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w) :
    ∃ (final : Tree Nat) (finish : Heap) (targetFinish : Ram.Source.State w)
        (steps : Nat) (target : Ram.State w),
      Implementation.splay keys left right (root tree) query heap =
        Part.some (.ok (root final), finish) ∧
      Rep key keys left right finish final ∧
      SplayTrace (searchFocus key query tree) tree final (searchDepth key query tree) ∧
      Heap.PreservesOutside (linkCells left right tree) heap finish ∧
      HeapRep placement heapLimit finish targetFinish ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.splayId.val
          (contextSize (Implementation.signatures[Implementation.splayId.val]'
            Implementation.splayId.isLt).params)
          heapLimit (envWords placement (splayArgs keys left right (root tree) query)) entry =
        some ⟨target, steps, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords placement (τ := .nat) (root final) ∧
      Ram.Source.State.Observes heapLimit 0 targetFinish target ∧
      steps ≤ splayInvocationBound key query tree ∧
      steps ≤ splayInstructionFactor * (searchDepth key query tree + 1) := by
  have arguments : EnvFits w (splayArgs keys left right (root tree) query) :=
    splayArgs_fits represented keysFit leftFit rightFit queryFit
  have priced : splayCostPre key query tree
      (splayArgs keys left right (root tree) query) heap := ⟨rfl, rfl, represented⟩
  obtain ⟨value, finish, targetFinish, bodySteps, target, evaluated, property,
      _, finalMemory, execution, returned, observed, _, _, bounded⟩ :=
    (splay_realizable hw key query tree unique).runUntil_le
      (splay_total key query tree unique) (splay_costBound_at key query tree) hw
      (splayArgs keys left right (root tree) query) heap arguments
      ⟨priced, keysLeft, keysRight, leftRight, arguments, memory.heapFits⟩
      ⟨rfl, rfl, represented, keysLeft, keysRight, leftRight⟩ priced entry memory
      codeCapacity stackCapacity
  obtain ⟨final, rfl, finalRep, trace, frame⟩ := property
  refine ⟨final, finish, targetFinish, _, target, ?_, finalRep, trace, frame,
    finalMemory, execution, returned, observed, bounded,
    bounded.trans (splayInvocationBound_le key query tree)⟩
  simpa only [Implementation.splay, splayArgs] using evaluated

end Complexity.Language.Examples.Splay
