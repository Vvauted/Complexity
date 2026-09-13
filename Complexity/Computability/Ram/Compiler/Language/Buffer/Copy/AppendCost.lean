/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Allocation
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.CallSequence
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.Validity

/-!
# Allocation-aware linear cost of the existing buffer append

The actual `Copy.append` allocates and initializes its fresh destination, copies
the left input, copies the right input, then returns that destination. Its cost
proof reuses the existing copy loop bound and source contracts at the real
intermediate heaps. Inputs may overlap: only the freshly allocated destination
needs to be disjoint. No readiness or finite-word assumption restricts this
conditional cost contract; those belong to the independent launch proof.

The size envelopes count initialization, both calls, their sequence dispatch,
and the actual return. The whole-invocation envelope additionally counts its
outer call and final halt through the existing compiler cost function.
-/

namespace Ram.LanguageCompiler.BufferCopy

open Complexity.Language
open Complexity.Language.Buffer

/-- The same copying body has its existing bound on any actual arena trace.
The local no-allocation check permits its actual target writes. -/
theorem copyInto_arenaCostBound (input output : Array Nat) (w heapLimit depth : Nat) :
    FunctionArenaCostBound Copy.program (Copy.program.body Copy.copyIntoId) id
      (fun args heap => args.head.Contents heap input ∧
        args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
        args.tail.tail.head + input.size ≤ output.size)
      w heapLimit depth (fun _ => copyIntoBodyBound input.size) := by
  apply FunctionArenaCostBound.of_noAllocationOrCalls (copyInto_costBound input output)
  simp [Copy.program, Copy.copyIntoBody, Copy.copyInto_loop1.Code,
    Copy.copyInto_loop1.Guard, Copy.copyInto_loop1.Body, NoAllocationOrCalls]

private abbrev appendCost (leftSize rightSize : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (leftValues rightValues : Array Nat)
      (left right : Buffer .nat) (heap : Heap),
      leftValues.size = leftSize → rightValues.size = rightSize →
      left.Contents heap leftValues → right.Contents heap rightValues →
      StmtArenaCostBound Copy.program w heapLimit 1
        (Copy.program.body Copy.appendId) ⟨Copy.append_args left right, heap⟩ bound } := ⟨_, by
  intro w heapLimit leftValues rightValues left right heap leftEq rightEq
    observedLeft observedRight
  let totalSize := left.length + right.length
  let allocated := heap.alloc (τ := .nat) totalSize 0
  let target := allocated.1
  let initialValues : Array Nat := Array.replicate totalSize 0
  have leftNow : left.Contents allocated.2 leftValues := observedLeft.alloc totalSize 0
  have rightNow : right.Contents allocated.2 rightValues := observedRight.alloc totalSize 0
  have initialized : target.Contents allocated.2 initialValues := heap.alloc_contents totalSize 0
  have separatedLeft : target.Disjoint left := observedLeft.valid.rooted.disjoint_alloc totalSize 0
  have separatedRight : target.Disjoint right := observedRight.valid.rooted.disjoint_alloc totalSize 0
  have leftExtent : 0 + leftValues.size ≤ initialValues.size := by
    simp only [initialValues, Array.size_replicate, Nat.zero_add]
    dsimp only [totalSize]
    have := observedLeft.size_eq
    omega
  have rightExtent : left.length + rightValues.size ≤
      (copied leftValues initialValues 0 leftValues.size).size := by
    simp only [copied_size, initialValues, Array.size_replicate]
    dsimp only [totalSize]
    have := observedRight.size_eq
    omega
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost
    apply StmtArenaCostBound.alloc
    apply StmtArenaCostBound.call_seq_at_of_spec
      (copyInto_arenaCostBound leftValues initialValues w heapLimit 0)
      (copyInto_total leftValues initialValues)
      (Copy.copyInto_args left target 0)
    · rfl
    · exact ⟨leftNow, initialized, separatedLeft, leftExtent⟩
    · exact ⟨leftNow, initialized, separatedLeft, leftExtent⟩
    · intro value middle firstPost
      change left.Contents middle leftValues ∧
        target.Contents middle (copied leftValues initialValues 0 leftValues.size) ∧
        target.PreservesOutside allocated.2 middle at firstPost
      have rightAfter : right.Contents middle rightValues :=
        firstPost.2.2 right rightValues separatedRight rightNow
      repeat' apply StmtArenaCostBound.letPrim
      apply StmtArenaCostBound.call_seq_at_of_spec
        (copyInto_arenaCostBound rightValues
          (copied leftValues initialValues 0 leftValues.size) w heapLimit 0)
        (copyInto_total rightValues (copied leftValues initialValues 0 leftValues.size))
        (Copy.copyInto_args right target left.length)
      · rfl
      · exact ⟨rightAfter, firstPost.2.1, separatedRight, rightExtent⟩
      · exact ⟨rightAfter, firstPost.2.1, separatedRight, rightExtent⟩
      · intro value finish secondPost
        ram_source_arena_cost
  · simp only [Copy.append_args, State.cons,
      Atom.eval, Prim.eval, Env.cons_here, Env.cons_there,
      ← observedLeft.size_eq, ← observedRight.size_eq, leftEq, rightEq]
    exact Nat.le_refl _⟩

/-- The compiler-derived core envelope includes real allocation initialization
and both actual copying calls; it omits only the outer function initialization. -/
def appendCoreBound (leftSize rightSize : Nat) : Nat :=
  (appendCost leftSize rightSize).val

/-- Bound the same allocating source statement from ordinary input contents.
There are no cell ranges, word-width inequalities or proposed readiness premises. -/
theorem append_stmt_costBound (leftValues rightValues : Array Nat)
    (left right : Buffer .nat) (heap : Heap) (w heapLimit : Nat)
    (observedLeft : left.Contents heap leftValues)
    (observedRight : right.Contents heap rightValues) :
    StmtArenaCostBound Copy.program w heapLimit 1 (Copy.program.body Copy.appendId)
      ⟨Copy.append_args left right, heap⟩
      (appendCoreBound leftValues.size rightValues.size) := by
  intro finish control execution cursor finalCursor ready steps cost
  exact (appendCost leftValues.size rightValues.size).property
    w heapLimit leftValues rightValues left right heap rfl rfl observedLeft observedRight
    execution ready cost

/-- Each input element pays for one initializer iteration and one copy round.
All remaining compiler-generated costs are fixed overhead. -/
theorem appendCoreBound_eq (leftSize rightSize : Nat) :
    appendCoreBound leftSize rightSize =
      (14 + copyIntoGuardCost.val + copyIntoBodyCost.val + 10) *
        (leftSize + rightSize) + appendCoreBound 0 0 := by
  simp only [appendCoreBound, callCost,
    Ram.LocalCompiler.Function.callSteps_eq]
  rw [copyIntoBodyBound_eq leftSize, copyIntoBodyBound_eq rightSize]
  ring

/-- The complete lowered function-body envelope uses only total input size,
and adds the existing two-instruction function initialization exactly once. -/
def appendBodyBound (size : Nat) : Nat := appendCoreBound size 0 + 2

/-- Splitting the same total size differently does not change the body envelope. -/
theorem appendBodyBound_sizes (leftSize rightSize : Nat) :
    appendCoreBound leftSize rightSize + 2 = appendBodyBound (leftSize + rightSize) := by
  unfold appendBodyBound
  rw [appendCoreBound_eq leftSize rightSize,
    appendCoreBound_eq (leftSize + rightSize) 0]
  simp only [Nat.add_zero]

/-- The actual callable append body has a total-size bound under just its
original contents precondition. Both inputs may refer to overlapping storage. -/
theorem append_costBound (leftValues rightValues : Array Nat) (w heapLimit : Nat) :
    FunctionArenaCostBound Copy.program (Copy.program.body Copy.appendId)
      (fun input : Buffer .nat × Buffer .nat => Copy.append_args input.1 input.2)
      (fun input heap => input.1.Contents heap leftValues ∧ input.2.Contents heap rightValues)
      w heapLimit 1 (fun _ => appendBodyBound (leftValues.size + rightValues.size)) := by
  rw [← appendBodyBound_sizes]
  apply FunctionArenaCostBound.of_stmt
  intro input heap allowed
  intro finish control execution cursor finalCursor ready steps cost
  exact append_stmt_costBound leftValues rightValues input.1 input.2 heap w heapLimit
    allowed.1 allowed.2 execution ready cost

/-- The body envelope is affine in the sum of the two native array lengths. -/
theorem appendBodyBound_eq (size : Nat) :
    appendBodyBound size =
      (14 + copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size + appendBodyBound 0 := by
  unfold appendBodyBound
  rw [appendCoreBound_eq size 0]
  simp only [Nat.add_zero, Nat.add_assoc]

/-- Add the actual outer invocation and final halt to the proved body budget. -/
def appendInvocationBound (size : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Copy.program)
    (lowerFunc Copy.program Copy.appendId) (appendBodyBound size) + 1

/-- The invocation keeps exactly the body envelope's linear coefficient. -/
theorem appendInvocationBound_eq (size : Nat) :
    appendInvocationBound size =
      (14 + copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size +
        appendInvocationBound 0 := by
  unfold appendInvocationBound
  rw [appendBodyBound_eq size]
  simp only [Ram.LocalCompiler.Function.callSteps_eq]
  ring

private theorem isBigO_of_affine (bound : Nat → Nat) (coefficient : Nat)
    (affine : ∀ size, bound size = coefficient * size + bound 0) :
    Asymptotics.IsBigO Filter.atTop (fun size => (bound size : ℝ))
      (fun size : Nat => (size : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((coefficient + bound 0 : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with size positive
  have fixed : bound 0 ≤ size * bound 0 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (bound 0) positive
  have bounded : bound size ≤ (coefficient + bound 0) * size := by
    rw [affine]
    calc
      coefficient * size + bound 0 ≤ coefficient * size + size * bound 0 :=
        Nat.add_le_add_left fixed _
      _ = _ := by ring
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr bounded : (bound size : ℝ) ≤ (((coefficient + bound 0) * size : Nat) : ℝ))

/-- The body cost is linear in total native input size. -/
theorem isBigO_appendBodyBound :
    Asymptotics.IsBigO Filter.atTop (fun size => (appendBodyBound size : ℝ))
      (fun size : Nat => (size : ℝ)) :=
  isBigO_of_affine appendBodyBound _ appendBodyBound_eq

/-- The complete invocation envelope is linear in total native input size. -/
theorem isBigO_appendInvocationBound :
    Asymptotics.IsBigO Filter.atTop (fun size => (appendInvocationBound size : ℝ))
      (fun size : Nat => (size : ℝ)) :=
  isBigO_of_affine appendInvocationBound _ appendInvocationBound_eq

end Ram.LanguageCompiler.BufferCopy
