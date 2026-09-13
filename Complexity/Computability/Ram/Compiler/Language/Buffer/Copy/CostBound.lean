/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.LoopTactic
import Complexity.Computability.Ram.Compiler.Language.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring

/-!
# Linear instruction bounds for the existing buffer-copy loop

The cost proof follows `Buffer.Copy.copyInto` itself. Its original guard/body
contracts supply the copied-prefix invariant and index advance; the existing
compiler rules supply all structural charges. A size-only potential includes
the last false guard, and the enclosing function adds its own setup and return.

These are conditional bounds on actual executions, not new termination or
word-range assumptions for the source contracts. They can be combined with an
independent finite-word realization through the existing arena resource bridge.
Allocation and the enclosing calls of `Copy.copy` and `Copy.append` retain
their own costs; neither is silently included in this copying-loop bound.
-/

namespace Ram.LanguageCompiler.BufferCopy

open Complexity.Language
open Complexity.Language.Buffer

/-- The actual guard has one uniform compiler-derived instruction budget. -/
def copyIntoGuardCost : { bound : Nat //
    ∀ (locals : Copy.copyInto_loop1.Locals) (heap : Heap),
      StmtCostBound Copy.program Copy.copyInto_loop1.Guard
        ⟨Copy.copyInto_loop1.View.symm locals, heap⟩ bound } := ⟨_, by
  intro locals heap
  ram_source_cost_step⟩

/-- The inferred guard budget includes its length comparison and Boolean return. -/
theorem copyInto_guard_costBound (locals : Copy.copyInto_loop1.Locals) (heap : Heap) :
    StmtCostBound Copy.program Copy.copyInto_loop1.Guard
      ⟨Copy.copyInto_loop1.View.symm locals, heap⟩ copyIntoGuardCost.val :=
  copyIntoGuardCost.property locals heap

/-- Infer the actual body's read, offset addition, store and index-update costs
uniformly before introducing any values or heap. -/
def copyIntoBodyCost : { bound : Nat //
    ∀ (locals : Copy.copyInto_loop1.Locals) (heap : Heap),
      StmtCostBound Copy.program Copy.copyInto_loop1.Body
        ⟨Copy.copyInto_loop1.View.symm locals, heap⟩ bound } := ⟨_, by
  intro locals heap
  ram_source_cost_step⟩

/-- Every actual body execution is bounded by the same structural certificate. -/
theorem copyInto_body_costBound (locals : Copy.copyInto_loop1.Locals) (heap : Heap) :
    StmtCostBound Copy.program Copy.copyInto_loop1.Body
      ⟨Copy.copyInto_loop1.View.symm locals, heap⟩ copyIntoBodyCost.val :=
  copyIntoBodyCost.property locals heap

/-- Pay for the remaining rounds and the final false test with the existing
loop rule's normal-round and exit charges. -/
def copyIntoLoopBound (remaining : Nat) : Nat :=
  StmtCostBound.whileLinearBound copyIntoGuardCost.val copyIntoBodyCost.val remaining

/-- The copied-prefix contract advances the index by one on each normal round.
Its mathematical contents/frame proof is reused unchanged in this potential bound. -/
theorem copyInto_loop_costBound (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) (index : Nat) (heap : Heap)
    (current : copyInvariant source target offset input output index heap)
    (separated : target.Disjoint source) (extent : offset + input.size ≤ output.size) :
    StmtCostBound Copy.program Copy.copyInto_loop1.Code
      ⟨Copy.copyInto_loop1.View.symm (index, source, target, offset, ()), heap⟩
      (copyIntoLoopBound (input.size - index)) := by
  ram_source_loop_cost (remaining := fun locals _ => input.size - locals.1)
    using (copy_guard source target offset input output),
      (copy_body source target offset input output separated extent)
    costs copyInto_guard_costBound, copyInto_body_costBound
  · intro _ _ _ _ _ ready
    exact ⟨ready.2.2.1, ready.2.2.2.mp rfl⟩
  · intro _ _ _ _ _ _ _ _ completed
    exact completed.2.1
  · rintro ⟨j, ⟨⟩⟩ entry ⟨k, ⟨⟩⟩ afterHeap ⟨l, ⟨⟩⟩ bodyHeap initial ready completed
    have next : l = j + 1 := completed.1.trans (congrArg (· + 1) ready.1)
    have nextBound : l ≤ input.size := completed.2.1.1
    dsimp only
    omega
  · rintro ⟨j, ⟨⟩⟩ entry ⟨k, ⟨⟩⟩ afterHeap initial ready
    have inside : k < input.size := ready.2.2.2.mp rfl
    have same : k = j := ready.1
    dsimp only
    omega
  · exact current

private abbrev copyIntoCost (size : Nat) : { bound : Nat //
    ∀ input output : Array Nat, input.size = size →
      FunctionCostBound Copy.program Copy.copyIntoId
        (fun args heap => args.head.Contents heap input ∧
          args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
          args.tail.tail.head + input.size ≤ output.size)
        (fun _ _ => bound) } := ⟨_, by
  intro input output sameSize
  ram_source_cost_intro (source target offset)
  intro heap allowed
  rcases allowed with ⟨sourceContents, targetContents, separated, extent⟩
  ram_source_cost_step
  have current : copyInvariant source target offset input output 0 heap :=
    ⟨Nat.zero_le _, sourceContents, by simpa only [copied_zero] using targetContents⟩
  have bound : StmtCostBound Copy.program Copy.copyInto_loop1.Code
      ⟨Copy.copyInto_loop1.View.symm (0, source, target, offset, ()), heap⟩
      (copyIntoLoopBound (input.size - 0)) :=
    copyInto_loop_costBound source target offset input output 0 heap current separated extent
  simp only [Nat.sub_zero, sameSize] at bound
  ram_source_locals Copy.copyInto_loop1 at bound
  exact @bound⟩

/-- The complete lowered function-body budget depends only on the copied
length. It includes function initialization, but not an enclosing caller's ABI. -/
def copyIntoBodyBound (size : Nat) : Nat := (copyIntoCost size).val

/-- The same source function has the inferred bound under its existing
mathematical copy contract, independently of any proposed time budget. -/
theorem copyInto_costBound (input output : Array Nat) :
    FunctionCostBound Copy.program Copy.copyIntoId
      (fun args heap => args.head.Contents heap input ∧
        args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
        args.tail.tail.head + input.size ≤ output.size)
      (fun _ _ => copyIntoBodyBound input.size) :=
  (copyIntoCost input.size).property input output rfl

/-- Both the per-element coefficient and fixed overhead come from the inferred
compiler budgets. Heap contents and destination offsets do not change them. -/
theorem copyIntoBodyBound_eq (size : Nat) :
    copyIntoBodyBound size =
      (copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size + copyIntoBodyBound 0 := by
  simp only [copyIntoBodyBound, copyIntoLoopBound, StmtCostBound.whileLinearBound]
  omega

/-- The same proved body envelope is linear in the mathematical source length.
This numerical fact supplies neither a launch nor a new execution. -/
theorem isBigO_copyIntoBodyBound :
    Asymptotics.IsBigO Filter.atTop (fun size => (copyIntoBodyBound size : ℝ))
      (fun size : Nat => (size : ℝ)) := by
  let coefficient := copyIntoGuardCost.val + copyIntoBodyCost.val + 10
  let fixed := copyIntoBodyBound 0
  apply Asymptotics.IsBigO.of_bound ((coefficient + fixed : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with size positive
  have setup : fixed ≤ size * fixed := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right fixed positive
  have bound : copyIntoBodyBound size ≤ (coefficient + fixed) * size := by
    rw [copyIntoBodyBound_eq]
    change coefficient * size + fixed ≤ (coefficient + fixed) * size
    calc
      coefficient * size + fixed ≤ coefficient * size + size * fixed :=
        Nat.add_le_add_left setup _
      _ = (coefficient + fixed) * size := by
        dsimp [coefficient]
        ring
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr bound : (copyIntoBodyBound size : ℝ) ≤
      (((coefficient + fixed) * size : Nat) : ℝ))

end Ram.LanguageCompiler.BufferCopy
