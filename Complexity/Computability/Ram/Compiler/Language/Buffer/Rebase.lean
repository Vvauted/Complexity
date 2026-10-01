/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Rebase
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.LoopTactic
import Complexity.Computability.Ram.Compiler.Language.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Allocation
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.CallSequence
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.Validity
import Mathlib.Tactic.Ring

/-!
# Linear costs of rebasing a buffer

The same copied-prefix contracts supply progress to the compiler loop rule.
The allocating wrapper additionally pays initialization, the real copying call
and its return. These conditional instruction bounds do not assume or establish
finite-word readiness, capacity, or a different source execution.
-/

namespace Ram.LanguageCompiler.BufferRebase

open Complexity.Language
open Complexity.Language.Buffer

/-- The actual guard has one uniform compiler-derived instruction budget. -/
def copyIntoGuardCost : { bound : Nat //
    ∀ (locals : Rebase.copyInto_loop1.Locals) (heap : Heap),
      StmtCostBound Rebase.program Rebase.copyInto_loop1.Guard
        ⟨Rebase.copyInto_loop1.View.symm locals, heap⟩ bound } := ⟨_, by
  intro locals heap
  ram_source_cost_step⟩

/-- The inferred guard budget includes its length comparison and Boolean return. -/
theorem copyInto_guard_costBound (locals : Rebase.copyInto_loop1.Locals) (heap : Heap) :
    StmtCostBound Rebase.program Rebase.copyInto_loop1.Guard
      ⟨Rebase.copyInto_loop1.View.symm locals, heap⟩ copyIntoGuardCost.val :=
  copyIntoGuardCost.property locals heap

/-- Infer the actual body's read, subtraction, store and index-update costs
uniformly before introducing any values or heap. -/
def copyIntoBodyCost : { bound : Nat //
    ∀ (locals : Rebase.copyInto_loop1.Locals) (heap : Heap),
      StmtCostBound Rebase.program Rebase.copyInto_loop1.Body
        ⟨Rebase.copyInto_loop1.View.symm locals, heap⟩ bound } := ⟨_, by
  intro locals heap
  ram_source_cost_step⟩

/-- Every actual body execution is bounded by the same structural certificate. -/
theorem copyInto_body_costBound (locals : Rebase.copyInto_loop1.Locals) (heap : Heap) :
    StmtCostBound Rebase.program Rebase.copyInto_loop1.Body
      ⟨Rebase.copyInto_loop1.View.symm locals, heap⟩ copyIntoBodyCost.val :=
  copyIntoBodyCost.property locals heap

/-- Pay for the remaining rounds and the final false test with the existing
loop rule's normal-round and exit charges. -/
def copyIntoLoopBound (remaining : Nat) : Nat :=
  StmtCostBound.whileLinearBound copyIntoGuardCost.val copyIntoBodyCost.val remaining

/-- The copied-prefix contract advances the index by one on each normal round.
Its mathematical contents/frame proof is reused unchanged in this potential bound. -/
theorem copyInto_loop_costBound (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) (index : Nat) (heap : Heap)
    (current : rebaseInvariant source target base input output index heap)
    (separated : target.Disjoint source) (extent : input.size ≤ output.size) :
    StmtCostBound Rebase.program Rebase.copyInto_loop1.Code
      ⟨Rebase.copyInto_loop1.View.symm (index, source, target, base, ()), heap⟩
      (copyIntoLoopBound (input.size - index)) := by
  ram_source_loop_cost (remaining := fun locals _ => input.size - locals.1)
    using (rebase_guard source target base input output),
      (rebase_body source target base input output separated extent)
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
      FunctionCostBound Rebase.program Rebase.copyIntoId
        (fun args heap => args.head.Contents heap input ∧
          args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
          input.size ≤ output.size)
        (fun _ _ => bound) } := ⟨_, by
  intro input output sameSize
  ram_source_cost_intro (source target base)
  intro heap allowed
  rcases allowed with ⟨sourceContents, targetContents, separated, extent⟩
  ram_source_cost_step
  have current : rebaseInvariant source target base input output 0 heap :=
    ⟨Nat.zero_le _, sourceContents, by simpa only [copied_zero] using targetContents⟩
  have bound : StmtCostBound Rebase.program Rebase.copyInto_loop1.Code
      ⟨Rebase.copyInto_loop1.View.symm (0, source, target, base, ()), heap⟩
      (copyIntoLoopBound (input.size - 0)) :=
    copyInto_loop_costBound source target base input output 0 heap current separated extent
  simp only [Nat.sub_zero, sameSize] at bound
  ram_source_locals Rebase.copyInto_loop1 at bound
  exact @bound⟩

/-- The complete lowered function-body budget depends only on the copied
length. It includes function initialization, but not an enclosing caller's ABI. -/
def copyIntoBodyBound (size : Nat) : Nat := (copyIntoCost size).val

/-- The same source function has the inferred bound under its existing
mathematical copy contract, independently of any proposed time budget. -/
theorem copyInto_costBound (input output : Array Nat) :
    FunctionCostBound Rebase.program Rebase.copyIntoId
      (fun args heap => args.head.Contents heap input ∧
        args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
        input.size ≤ output.size)
      (fun _ _ => copyIntoBodyBound input.size) :=
  (copyIntoCost input.size).property input output rfl

/-- Both the per-element coefficient and fixed overhead come from the inferred
compiler budgets. Heap contents and destination bases do not change them. -/
theorem copyIntoBodyBound_eq (size : Nat) :
    copyIntoBodyBound size =
      (copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size + copyIntoBodyBound 0 := by
  simp only [copyIntoBodyBound, copyIntoLoopBound, StmtCostBound.whileLinearBound]
  omega


/-- Lift the same nonallocating worker bound to arena executions. -/
theorem copyInto_arenaCostBound (input output : Array Nat) (w heapLimit depth : Nat) :
    FunctionArenaCostBound Rebase.program (Rebase.program.body Rebase.copyIntoId) id
      (fun args heap => args.head.Contents heap input ∧
        args.tail.head.Contents heap output ∧ args.tail.head.Disjoint args.head ∧
        input.size ≤ output.size)
      w heapLimit depth (fun _ => copyIntoBodyBound input.size) := by
  apply FunctionArenaCostBound.of_noAllocationOrCalls (copyInto_costBound input output)
  simp [Rebase.program, Rebase.copyIntoBody, Rebase.copyInto_loop1.Code,
    Rebase.copyInto_loop1.Guard, Rebase.copyInto_loop1.Body, NoAllocationOrCalls]

private abbrev copyCost (size : Nat) : { bound : Nat //
    ∀ (w heapLimit : Nat) (input : Array Nat) (source : Buffer .nat) (base : Nat) (heap : Heap),
      input.size = size → source.Contents heap input →
      StmtArenaCostBound Rebase.program w heapLimit 1
        (Rebase.program.body Rebase.copyId) ⟨Rebase.copy_args source base, heap⟩ bound } := ⟨_, by
  intro w heapLimit input source base heap sameSize observed
  let allocated := heap.alloc (τ := .nat) source.length 0
  let target := allocated.1
  let initialValues := Array.replicate source.length 0
  have sourceNow : source.Contents allocated.2 input := observed.alloc source.length 0
  have initialized : target.Contents allocated.2 initialValues :=
    heap.alloc_contents source.length 0
  have separated : target.Disjoint source :=
    observed.valid.rooted.disjoint_alloc source.length 0
  have extent : input.size ≤ initialValues.size := by
    simpa only [initialValues, Array.size_replicate] using observed.size_eq.le
  apply StmtArenaCostBound.mono
  · ram_source_arena_cost
    apply StmtArenaCostBound.alloc
    apply StmtArenaCostBound.call_seq_at_of_spec
      (copyInto_arenaCostBound input initialValues w heapLimit 0)
      (rebaseInto_total input initialValues)
      (Rebase.copyInto_args source target base)
    · rfl
    · exact ⟨sourceNow, initialized, separated, extent⟩
    · exact ⟨sourceNow, initialized, separated, extent⟩
    · intro value finish completed
      ram_source_arena_cost
  · simp only [Rebase.copy_args, State.cons, Atom.eval, Prim.eval,
      Env.cons_here, ← observed.size_eq, sameSize]
    exact Nat.le_refl _⟩

/-- Actual initialization and copying costs before enclosing function setup. -/
def copyCoreBound (size : Nat) : Nat := (copyCost size).val

/-- The bound follows the allocating source body at the supplied input heap. -/
theorem copy_stmt_costBound (input : Array Nat) (source : Buffer .nat) (base : Nat)
    (heap : Heap) (w heapLimit : Nat) (observed : source.Contents heap input) :
    StmtArenaCostBound Rebase.program w heapLimit 1 (Rebase.program.body Rebase.copyId)
      ⟨Rebase.copy_args source base, heap⟩ (copyCoreBound input.size) :=
  (copyCost input.size).property w heapLimit input source base heap rfl observed

/-- Every element pays for initialized allocation and one actual rebasing round. -/
theorem copyCoreBound_eq (size : Nat) :
    copyCoreBound size =
      (14 + copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size + copyCoreBound 0 := by
  simp only [copyCoreBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  rw [copyIntoBodyBound_eq size]
  ring

/-- Callable cost includes function initialization exactly once. -/
def copyBodyBound (size : Nat) : Nat := copyCoreBound size + 2

/-- Compose the actual allocator and worker under only the contents precondition. -/
theorem copy_arenaCostBound (input : Array Nat) (w heapLimit : Nat) :
    FunctionArenaCostBound Rebase.program (Rebase.program.body Rebase.copyId)
      (fun args : Buffer .nat × Nat => Rebase.copy_args args.1 args.2)
      (fun args heap => args.1.Contents heap input)
      w heapLimit 1 (fun _ => copyBodyBound input.size) :=
  FunctionArenaCostBound.of_stmt (fun args heap observed =>
    copy_stmt_costBound input args.1 args.2 heap w heapLimit observed)

/-- The complete body envelope is affine even when the selected interval is empty. -/
theorem copyBodyBound_eq (size : Nat) :
    copyBodyBound size =
      (14 + copyIntoGuardCost.val + copyIntoBodyCost.val + 10) * size + copyBodyBound 0 := by
  unfold copyBodyBound
  rw [copyCoreBound_eq size]
  omega

end Ram.LanguageCompiler.BufferRebase
