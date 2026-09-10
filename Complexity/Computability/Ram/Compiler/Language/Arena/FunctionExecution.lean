/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Local.Function.Memory

/-!
# Typed results of allocation-aware source invocations

`FunctionArenaLaunch` adds rooted arguments and the actual shared arena to the
existing function capacity. `FunctionArenaExecution` retains the source result,
final placement and cursor together with the same halted RAM state. Its memory
representation uses that actual state's complete data projection, so a subsequent
invocation does not reset private memory or bootstrap the arena again.

The measured invocation retains the specified call depth. The resulting bounds
cover every actual memory access of this invocation, including transient scratch
and stack accesses. They are sufficient physical workspace envelopes, not peak
reachable-live-object counts. Registers, code, I/O and host-side input preparation
remain outside this memory measure.

Correctness and termination require no proposed instruction budget. Readiness
supplies the existing execution and its count; no evaluator, allocator or cost
interpretation is introduced by this publication interface.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Heap observation transfers both represented cells and the shared cursor to
the actual RAM data. Memory outside the heap boundary need not match the source
witness and is retained unchanged by the projection. -/
theorem ArenaRep.of_observes {w cursor heapLimit locals : Nat}
    {placement : Nat → Word w} {heap : Heap}
    {source : Source.State w} {target : Ram.State w}
    (arena : ArenaRep placement cursor heapLimit heap source)
    (observed : Source.State.Observes heapLimit locals source target) :
    ArenaRep placement cursor heapLimit heap (Source.State.ofRam target) := by
  refine ⟨arena.heapRep.of_observes observed, arena.cursor_pos, arena.cursor_le,
    arena.limit_lt, ?_, arena.reserved⟩
  have positive : 0 < heapLimit := lt_of_lt_of_le arena.cursor_pos arena.cursor_le
  exact (observed.heap (0 : Word w) (by simpa only [BitVec.toNat_zero] using positive)).symm.trans
    arena.cursor_eq

/-- Existing backend conditions for one preloaded allocating invocation. The
arena cursor is the current cursor, not a request to initialize it again. -/
structure FunctionArenaLaunch {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {w : Nat} (depth heapLimit : Nat) (placement : Nat → Word w)
    (args : Env (signatures[fn.val]'fn.isLt).params)
    (initialHeap : Heap) (cursor : Nat) (entry : Source.State w) : Prop where
  toFunctionCapacity : FunctionCapacity program fn w depth heapLimit
  arguments : EnvFits (Γ := (signatures[fn.val]'fn.isLt).params) w args
  rooted : args.Rooted initialHeap
  arena : ArenaRep placement cursor heapLimit initialHeap entry

namespace FunctionArenaLaunch

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w depth heapLimit cursor : Nat}
variable {placement : Nat → Word w} {args : Env (signatures[fn.val]'fn.isLt).params}
variable {initialHeap : Heap} {entry : Source.State w}

/-- A launch retains the positive word width of its capacity. -/
theorem positive
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args initialHeap cursor entry) :
    0 < w := launch.toFunctionCapacity.positive

/-- A launch retains the code capacity of the same compiled function. -/
theorem codeCapacity
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args initialHeap cursor entry) :
    (lowerCode program fn).length < 2 ^ w := launch.toFunctionCapacity.codeCapacity

/-- The stack allowance includes the outer function trampoline. -/
theorem stackCapacity
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args initialHeap cursor entry) :
    heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w :=
  launch.toFunctionCapacity.stackCapacity

end FunctionArenaLaunch

/-- Source meaning and resources of the same actual halted allocating call.
The known depth is retained by its measured invocation instead of existentially
hiding it. Final memory includes all actual private stack and shared words. -/
structure FunctionArenaExecution {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {w : Nat} (depth heapLimit : Nat) (placement : Nat → Word w)
    (args : Env (signatures[fn.val]'fn.isLt).params)
    (initialHeap : Heap) (entry : Source.State w) where
  value : Value (signatures[fn.val]'fn.isLt).result
  heap : Heap
  finalPlacement : Nat → Word w
  cursor : Nat
  result : RunResult (Ram.State w)
  sourceFinish : Source.State w
  bodySteps : Nat
  capacity : FunctionCapacity program fn w depth heapLimit
  source : program.eval fn args initialHeap = Part.some (.ok value, heap)
  run : LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
    (contextSize (signatures[fn.val]'fn.isLt).params) heapLimit
    (envWords placement args) entry = some result
  halted : result.reason = .halted
  returned : LocalCompiler.Function.returnedValues (fieldCount (signatures[fn.val]'fn.isLt).result)
    result.state = valueWords finalPlacement value
  fits : ValueFits w value
  memory : ArenaRep finalPlacement cursor heapLimit heap (Source.State.ofRam result.state)
  agreement : Placement.Agrees initialHeap placement finalPlacement
  invocation : Source.FunctionMeasuredExec (programControl program) (lowerProgram program)
    heapLimit depth (lowerFunc program fn) (envWords placement args) bodySteps
    entry (valueWords finalPlacement value) sourceFinish
  observed : Source.State.Observes heapLimit 0 sourceFinish result.state
  steps_eq : result.steps =
    LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn) bodySteps + 1

namespace FunctionArenaExecution

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w depth heapLimit : Nat} {placement : Nat → Word w}
variable {args : Env (signatures[fn.val]'fn.isLt).params} {initialHeap : Heap}
variable {entry : Source.State w}

/-- Resume from the full actual data state, including the updated shared cursor. -/
def nextEntry
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry) :
    Source.State w := Source.State.ofRam outcome.result.state

/-- An independent source contract describes this actual result and final heap. -/
theorem post
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry)
    {pre : Env (signatures[fn.val]'fn.isLt).params → Heap → Prop}
    {post : Env (signatures[fn.val]'fn.isLt).params → Heap →
      Value (signatures[fn.val]'fn.isLt).result → Heap → Prop}
    (specification : FunctionTotal program fn pre post) (hpre : pre args initialHeap) :
    post args initialHeap outcome.value outcome.heap := by
  obtain ⟨finish, execution, sameHeap⟩ :=
    Complexity.Language.Program.eval_eq_ok_iff.mp outcome.source
  simpa only [sameHeap] using specification.postcondition hpre execution

/-- Expose the halted runner equation without unpacking the publication record. -/
theorem run_halted
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry) :
    LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
        (contextSize (signatures[fn.val]'fn.isLt).params) heapLimit
        (envWords placement args) entry =
      some ⟨outcome.result.state, outcome.result.steps, .halted⟩ := by
  have resultEq : outcome.result =
      ⟨outcome.result.state, outcome.result.steps, .halted⟩ := by rw [← outcome.halted]
  exact outcome.run.trans (congrArg some resultEq)

/-- The sufficient shared-heap and call-stack interval for this invocation.
This does not count reachable live objects, registers, code or I/O storage. -/
def workspaceWords
    (_outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry) :
    Nat := heapLimit + (depth + 1) * ABI.frameSize (programControl program)

/-- The actual finite set of memory addresses touched by the complete invocation,
not a sum of allocations or a set selected from the desired specification. -/
def heapAccesses
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry) :
    Finset (Word w) :=
  Ram.heapAccesses (lowerCode program fn) outcome.result.steps
    (LocalCompiler.Function.start (programControl program) heapLimit (envWords placement args) entry)

/-- Every actual access, including transient scratch and call-frame accesses,
lies inside the sufficient physical workspace interval. -/
theorem heapAccesses_below
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry)
    {address : Word w} (member : address ∈ outcome.heapAccesses) :
    address.toNat < outcome.workspaceWords := by
  unfold heapAccesses at member
  rw [outcome.steps_eq] at member
  exact LocalCompiler.Function.heapAccesses_below (compile_eq_some program fn)
    (lowerProgram_lookup program fn) outcome.capacity.codeCapacity outcome.capacity.stackCapacity
    outcome.invocation member

/-- Reusing scratch addresses does not accumulate distinct physical words.
The bound concerns all addresses touched, not peak reachable-live storage. -/
theorem heapAccesses_card_le
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry) :
    outcome.heapAccesses.card ≤ outcome.workspaceWords := by
  unfold heapAccesses
  rw [outcome.steps_eq]
  exact LocalCompiler.Function.heapAccesses_card_le (compile_eq_some program fn)
    (lowerProgram_lookup program fn) outcome.capacity.codeCapacity outcome.capacity.stackCapacity
    outcome.invocation

/-- Every execution prefix preserves environment memory outside the workspace;
temporary out-of-envelope writes cannot be hidden by restoring the final value. -/
theorem prefix_mem_above
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry)
    {k : Nat} {current : Ram.State w} (hk : k ≤ outcome.result.steps)
    (prefixRun : Ram.Exec (lowerCode program fn) k
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry) current)
    {address : Word w} (above : outcome.workspaceWords ≤ address.toNat) :
    current.mem address = entry.mem address := by
  rw [outcome.steps_eq] at hk
  exact LocalCompiler.Function.prefix_mem_above (compile_eq_some program fn)
    (lowerProgram_lookup program fn) outcome.capacity.codeCapacity outcome.capacity.stackCapacity
    outcome.invocation hk prefixRun above

end FunctionArenaExecution

namespace ArenaExecutionCost

/-- Publish the same counted allocating execution with its actual typed result,
complete machine memory and known call depth. The body count includes the two
existing function-initialization instructions. -/
theorem execute {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor finalCursor steps : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {finish : Complexity.Language.State (signatures[fn.val]'fn.isLt).params}
    {value : Value (signatures[fn.val]'fn.isLt).result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {ready : ArenaReady execution w heapLimit depth cursor finalCursor}
    {placement : Nat → Word w} {entry : Source.State w}
    (cost : ArenaExecutionCost ready steps)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      outcome.value = value ∧ outcome.heap = finish.heap ∧
        outcome.cursor = finalCursor ∧ outcome.bodySteps = steps + 2 := by
  obtain ⟨finalPlacement, sourceFinish, target, invocation, finalArena, agreement,
      run, returned, observed⟩ :=
    cost.runUntil launch.positive launch.arguments launch.rooted entry launch.arena
      launch.codeCapacity launch.stackCapacity
  refine ⟨{
    value := value
    heap := finish.heap
    finalPlacement := finalPlacement
    cursor := finalCursor
    result := ⟨target, LocalCompiler.Function.callSteps (programControl program)
      (lowerFunc program fn) (steps + 2) + 1, .halted⟩
    sourceFinish := sourceFinish
    bodySteps := steps + 2
    capacity := launch.toFunctionCapacity
    source := Complexity.Language.Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩
    run := run
    halted := rfl
    returned := returned
    fits := ready.outcome_fits
    memory := finalArena.of_observes observed
    agreement := agreement
    invocation := invocation
    observed := observed
    steps_eq := rfl }, rfl, rfl, rfl, rfl⟩

end ArenaExecutionCost

namespace ArenaReady

/-- Readiness publishes a complete typed invocation without a time-budget
premise. Its actual instruction count is obtained from that same execution. -/
theorem execute {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor finalCursor : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {finish : Complexity.Language.State (signatures[fn.val]'fn.isLt).params}
    {value : Value (signatures[fn.val]'fn.isLt).result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {placement : Nat → Word w} {entry : Source.State w}
    (ready : ArenaReady execution w heapLimit depth cursor finalCursor)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      outcome.value = value ∧ outcome.heap = finish.heap ∧ outcome.cursor = finalCursor := by
  obtain ⟨steps, cost⟩ := ready.exists_cost
  obtain ⟨outcome, returned, memory, cursorEq, _⟩ := cost.execute launch
  exact ⟨outcome, returned, memory, cursorEq⟩

end ArenaReady

namespace FunctionArenaRealizable

/-- Publish an allocating function's independent mathematical contract against
the same typed RAM result, retaining all actual final arena resources. -/
theorem execute {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor : Nat}
    {args : Env (signatures[fn.val]'fn.isLt).params} {heap : Heap}
    {placement : Nat → Word w} {entry : Source.State w}
    {feasible : Env (signatures[fn.val]'fn.isLt).params → Heap → Nat → Prop}
    {pre : Env (signatures[fn.val]'fn.isLt).params → Heap → Prop}
    {post : Env (signatures[fn.val]'fn.isLt).params → Heap →
      Value (signatures[fn.val]'fn.isLt).result → Heap → Prop}
    (realizable : FunctionArenaRealizable program w heapLimit depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (launch : FunctionArenaLaunch program fn depth heapLimit placement args heap cursor entry)
    (hfeasible : feasible args heap cursor) (hpre : pre args heap) :
    ∃ outcome : FunctionArenaExecution program fn depth heapLimit placement args heap entry,
      post args heap outcome.value outcome.heap := by
  obtain ⟨finish, value, finalCursor, execution, ready, property⟩ :=
    realizable.with_specification specification args heap cursor hfeasible hpre
  obtain ⟨outcome, returned, memory, _⟩ := ready.execute launch
  refine ⟨outcome, ?_⟩
  simpa only [returned, memory] using property

end FunctionArenaRealizable
end Ram.LanguageCompiler
