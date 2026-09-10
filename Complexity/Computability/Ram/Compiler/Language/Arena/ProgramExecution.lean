/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.MeasuredSimulation
import Complexity.Computability.Ram.Compiler.Language.Arena.Verification
import Complexity.Computability.Ram.Compiler.Language.Validity

/-!
# Running allocation-ready source functions

The generic counted simulation feeds the existing compiled function runner.
The returned fields, final source heap, extended placement and reserved cursor
belong to this same execution. Code and call-stack capacities remain explicit
backend premises; algorithm authors supply no register-level lowering proof.

The count includes the function's actual private-flag initialization, calls and
outer call-and-halt wrapper. Input preparation and the once-per-session arena
bootstrap are separate operations, not silently free source allocations.
Readiness alone also supplies a terminating invocation without a proposed time
bound; its instruction count is an observation of that invocation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaExecutionCost

/-- The same allocation-ready execution determines the actual halted compiled
invocation and its exact instruction count, with its final arena retained. -/
theorem runUntil {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor finalCursor steps : Nat} {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {ready : ArenaReady execution w heapLimit depth cursor finalCursor}
    (cost : ArenaExecutionCost ready steps)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ finalPlacement finishTarget target,
      Source.FunctionMeasuredExec (programControl program) (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) (steps + 2) entry
        (valueWords finalPlacement value) finishTarget ∧
      ArenaRep finalPlacement finalCursor heapLimit finish.heap finishTarget ∧
      Placement.Agrees heap placement finalPlacement ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
        some ⟨target, LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program fn) (steps + 2) + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords finalPlacement value ∧
      Source.State.Observes heapLimit 0 finishTarget target := by
  obtain ⟨finalPlacement, finishTarget, invocation, finalArena, agreed⟩ :=
    cost.lowerCoreMeasured.functionMeasuredExec (programControl program)
      hw arguments rooted entry arena
  obtain ⟨target, returned, fields, observed⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured (compile_eq_some program fn)
      (lowerProgram_lookup program fn) codeCapacity stackCapacity invocation
  exact ⟨finalPlacement, finishTarget, target, invocation, finalArena, agreed, returned,
    by simpa only [lowerFunc_results_length] using fields, observed⟩

end ArenaExecutionCost

namespace ArenaReady

/-- Readiness yields an actual terminated invocation without assuming a time
budget. The existential count is derived from the same finite source execution. -/
theorem runUntil {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor finalCursor : Nat} {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    (ready : ArenaReady execution w heapLimit depth cursor finalCursor)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ steps finalPlacement finishTarget target,
      ArenaExecutionCost ready steps ∧
      Source.FunctionMeasuredExec (programControl program) (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) (steps + 2) entry
        (valueWords finalPlacement value) finishTarget ∧
      ArenaRep finalPlacement finalCursor heapLimit finish.heap finishTarget ∧
      Placement.Agrees heap placement finalPlacement ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
        some ⟨target, LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program fn) (steps + 2) + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords finalPlacement value ∧
      Source.State.Observes heapLimit 0 finishTarget target := by
  obtain ⟨steps, cost⟩ := ready.exists_cost
  obtain ⟨finalPlacement, finishTarget, target, invocation, finalArena, agreed,
    returned, fields, observed⟩ :=
    cost.runUntil hw arguments rooted entry arena codeCapacity stackCapacity
  exact ⟨steps, finalPlacement, finishTarget, target, cost, invocation, finalArena,
    agreed, returned, fields, observed⟩

end ArenaReady

namespace FunctionArenaRealizable

/-- An independent mathematical contract holds for the actual allocating
compiled invocation. Neither the source proof nor this interface needs a
proposed instruction budget or program-specific register invariant. -/
theorem runUntil {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {fn : Fin signatures.length}
    {feasible : Env signatures[fn].params → Heap → Nat → Prop}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionArenaRealizable program w heapLimit depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (heap : Heap) (cursor : Nat)
    (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (hfeasible : feasible args heap cursor) (hpre : pre args heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ value finalHeap finalCursor steps finalPlacement finishTarget target,
      program.eval fn args heap = Part.some (.ok value, finalHeap) ∧
      post args heap value finalHeap ∧
      Source.FunctionMeasuredExec (programControl program) (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) (steps + 2) entry
        (valueWords finalPlacement value) finishTarget ∧
      ArenaRep finalPlacement finalCursor heapLimit finalHeap finishTarget ∧
      Placement.Agrees heap placement finalPlacement ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
        some ⟨target, LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program fn) (steps + 2) + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords finalPlacement value ∧
      Source.State.Observes heapLimit 0 finishTarget target := by
  obtain ⟨finish, value, finalCursor, execution, ready, property⟩ :=
    realizable.with_specification specification args heap cursor hfeasible hpre
  obtain ⟨steps, finalPlacement, finishTarget, target, _, invocation, finalArena,
    agreed, returned, fields, observed⟩ :=
    ready.runUntil hw arguments rooted entry arena codeCapacity stackCapacity
  exact ⟨value, finish.heap, finalCursor, steps, finalPlacement, finishTarget, target,
    Complexity.Language.Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩,
    property, invocation, finalArena, agreed, returned, fields, observed⟩

end FunctionArenaRealizable
end Ram.LanguageCompiler
