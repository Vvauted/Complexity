/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution
import Complexity.Computability.Ram.Compiler.Local.Function.Memory

/-!
# Physical memory bounds for allocation-ready source functions

Allocation readiness and the existing measured compiler simulation imply an
address envelope for the actual call-and-halt invocation, including every
intermediate read and write. This remains valid when a scope restores its
cursor: a final cursor is not substituted for the trace's workspace bound.

The interval below `heapLimit` includes represented inputs, retained outputs,
temporary storage and the allocator metadata word at address zero. The stack
allowance includes the outer call and all declared nested calls. This is a
sufficient physical workspace bound, not a tight live-space characterization.
Registers, code and I/O streams are separate resources. Host-side input loading
and output conversion remain outside the preloaded invocation boundary.
-/

namespace Ram.LanguageCompiler.ArenaExecutionCost

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth cursor finalCursor steps : Nat} {fn : Fin signatures.length}
variable {args : Env signatures[fn].params} {heap : Heap}
variable {finish : Complexity.Language.State signatures[fn].params}
variable {value : Value signatures[fn].result}
variable {execution : Complexity.Language.Exec program (program.body fn)
  ⟨args, heap⟩ finish (.returned value)}
variable {ready : ArenaReady execution w heapLimit depth cursor finalCursor}

/-- The source execution's existing cost certificate bounds every actual
memory address of the full compiled invocation, including transient accesses. -/
theorem heapAccesses_below (cost : ArenaExecutionCost ready steps)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w)
    {address : Word w}
    (member : address ∈ heapAccesses (lowerCode program fn)
      (LocalCompiler.Function.callSteps (programControl program)
        (lowerFunc program fn) (steps + 2) + 1)
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry)) :
    address.toNat < heapLimit + (depth + 1) * ABI.frameSize (programControl program) := by
  obtain ⟨finalPlacement, finishTarget, invocation, _, _⟩ :=
    cost.lowerCoreMeasured.functionMeasuredExec (programControl program)
      hw arguments rooted entry arena
  exact LocalCompiler.Function.heapAccesses_below (compile_eq_some program fn)
    (lowerProgram_lookup program fn) codeCapacity stackCapacity invocation member

/-- The same envelope includes initialization, cursor updates, frame stores
and every other actual write, even when later execution restores its value. -/
theorem heapWrites_below (cost : ArenaExecutionCost ready steps)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w)
    {address : Word w}
    (member : address ∈ heapWrites (lowerCode program fn)
      (LocalCompiler.Function.callSteps (programControl program)
        (lowerFunc program fn) (steps + 2) + 1)
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry)) :
    address.toNat < heapLimit + (depth + 1) * ABI.frameSize (programControl program) :=
  cost.heapAccesses_below hw arguments rooted entry arena codeCapacity stackCapacity
    (heapWrites_subset_accesses _ _ _ member)

/-- Repeated use of one scratch interval does not increase the number of
physical words touched. The count comes from the actual whole execution's
access set, not a sum of source allocation lengths. -/
theorem heapAccesses_card_le (cost : ArenaExecutionCost ready steps)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    (heapAccesses (lowerCode program fn)
      (LocalCompiler.Function.callSteps (programControl program)
        (lowerFunc program fn) (steps + 2) + 1)
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry)).card ≤
      heapLimit + (depth + 1) * ABI.frameSize (programControl program) := by
  obtain ⟨finalPlacement, finishTarget, invocation, _, _⟩ :=
    cost.lowerCoreMeasured.functionMeasuredExec (programControl program)
      hw arguments rooted entry arena
  exact LocalCompiler.Function.heapAccesses_card_le (compile_eq_some program fn)
    (lowerProgram_lookup program fn) codeCapacity stackCapacity invocation

/-- Every actual prefix preserves memory outside the sufficient workspace
interval. This rules out temporary out-of-envelope writes, not just a changed
final state; the untouched preloaded environment is not charged as workspace. -/
theorem prefix_mem_above (cost : ArenaExecutionCost ready steps)
    (hw : 0 < w) (arguments : EnvFits w args) (rooted : args.Rooted heap)
    (entry : Source.State w) {placement : Nat → Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w)
    {k : Nat} {current : Ram.State w}
    (hk : k ≤ LocalCompiler.Function.callSteps (programControl program)
      (lowerFunc program fn) (steps + 2) + 1)
    (prefixRun : Ram.Exec (lowerCode program fn) k
      (LocalCompiler.Function.start (programControl program) heapLimit
        (envWords placement args) entry) current)
    {address : Word w}
    (above : heapLimit + (depth + 1) * ABI.frameSize (programControl program) ≤ address.toNat) :
    current.mem address = entry.mem address := by
  apply prefixRun.prefix_mem_eq_of_not_written hk
  intro member
  exact Nat.not_lt_of_ge above
    (cost.heapWrites_below hw arguments rooted entry arena codeCapacity stackCapacity member)

end Ram.LanguageCompiler.ArenaExecutionCost
