/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Simulation
import Complexity.Computability.Ram.Compiler.Language.Effects
import Complexity.Computability.Ram.Compiler.Language.Validity

/-!
# Executing realized source programs

Independent source correctness and realization supply the actual returned value
of the generated function. The existing checked compiler and unbounded function
runner then provide a halted execution, its returned fields and its measured
instruction count. No register proof, lookup certificate, operational budget or
new runtime is supplied by the algorithm author.

The source result retains the actual final heap, represented by the same fixed
placement as the input. The runner observes the actual shared post-state below
its heap boundary, not an assumed copy of the entry state. Private call-stack
cells are not identified with source objects. Code size and stack capacity
remain explicit backend conditions.

The existential body count belongs to this same execution and includes its
internal calls. The existing outer call-and-halt count accounts for the entry
wrapper. This theorem does not assert a source-level cost bound.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace FunctionRealizable

/-- Run a realized source function through the existing compiled runner. Its
actual value satisfies the independent source contract, and its body observation
identifies the count of this same halted invocation. -/
theorem runUntil {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (initialHeap : Heap)
    (arguments : EnvFits w args)
    (hfeasible : feasible args initialHeap) (hpre : pre args initialHeap) (entry : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap entry)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (value : Value signatures[fn].result) (finalHeap : Heap)
        (targetFinish : Source.State w) (bodySteps : Nat) (target : Ram.State w),
      program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      post args initialHeap value finalHeap ∧
      Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
        (envWords placement args) entry (valueWords placement value) targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
        some ⟨target,
          LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
            bodySteps + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords placement value ∧
      Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit
        (envWords placement args) entry =
        Part.some bodySteps := by
  obtain ⟨value, finalHeap, finish, sourceEval, execution, property, representedFinal⟩ :=
    realizable.functionExec (heapLimit := heapLimit) specification hw args initialHeap arguments
      hfeasible hpre entry represented
  obtain ⟨bodySteps, target, returned, values, observed, time⟩ :=
    LocalCompiler.Function.runUntil_of_execution (compile_eq_some program fn)
      (lowerProgram_lookup program fn) codeCapacity stackCapacity execution
  refine ⟨value, finalHeap, finish, bodySteps, target, sourceEval, property, execution,
    representedFinal, returned, ?_, observed, time⟩
  simpa only [lowerFunc_results_length] using values

end FunctionRealizable

end Ram.LanguageCompiler
