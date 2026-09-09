/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Simulation
import Complexity.Computability.Ram.Compiler.Language.Effects
import Complexity.Computability.Ram.Compiler.Language.Validity

/-!
# Executing realized scalar source programs

Independent source correctness and realization supply the actual returned value
of the generated function. The existing checked compiler and unbounded function
runner then provide a halted execution, its returned fields and its measured
instruction count. No register proof, lookup certificate, operational budget or
new runtime is supplied by the algorithm author.

The source result retains the actual final heap. The current scalar lowering
preserves the RAM shared entry state, observed only below its heap boundary;
its private call-stack cells are not identified with the source heap. This
does not assert a source-heap representation. Code size and stack capacity
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
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (initialHeap : Heap)
    (arguments : EnvFits w args)
    (hfeasible : feasible args initialHeap) (hpre : pre args initialHeap) (entry : Source.State w)
    (codeCapacity : (lowerCode program fn).length < 2 ^ w)
    (stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (value : Value signatures[fn].result) (finalHeap : Heap)
        (bodySteps : Nat) (target : Ram.State w),
      program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      post args initialHeap value finalHeap ∧
      LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
          (contextSize signatures[fn].params) heapLimit (envWords w args) entry =
        some ⟨target,
          LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
            bodySteps + 1, .halted⟩ ∧
      LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result) target =
        valueWords w value ∧
      Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit (envWords w args) entry =
        Part.some bodySteps := by
  obtain ⟨value, finalHeap, finish, sourceEval, execution, property⟩ :=
    realizable.functionExec (heapLimit := heapLimit) specification hw args initialHeap arguments
      hfeasible hpre entry
  have unchanged : finish = entry := execution.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites program) (lowerBody_noSharedWrites program fn)
  subst finish
  obtain ⟨bodySteps, target, returned, values, observed, time⟩ :=
    LocalCompiler.Function.runUntil_of_execution (compile_eq_some program fn)
      (lowerProgram_lookup program fn) codeCapacity stackCapacity execution
  refine ⟨value, finalHeap, bodySteps, target, sourceEval, property, returned, ?_, observed, time⟩
  simpa only [lowerFunc_results_length] using values

end FunctionRealizable

end Ram.LanguageCompiler
