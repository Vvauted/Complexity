/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Simulation
import Complexity.Computability.Ram.Verification.Function

/-!
# Reusing RAM source contracts at the high-level interface

A contract for the actual lowered function can supply its mathematical result
property without another proof of the high-level algorithm. The shared forward
simulation produces that function's real invocation; `FunctionContract.post`
transports the existing contract to its returned fields and shared final state.

Source realizability still supplies a genuine finite source execution, its word
ranges and sufficient call nesting. These rules do not infer source termination
from target termination alone. The contract must concern the same `lowerProgram`
and `lowerFunc`, not an unrelated implementation with a similar specification.

The result bridge uses ordinary source values and retains the actual target
post-state. A word-range premise permits exact mathematical decoding, rather
than silently identifying modular arithmetic with unbounded natural arithmetic.
There is no instruction budget, new source syntax or new execution relation.

Input and output heaps are related to their actual RAM states under a fixed
placement. Source heap identity is not inferred from returned descriptors, which
need not encode handles injectively. The source postcondition concerns the actual
updated heap; caller-local restoration does not undo shared writes.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A contract for the actual lowered function applies to the invocation obtained
from source realization. Both its returned fields and shared final state belong
to that same invocation. -/
theorem RealizedExec.post_of_contract {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {args : Env signatures[fn].params} {initialHeap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {lowPre : List (Word w) → Source.State w → Prop}
    {lowPost : List (Word w) → Source.State w → List (Word w) → Source.State w → Prop}
    (execution : RealizedExec program w depth (program.body fn)
      ⟨args, initialHeap⟩ finish (.returned value))
    (contract : Source.FunctionContract (lowerProgram program) heapLimit depth
      (lowerFunc program fn) lowPre lowPost)
    (hw : 0 < w) (arguments : EnvFits w args) (entry : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap entry)
    (input : lowPre (envWords placement args) entry) :
    ∃ targetFinish,
      Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
        (envWords placement args) entry (valueWords placement value) targetFinish ∧
      lowPost (envWords placement args) entry (valueWords placement value) targetFinish ∧
      HeapRep placement heapLimit finish.heap targetFinish := by
  obtain ⟨targetFinish, invocation, representedFinal⟩ :=
    execution.functionExec hw arguments entry represented
  exact ⟨targetFinish, invocation, contract.post input invocation, representedFinal⟩

/-- Reuse a lowered function's existing mathematical contract to establish the
high-level source contract. Realization provides source termination and ranges;
the supplied result implication decodes the actual returned value. Its input
conditions are explicit and do not change the source precondition. -/
theorem FunctionRealizable.functionTotal_of_contract {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {lowPre : List (Word w) → Source.State w → Prop}
    {lowPost : List (Word w) → Source.State w → List (Word w) → Source.State w → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (contract : Source.FunctionContract (lowerProgram program) heapLimit depth
      (lowerFunc program fn) lowPre lowPost)
    (hw : 0 < w) (entry : Env signatures[fn].params → Heap → Source.State w)
    (input : ∀ args heap, pre args heap →
      feasible args heap ∧ EnvFits w args ∧
      HeapRep placement heapLimit heap (entry args heap) ∧
      lowPre (envWords placement args) (entry args heap))
    (output : ∀ (args : Env signatures[fn].params) (heap : Heap)
      (value : Value signatures[fn].result) (finalHeap : Heap) (targetFinish : Source.State w),
      pre args heap → ValueFits w value →
      HeapRep placement heapLimit finalHeap targetFinish →
      lowPost (envWords placement args) (entry args heap) (valueWords placement value) targetFinish →
      post args heap value finalHeap) :
    FunctionTotal program fn pre post := by
  intro args heap hpre
  obtain ⟨feasibleArgs, arguments, represented, lowInput⟩ := input args heap hpre
  obtain ⟨finish, value, execution⟩ := realizable args heap feasibleArgs
  obtain ⟨targetFinish, _, property, representedFinal⟩ :=
    execution.post_of_contract contract hw arguments (entry args heap) represented lowInput
  exact ⟨finish, value, execution.erase,
    output args heap value finish.heap targetFinish hpre execution.returned_fits
      representedFinal property⟩

end Ram.LanguageCompiler
