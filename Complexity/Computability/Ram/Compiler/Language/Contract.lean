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
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A contract for the actual lowered function applies to the invocation obtained
from source realization. Both its returned fields and shared final state belong
to that same invocation. -/
theorem RealizedExec.post_of_contract {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {fn : Fin signatures.length} {args finish : Env signatures[fn].params}
    {value : Value signatures[fn].result}
    {lowPre : List (Word w) → Source.State w → Prop}
    {lowPost : List (Word w) → Source.State w → List (Word w) → Source.State w → Prop}
    (execution : RealizedExec program w depth (program.body fn) args finish (.returned value))
    (contract : Source.FunctionContract (lowerProgram program) heapLimit depth
      (lowerFunc program fn) lowPre lowPost)
    (hw : 0 < w) (arguments : EnvFits w args) (entry : Source.State w)
    (input : lowPre (envWords w args) entry) :
    ∃ targetFinish,
      Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
        (envWords w args) entry (valueWords w value) targetFinish ∧
      lowPost (envWords w args) entry (valueWords w value) targetFinish := by
  obtain ⟨targetFinish, invocation⟩ := execution.functionExec hw arguments entry
    (heapLimit := heapLimit)
  exact ⟨targetFinish, invocation, contract.post input invocation⟩

/-- Reuse a lowered function's existing mathematical contract to establish the
high-level source contract. Realization provides source termination and ranges;
the supplied result implication decodes the actual returned value. Its input
conditions are explicit and do not change the source precondition. -/
theorem FunctionRealizable.functionTotal_of_contract {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop}
    {lowPre : List (Word w) → Source.State w → Prop}
    {lowPost : List (Word w) → Source.State w → List (Word w) → Source.State w → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (contract : Source.FunctionContract (lowerProgram program) heapLimit depth
      (lowerFunc program fn) lowPre lowPost)
    (hw : 0 < w) (entry : Env signatures[fn].params → Source.State w)
    (input : ∀ args, pre args →
      feasible args ∧ EnvFits w args ∧ lowPre (envWords w args) (entry args))
    (output : ∀ (args : Env signatures[fn].params) (value : Value signatures[fn].result)
      (targetFinish : Source.State w), pre args → valueToNat value < 2 ^ w →
      lowPost (envWords w args) (entry args) (valueWords w value) targetFinish → post args value) :
    FunctionTotal program fn pre post := by
  intro args hpre
  obtain ⟨feasibleArgs, arguments, lowInput⟩ := input args hpre
  obtain ⟨finish, value, execution⟩ := realizable args feasibleArgs
  obtain ⟨targetFinish, _, property⟩ :=
    execution.post_of_contract contract hw arguments (entry args) lowInput
  exact ⟨finish, value, execution.erase,
    output args value targetFinish hpre execution.returned_fits property⟩

end Ram.LanguageCompiler
