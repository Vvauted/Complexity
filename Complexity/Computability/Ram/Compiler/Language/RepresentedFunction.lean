/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.RepresentedFunction
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution

/-!
# Mathematical representations of the same typed RAM result

These rules apply represented source contracts to an existing `FunctionExecution`
or `FunctionArenaExecution`. Their mathematical output observes the actual source
value and final heap already connected to that halted RAM invocation. No new run,
input loader, specification-based decoder or container freeze is introduced.

The existing execution records retain their independent instruction counts and
machine conditions. The rules below assert no time bound: resource proofs still
use the same program and the existing cost and publication interfaces.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u v

variable {α : Type u} {β : α → Type v} {signatures : List Signature}
variable {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
variable {representation : FunctionRepresentation α β signatures[fn]}
variable {pre : α → Prop} {post : (x : α) → β x → Prop}
variable {w heapLimit : Nat} {placement : Nat → Word w}
variable {args : Env signatures[fn].params} {initialHeap : Heap} {entry : Source.State w}

/-- Publish a high-level represented postcondition for this same halted invocation.
Input existence, source termination and machine admissibility are not inferred
from the representation relation. -/
theorem FunctionExecution.represented
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    (specification : RepresentedFunction.Total program fn representation pre post)
    {x : α} (valid : pre x) (represented : representation.input.Rel x args initialHeap) :
    ∃ output, representation.post x args initialHeap outcome.value outcome.heap output ∧
      post x output :=
  outcome.post (specification x valid) represented

/-- Apply a proved ordinary-function correspondence to the actual returned value
and final heap, without executing that ordinary function as a RAM primitive. -/
theorem FunctionExecution.refines
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    {function : (x : α) → β x}
    (refinement : RepresentedFunction.Refines program fn representation pre function)
    {x : α} (valid : pre x) (represented : representation.input.Rel x args initialHeap) :
    representation.post x args initialHeap outcome.value outcome.heap (function x) :=
  outcome.post (refinement x valid) represented

/-- The allocation-aware execution exposes the same mathematical postcondition.
Its final placement and cursor remain those already recorded by the actual run. -/
theorem FunctionArenaExecution.represented {depth : Nat}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry)
    (specification : RepresentedFunction.Total program fn representation pre post)
    {x : α} (valid : pre x) (represented : representation.input.Rel x args initialHeap) :
    ∃ output, representation.post x args initialHeap outcome.value outcome.heap output ∧
      post x output :=
  outcome.post (specification x valid) represented

/-- Allocation does not change the implementation identity of an independently
proved mathematical correspondence or turn a borrowed result into a frozen one. -/
theorem FunctionArenaExecution.refines {depth : Nat}
    (outcome : FunctionArenaExecution program fn depth heapLimit placement args initialHeap entry)
    {function : (x : α) → β x}
    (refinement : RepresentedFunction.Refines program fn representation pre function)
    {x : α} (valid : pre x) (represented : representation.input.Rel x args initialHeap) :
    representation.post x args initialHeap outcome.value outcome.heap (function x) :=
  outcome.post (refinement x valid) represented

end Ram.LanguageCompiler
