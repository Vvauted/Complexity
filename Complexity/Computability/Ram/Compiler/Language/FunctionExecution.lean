/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.Heap.Observation

/-!
# Typed results of compiled source invocations

`FunctionCapacity` collects code/stack capacity independently of the current
arguments and heap. `FunctionLaunch` adds the existing argument ranges and
represented memory of a preloaded invocation. They are backend conditions,
separate from its mathematical precondition and time bound.

`FunctionExecution` retains a source value, its final heap and the existing
runner's actual state and instruction count. Its proofs connect that same
result to source evaluation and to represented memory on the full actual RAM
data projection. It introduces neither another interpreter nor a decoder that
selects a mathematical result from its specification.

`FunctionRealizable.execute` and `FunctionRealizable.execute_le` package the
existing execution theorems. Mathematical postconditions and time bounds remain
independent of the result record. The next invocation can use `nextEntry` without
resetting private memory or rolling back any shared effects.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Code and stack capacity reusable across different arguments and shared heaps. -/
structure FunctionCapacity {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (w depth heapLimit : Nat) : Prop where
  positive : 0 < w
  codeCapacity : (lowerCode program fn).length < 2 ^ w
  stackCapacity : heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w

/-- Capacity for more nested calls also accommodates a smaller nesting allowance. -/
theorem FunctionCapacity.mono_depth {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w depth depth' heapLimit : Nat}
    (capacity : FunctionCapacity program fn w depth heapLimit) (bound : depth' ≤ depth) :
    FunctionCapacity program fn w depth' heapLimit := by
  refine ⟨capacity.positive, capacity.codeCapacity, ?_⟩
  exact lt_of_le_of_lt
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right bound 1)) heapLimit)
    capacity.stackCapacity

/-- The existing backend conditions for one preloaded compiled invocation.
Input loading and host scheduling are outside this invocation boundary. -/
structure FunctionLaunch {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {w : Nat} (depth heapLimit : Nat) (placement : Nat → Word w)
    (args : Env (signatures[fn.val]'fn.isLt).params)
    (initialHeap : Heap) (entry : Source.State w) : Prop where
  toFunctionCapacity : FunctionCapacity program fn w depth heapLimit
  arguments : EnvFits (Γ := (signatures[fn.val]'fn.isLt).params) w args
  memory : HeapRep placement heapLimit initialHeap entry

namespace FunctionLaunch

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w depth heapLimit : Nat} {placement : Nat → Word w}
variable {args : Env signatures[fn].params} {initialHeap : Heap} {entry : Source.State w}

/-- A launch retains its capacity's positive word width. -/
theorem positive (launch : FunctionLaunch program fn depth heapLimit placement args initialHeap entry) :
    0 < w := launch.toFunctionCapacity.positive

/-- A launch retains its capacity's code bound. -/
theorem codeCapacity
    (launch : FunctionLaunch program fn depth heapLimit placement args initialHeap entry) :
    (lowerCode program fn).length < 2 ^ w := launch.toFunctionCapacity.codeCapacity

/-- A launch retains its capacity's stack bound. -/
theorem stackCapacity
    (launch : FunctionLaunch program fn depth heapLimit placement args initialHeap entry) :
    heapLimit + (depth + 1) * ABI.frameSize (programControl program) < 2 ^ w :=
  launch.toFunctionCapacity.stackCapacity

end FunctionLaunch

/-- The mathematical value and heap of the same actual halted RAM invocation.
All physical memory in `result.state`, including private stack words, is kept. -/
structure FunctionExecution {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {w : Nat} (heapLimit : Nat) (placement : Nat → Word w)
    (args : Env signatures[fn].params) (initialHeap : Heap) (entry : Source.State w) where
  value : Value signatures[fn].result
  heap : Heap
  result : RunResult (Ram.State w)
  sourceFinish : Source.State w
  bodySteps : Nat
  source : program.eval fn args initialHeap = Part.some (.ok value, heap)
  run : LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
      (contextSize signatures[fn].params) heapLimit (envWords placement args) entry = some result
  halted : result.reason = .halted
  returned : LocalCompiler.Function.returnedValues (fieldCount signatures[fn].result)
    result.state = valueWords placement value
  fits : ValueFits w value
  memory : HeapRep placement heapLimit heap (Source.State.ofRam result.state)
  invocation : ∃ depth, Source.FunctionExec (lowerProgram program) heapLimit depth
    (lowerFunc program fn) (envWords placement args) entry (valueWords placement value) sourceFinish
  observed : Source.State.Observes heapLimit 0 sourceFinish result.state
  bodyTime : (lowerFunc program fn).bodyTime (lowerProgram program) heapLimit
    (envWords placement args) entry = Part.some bodySteps
  steps_eq : result.steps =
    LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn) bodySteps + 1

namespace FunctionExecution

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w heapLimit : Nat} {placement : Nat → Word w}
variable {args : Env signatures[fn].params} {initialHeap : Heap} {entry : Source.State w}

/-- Reuse the entire actual data state at the next preloaded call boundary. -/
def nextEntry (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry) :
    Source.State w :=
  Source.State.ofRam outcome.result.state

/-- Any independently proved source contract describes this actual result. -/
theorem post (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (specification : FunctionTotal program fn pre post) (hpre : pre args initialHeap) :
    post args initialHeap outcome.value outcome.heap := by
  obtain ⟨finish, execution, sameHeap⟩ :=
    Complexity.Language.Program.eval_eq_ok_iff.mp outcome.source
  simpa only [sameHeap] using specification.postcondition hpre execution

/-- Expose the usual halted runner equation without unpacking the result record. -/
theorem run_halted
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry) :
    LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) fn.val
        (contextSize signatures[fn].params) heapLimit (envWords placement args) entry =
      some ⟨outcome.result.state, outcome.result.steps, .halted⟩ := by
  have resultEq : outcome.result =
      ⟨outcome.result.state, outcome.result.steps, .halted⟩ := by
    rw [← outcome.halted]
  exact outcome.run.trans (congrArg some resultEq)

/-- Remove the fixed outer-call overhead from an actual invocation bound. -/
theorem bodySteps_le
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    {bound : Nat}
    (bounded : outcome.result.steps ≤ LocalCompiler.Function.callSteps (programControl program)
      (lowerFunc program fn) bound + 1) : outcome.bodySteps ≤ bound := by
  rw [outcome.steps_eq] at bounded
  simp only [LocalCompiler.Function.callSteps_eq] at bounded
  omega

/-- A lowered invocation with no shared writes observes the entire entry data
below the heap boundary, even when its represented source heap is empty. -/
theorem observes_of_noSharedWrites
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    (programCondition : ∀ function ∈ lowerProgram program, function.body.NoSharedWrites)
    (bodyCondition : (lowerFunc program fn).body.NoSharedWrites) :
    Source.State.Observes heapLimit 0 entry outcome.result.state := by
  obtain ⟨depth, invocation⟩ := outcome.invocation
  have unchanged := invocation.finish_eq_of_noSharedWrites programCondition bodyCondition
  simpa only [unchanged] using outcome.observed

/-- Source-level absence of heap writes supplies the existing lowered frame
conditions, including all recursive callees. -/
theorem observes_of_noHeapWrites
    (outcome : FunctionExecution program fn heapLimit placement args initialHeap entry)
    (condition : ∀ fn, NoHeapWrites (program.body fn)) :
    Source.State.Observes heapLimit 0 entry outcome.result.state :=
  outcome.observes_of_noSharedWrites (lowerProgram_noSharedWrites program condition)
    (lowerBody_noSharedWrites program fn (condition fn))

end FunctionExecution

namespace FunctionRealizable

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {w depth heapLimit : Nat} {placement : Nat → Word w}
variable {args : Env signatures[fn].params} {initialHeap : Heap} {entry : Source.State w}
variable {feasible pre costPre : Env signatures[fn].params → Heap → Prop}
variable {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
variable {bound : Env signatures[fn].params → Heap → Nat}

private theorem fits_of_eval (realizable : FunctionRealizable program w depth fn feasible)
    (hfeasible : feasible args initialHeap)
    {value : Value signatures[fn].result} {finalHeap : Heap}
    (source : program.eval fn args initialHeap = Part.some (.ok value, finalHeap)) :
    ValueFits w value := by
  obtain ⟨finish, execution, _⟩ := Complexity.Language.Program.eval_eq_ok_iff.mp source
  obtain ⟨realizedFinish, realizedValue, realized⟩ := realizable args initialHeap hfeasible
  have sameValue : realizedValue = value :=
    Control.returned.inj (realized.erase.deterministic execution).2
  exact sameValue ▸ realized.returned_fits

/-- Publish a typed result of the existing unbounded runner from independent
source correctness and backend admissibility. No time bound is required. -/
theorem execute (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (launch : FunctionLaunch program fn depth heapLimit placement args initialHeap entry)
    (hfeasible : feasible args initialHeap) (hpre : pre args initialHeap) :
    ∃ outcome : FunctionExecution program fn heapLimit placement args initialHeap entry,
      post args initialHeap outcome.value outcome.heap := by
  obtain ⟨value, finalHeap, targetFinish, bodySteps, target, source, property,
      invocation, represented, run, returned, observed, time⟩ :=
    realizable.runUntil specification launch.positive args initialHeap launch.arguments
      hfeasible hpre entry launch.memory launch.codeCapacity launch.stackCapacity
  exact ⟨{
    value := value
    heap := finalHeap
    result := ⟨target,
      LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
        bodySteps + 1, .halted⟩
    sourceFinish := targetFinish
    bodySteps := bodySteps
    source := source
    run := run
    halted := rfl
    returned := returned
    fits := fits_of_eval realizable hfeasible source
    memory := represented.of_observes observed
    invocation := ⟨depth, invocation⟩
    observed := observed
    bodyTime := time
    steps_eq := rfl }, property⟩

/-- Add a separately proved instruction bound to that same typed result.
The bound includes the actual outer call, return and final halt once. -/
theorem execute_le (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (timeBound : FunctionCostBound program fn costPre bound)
    (launch : FunctionLaunch program fn depth heapLimit placement args initialHeap entry)
    (hfeasible : feasible args initialHeap) (hpre : pre args initialHeap)
    (hcost : costPre args initialHeap) :
    ∃ outcome : FunctionExecution program fn heapLimit placement args initialHeap entry,
      post args initialHeap outcome.value outcome.heap ∧
      outcome.result.steps ≤ LocalCompiler.Function.callSteps (programControl program)
        (lowerFunc program fn) (bound args initialHeap) + 1 := by
  obtain ⟨value, finalHeap, targetFinish, bodySteps, target, source, property,
      invocation, represented, run, returned, observed, time, _, bounded⟩ :=
    realizable.runUntil_le specification timeBound launch.positive args initialHeap launch.arguments
      hfeasible hpre hcost entry launch.memory launch.codeCapacity launch.stackCapacity
  exact ⟨{
    value := value
    heap := finalHeap
    result := ⟨target,
      LocalCompiler.Function.callSteps (programControl program) (lowerFunc program fn)
        bodySteps + 1, .halted⟩
    sourceFinish := targetFinish
    bodySteps := bodySteps
    source := source
    run := run
    halted := rfl
    returned := returned
    fits := fits_of_eval realizable hfeasible source
    memory := represented.of_observes observed
    invocation := ⟨depth, invocation⟩
    observed := observed
    bodyTime := time
    steps_eq := rfl }, property, bounded⟩

end FunctionRealizable

end Ram.LanguageCompiler
