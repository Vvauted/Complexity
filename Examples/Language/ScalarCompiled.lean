/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Scalar
import Complexity.Computability.Ram.Compiler.Language.Execution
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.CostBound.Range
import Complexity.Computability.Ram.Compiler.Language.Realization.Range
import Complexity.Computability.Ram.Compiler.Language.Tactic
import Complexity.Computability.Ram.Compiler.Language.Linking.Tactic
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.RepresentedFunction
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Execution
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Scalar
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Asymptotics

/-!
# Transferring the scalar source proof through generic lowering

The independent source program and its mathematical proofs are imported
unchanged. The additional proofs here concern the actual intermediate natural
values and sufficient call nesting. The helper's existing source contract
identifies its actual returned value; its mathematical behavior is not reproved.

The shared lowering theorems produce both callable IR execution and a halted RAM
runner with the same mathematical minimum. No register layout, receiver update
or algorithm-specific source-to-IR adapter appears in this proof. Separate
source-execution cost bounds apply to that same invocation, including its
internal helper call, outer calling convention and final halt.

The source contracts preserve every initial heap. These pure backend consumers
instantiate the shared heap relation with no source objects, so arbitrary RAM
entry memory is admitted. Their read-only source bodies separately establish
that the actual target invocation preserves this entry state.
-/

namespace Complexity.Language.Examples.Scalar

open Ram.LanguageCompiler

private theorem program_noHeapWrites : ∀ fn, NoHeapWrites (program.body fn) := by
  intro fn
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) fn
  · change NoHeapWrites Implementation.incrementBody
    simp [Implementation.incrementBody, NoHeapWrites]
  · change NoHeapWrites Implementation.boundedIncrementBody
    simp [Implementation.boundedIncrementBody, NoHeapWrites]

/-- The helper needs no nested call and its actual sum must fit the word width. -/
theorem increment_realizable {w : Nat} :
    FunctionRealizable program w 0 (0 : Fin 2)
      (fun args _ => Env.head args + 1 < 2 ^ w) := by
  ram_source_realize (n)
  all_goals omega

/-- One call level suffices. The intermediate increment, not merely the final
minimum, and the compared limit must both be representable. -/
theorem boundedIncrement_realizable {w : Nat} :
    FunctionRealizable program w 1 (1 : Fin 2)
      (fun args _ => Env.head args + 1 < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  ram_source_realize (n limit) using increment_realizable, increment_total
  all_goals omega

/-- The automatically lowered helper returns the same mathematical increment.
The entry state and heap boundary are arbitrary; no manual register proof is needed. -/
theorem increment_functionExec {w heapLimit : Nat} (hw : 0 < w) (n : Nat) (_sourceHeap : Heap)
    (fits : n + 1 < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 0
      (lowerFunc program (0 : Fin 2))
      (envWords (fun _ => 0) (Env.cons (τ := .nat) n Env.empty)) entry
      (valueWords (fun _ => 0) (τ := .nat) (n + 1)) finish := by
  clear _sourceHeap
  let args : Env [.nat] := Env.cons (τ := .nat) n Env.empty
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, finish, _, execution, result, _⟩ :=
    increment_realizable.functionExec (heapLimit := heapLimit)
      increment_total hw args ⟨#[]⟩ arguments fits trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
  have actualValue : (value : Nat) = n + 1 := result.1
  exact ⟨finish, actualValue ▸ execution⟩

/-- The same source helper-call and branch program has an actual generated
function execution returning the mathematical minimum. This uses the shared
compiler theorem and the unchanged source correctness proof. -/
theorem boundedIncrement_functionExec {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram program) heapLimit 1
      (lowerFunc program (1 : Fin 2))
      (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry
      (valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit)) finish := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, finish, _, execution, result, _⟩ :=
    boundedIncrement_realizable.functionExec (heapLimit := heapLimit)
      boundedIncrement_total hw args ⟨#[]⟩ arguments ⟨sumFits, limitFits⟩ trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨finish, actualValue ▸ execution⟩

/-- The actual compiled machine returns the source-level minimum and preserves
the shared entry state. Its measured instruction count refers to this same
execution, without assuming or claiming an instruction upper bound. -/
theorem boundedIncrement_runUntil {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, targetFinish, bodySteps, target, _, result, invocation, _, execution,
      values, observed, time⟩ :=
    boundedIncrement_realizable.runUntil boundedIncrement_total hw args ⟨#[]⟩ arguments
      ⟨sumFits, limitFits⟩ trivial entry (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have unchanged : targetFinish = entry := invocation.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites program program_noHeapWrites)
    (lowerBody_noSharedWrites program _ (program_noHeapWrites _))
  subst targetFinish
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time⟩

/-- The helper body spends four transitions on addition, four on returning its
value and setting the flag, and two on flag initialization. -/
theorem increment_costBound :
    FunctionCostBound program (0 : Fin 2) (fun _ _ => True) (fun _ _ => 10) := by
  ram_source_cost (n)

/-- The caller reuses the helper's complete call bound. Local initialization,
comparison, assignment and return retain the actual branch selected by the
helper's result. The false branch retains the initialized limit. -/
theorem boundedIncrement_costBound_by_branch :
    FunctionCostBound program (1 : Fin 2) (fun _ _ => True)
      (Implementation.boundedIncrement_onArgs fun n limit _ =>
        callCost program (0 : Fin 2) 10 + if n + 1 ≤ limit then 19 else 18) := by
  ram_source_cost (n limit)
  · ram_source_call (next := fun (value : Nat) _ => if value ≤ limit then 15 else 14)
      using increment_costBound, increment_total
    · rename_i value finish returned
      apply Classical.byCases (p := value ≤ limit)
      · intro within
        apply StmtCostBound.mono
        · ram_source_cost_step
        · norm_num [primCodeSize, fieldCount, if_pos within]
      · intro within
        apply StmtCostBound.mono
        · ram_source_cost_step
        · norm_num [primCodeSize, fieldCount, if_neg within]
    · rename_i value finish returned
      rcases returned with ⟨rfl, _⟩
      exact Nat.le_refl _
  · simp only [Implementation.boundedIncrement_onArgs, Env.head_cons, Env.tail_cons]
    split_ifs <;> omega

/-- The caller reuses the helper's complete call bound. Local initialization,
comparison, the selected assignment, dispatch and return add at most nineteen transitions. -/
theorem boundedIncrement_costBound :
    FunctionCostBound program (1 : Fin 2) (fun _ _ => True)
      (fun _ _ => callCost program (0 : Fin 2) 10 + 19) := by
  apply boundedIncrement_costBound_by_branch.mono_bound
  intro args heap input
  simp only [Implementation.boundedIncrement_onArgs]
  split_ifs <;> omega

/-- The same halted machine invocation returns the mathematical minimum and
satisfies the independent source cost bound, including the outer call and halt. -/
theorem boundedIncrement_runUntil_le {w heapLimit : Nat} (hw : 0 < w) (n limit : Nat)
    (_sourceHeap : Heap)
    (sumFits : n + 1 < 2 ^ w) (limitFits : limit < 2 ^ w) (entry : Ram.Source.State w)
    (codeCapacity : (lowerCode program (1 : Fin 2)).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ (bodySteps : Nat) (target : Ram.State w),
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program) 1
          2 heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl program)
            (lowerFunc program (1 : Fin 2)) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 1 target =
        valueWords (fun _ => 0) (τ := .nat) (min (n + 1) limit) ∧
      Ram.Source.State.Observes heapLimit 0 entry target ∧
      (lowerFunc program (1 : Fin 2)).bodyTime (lowerProgram program) heapLimit
          (envWords (fun _ => 0) (Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty))) entry =
        Part.some bodySteps ∧
      bodySteps ≤ callCost program (0 : Fin 2) 10 + 19 ∧
      Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program (1 : Fin 2)) (callCost program (0 : Fin 2) 10 + 19) + 1 := by
  clear _sourceHeap
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simp only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true]
    omega
  obtain ⟨value, _, targetFinish, bodySteps, target, _, result, invocation, _, execution,
      values, observed, time, bodyBound, invocationBound⟩ :=
    boundedIncrement_realizable.runUntil_le boundedIncrement_total boundedIncrement_costBound
      hw args ⟨#[]⟩ arguments ⟨sumFits, limitFits⟩ trivial trivial entry
      (HeapRep.empty (fun _ => 0) heapLimit entry)
      codeCapacity stackCapacity
  have unchanged : targetFinish = entry := invocation.finish_eq_of_noSharedWrites
    (lowerProgram_noSharedWrites program program_noHeapWrites)
    (lowerBody_noSharedWrites program _ (program_noHeapWrites _))
  subst targetFinish
  have actualValue : (value : Nat) = min (n + 1) limit := result.1
  exact ⟨bodySteps, target, execution, actualValue ▸ values, observed, time,
    bodyBound, invocationBound⟩

/-- The structure wrapper reuses the actual imported scalar implementation.
Its two stored fields and the intermediate increment are the only value ranges;
two nested call levels include the imported helper's own call. -/
theorem structured_update_realizable {w : Nat} :
    FunctionRealizable Structured.program w 2 Structured.updateId
      (Structured.update_onArgs fun input _ =>
        input.1 + 1 < 2 ^ w ∧ input.2 < 2 ^ w) := by
  ram_source_realize (input) using boundedIncrement_realizable, boundedIncrement_total
    via Structured.imports.Implementation.embedding
  all_goals omega

/-- Infer the cost of the real structure copies, projections and imported call.
The witness is chosen before the arguments, so it is a uniform compiler-derived
bound, not a price assigned to the mathematical structure operation. -/
def structuredUpdateCost : { bound : Nat //
    FunctionCostBound Structured.program Structured.updateId (fun _ _ => True)
      (fun _ _ => bound + 2) } := ⟨_, by
  ram_source_cost_intro (input)
  intro heap _
  ram_source_cost_step using
    (ram_source_imported% (FunctionCostBound.renameCalls
      Structured.imports.Implementation.embedding boundedIncrement_costBound))⟩

/-- The structure callee's cost is reusable without reopening its source body. -/
theorem structured_update_costBound :
    FunctionCostBound Structured.program Structured.updateId (fun _ _ => True)
      (fun _ _ => structuredUpdateCost.val + 2) :=
  structuredUpdateCost.property

/-- The caller's own construction and projection are charged around the actual
structure-valued call, using the same shared structural rules. -/
def structuredRunCost : { bound : Nat //
    FunctionCostBound Structured.program Structured.runId (fun _ _ => True)
      (fun _ _ => bound + 2) } := ⟨_, by
  ram_source_cost_intro (n limit)
  intro heap _
  ram_source_cost_step using structured_update_costBound⟩

theorem structured_run_costBound :
    FunctionCostBound Structured.program Structured.runId (fun _ _ => True)
      (fun _ _ => structuredRunCost.val + 2) :=
  structuredRunCost.property

/-- The caller reuses generated source totality for the structure-valued call.
Only mathematical ranges remain after the shared projection/call rules. -/
theorem structured_run_realizable {w : Nat} :
    FunctionRealizable Structured.program w 3 Structured.runId
      (Structured.run_onArgs fun n limit _ => n + 1 < 2 ^ w ∧ limit < 2 ^ w) := by
  ram_source_realize (n limit) using structured_update_realizable, Structured.update_total
  all_goals omega

/-- Add the actual outer call, return and final halt to the inferred body cost. -/
def structuredRunSteps : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Structured.program)
    (lowerFunc Structured.program Structured.runId) (structuredRunCost.val + 2) + 1

/-- The ordinary structure proof and independent compiler-derived cost describe
one actual halted RAM invocation. The launch retains its input representation,
word width and code/stack capacity; input loading is outside this boundary. -/
theorem structured_run_execute_le {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (n limit : Nat) {heap : Heap} {entry : Ram.Source.State w}
    (launch : FunctionLaunch Structured.program Structured.runId 3 heapLimit placement
      (Structured.run_args n limit) heap entry)
    (sumFits : n + 1 < 2 ^ w) :
    ∃ outcome : FunctionExecution Structured.program Structured.runId heapLimit placement
        (Structured.run_args n limit) heap entry,
      outcome.value = min (n + 1) limit ∧ outcome.result.steps ≤ structuredRunSteps := by
  have limitFits : limit < 2 ^ w := launch.arguments (.there .here)
  obtain ⟨outcome, ⟨value, represented, property⟩, bounded⟩ :=
    structured_run_realizable.execute_le (structured_run_total (n, limit) trivial)
      structured_run_costBound launch ⟨sumFits, limitFits⟩ rfl trivial
  have observed : value = outcome.value := represented
  exact ⟨outcome, observed.symm.trans property, bounded⟩

/-- The existing native increment's mathematical contract also protects every
old buffer observation; mapping does not require another scalar proof. -/
theorem increment_map_contract :
    Buffer.Map.Contract (inputKind := .nat) (outputKind := .nat)
      program (0 : Fin 2) rfl (fun n : Nat => n + 1) := by
  apply increment_total.consequence (fun _ _ _ => trivial)
  intro args heap value finish _ property
  refine ⟨property.1, ?_⟩
  rw [property.2]
  intro kind view values observed
  exact observed

/-- A real allocating traversal calling the original increment implementation. -/
def mappedIncrement : Program (Buffer.Map.mapSignature .nat .nat :: signatures) :=
  Buffer.Map.program (inputKind := .nat) (outputKind := .nat) program (0 : Fin 2) rfl

/-- The existing scalar range and cost proofs suffice for the allocating map.
The conclusion describes fresh output, every retained old view and the same
halted RAM invocation. Only input ranges and sufficient storage remain. -/
theorem mappedIncrement_execute {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (source : Buffer .nat) (input : Array Nat) {heap : Heap} {cursor : Nat}
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch mappedIncrement (Buffer.Map.entry .nat .nat signatures)
      1 heapLimit placement (BufferMap.mapArgs source (0 : Nat)) heap cursor entry)
    (observed : source.Contents heap input)
    (fits : ∀ i (hi : i < input.size), input[i] + 1 < 2 ^ w)
    (capacity : cursor + input.size ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution mappedIncrement (Buffer.Map.entry .nat .nat signatures)
        1 heapLimit placement (BufferMap.mapArgs source (0 : Nat)) heap entry,
      outcome.value.Contents outcome.heap (input.map (fun n => n + 1)) ∧
        outcome.value.object = heap.objects.size ∧ Buffer.PreservesContents heap outcome.heap ∧
        outcome.result.steps ≤ BufferMap.linearInvocationBound
          (inputKind := .nat) (outputKind := .nat) program (0 : Fin 2) rfl 10 input.size ∧
        outcome.cursor ≤ cursor + input.size := by
  have realizable : FunctionRealizable program w 0 (0 : Fin 2)
      (BufferMap.scalarPre (inputKind := .nat) (outputKind := .nat)
        rfl (fun n : Nat => n + 1 < 2 ^ w)) :=
    increment_realizable
  have bounded : FunctionCostBound program (0 : Fin 2)
      (BufferMap.scalarPre (inputKind := .nat) (outputKind := .nat)
        rfl (fun n : Nat => n + 1 < 2 ^ w))
      (BufferMap.scalarBound (inputKind := .nat) (outputKind := .nat)
        rfl (fun _ : Nat => 10)) :=
    increment_costBound.consequence (fun _ _ _ => trivial)
  have resources := BufferMap.CalleeResources.of_functionRealizable
    (heapLimit := heapLimit) realizable
  have timeBound := BufferMap.CalleeCostBound.of_functionCostBound
    (heapLimit := heapLimit) realizable bounded
  simpa only [Nat.mul_zero, Nat.add_zero, BufferMap.invocationBound_const] using
    BufferMap.execute increment_map_contract resources timeBound source input (0 : Nat)
      launch observed fits (by simpa only [Nat.mul_zero, Nat.add_zero] using capacity)

/-- The same bound used by `mappedIncrement_execute` is linear in the array
length. Word ranges and storage capacity remain in that execution theorem. -/
theorem mappedIncrement_bound_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun length => (BufferMap.linearInvocationBound
        (inputKind := .nat) (outputKind := .nat) program (0 : Fin 2) rfl 10 length : ℝ))
      (fun length : Nat => (length : ℝ)) :=
  BufferMap.isBigO_linearInvocationBound program (0 : Fin 2) rfl 10

/-- Infer the actual structure-valued helper's uniform body cost once. -/
def structuredRangeAddCost : { bound : Nat //
    FunctionCostBound StructuredRange.program StructuredRange.addId (fun _ _ => True)
      (fun _ _ => bound + 2) } := ⟨_, by
  ram_source_cost_intro (input amount)
  intro heap _
  ram_source_cost_step⟩

/-- The same helper cost is reusable at every actual loop call. -/
theorem structured_range_add_costBound :
    FunctionCostBound StructuredRange.program StructuredRange.addId (fun _ _ => True)
      (fun _ _ => structuredRangeAddCost.val + 2) :=
  structuredRangeAddCost.property

/-- The finite-range guard has a uniform bound at native loop coordinates. -/
def structuredRangeGuardCost : { bound : Nat //
    ∀ (mutable : StructuredRange.sum_loop1.NativeMutable)
      (captures : StructuredRange.sum_loop1.NativeCaptured) (heap : Heap),
      StmtCostBound StructuredRange.program StructuredRange.sum_loop1.Guard
        ⟨StructuredRange.sum_loop1.NativeCaptureView.symm (mutable, captures), heap⟩ bound } := ⟨_, by
  intro mutable captures heap
  ram_source_locals StructuredRange.sum_loop1
  ram_source_cost_step⟩

/-- Structure copies, the real helper call and the cursor increment all occur
in this compiler-derived bound; no mathematical mapper is charged as a primitive. -/
def structuredRangeBodyCost : { bound : Nat //
    ∀ (mutable : StructuredRange.sum_loop1.NativeMutable)
      (captures : StructuredRange.sum_loop1.NativeCaptured) (heap : Heap),
      StmtCostBound StructuredRange.program StructuredRange.sum_loop1.Body
        ⟨StructuredRange.sum_loop1.NativeCaptureView.symm (mutable, captures), heap⟩ bound } := ⟨_, by
  intro mutable captures heap
  ram_source_locals StructuredRange.sum_loop1
  ram_source_cost_step using structured_range_add_costBound⟩

/-- The dynamic positive stride determines the actual number of rounds. Shared
loop accounting combines this count with inferred guard and helper-call costs. -/
theorem structured_range_loop_costBound
    (entry : State _)
    (positive : 0 < StructuredRange.sum_loop1.nativeRangeStep
      (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2) :
    StmtCostBound StructuredRange.program StructuredRange.sum_loop1.Code entry
      (StmtCostBound.whileLinearBound structuredRangeGuardCost.val structuredRangeBodyCost.val
        ((StructuredRange.sum_loop1.nativeRangeStop
            (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2 -
          (StructuredRange.sum_loop1.NativeCaptureView entry.locals).1.1 +
          StructuredRange.sum_loop1.nativeRangeStep
            (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2 - 1) /
          StructuredRange.sum_loop1.nativeRangeStep
            (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2)) := by
  let locals := StructuredRange.sum_loop1.NativeCaptureView entry.locals
  have paid := @StmtCostBound.while_range_encoded _ _ _ _ _ _
    StructuredRange.sum_loop1.NativeCaptureView
    StructuredRange.program StructuredRange.sum_loop1.Guard StructuredRange.sum_loop1.Body
    locals.2 _ _ positive BoundedInput.sourceEquiv
    (StructuredRange.sum_loop1.nativeBodyStep locals.2)
    (StructuredRange.sum_loop1.native_guard_eq locals.2)
    (StructuredRange.sum_loop1.native_body_eq locals.2)
    structuredRangeGuardCost.val structuredRangeBodyCost.val
    (fun index acc heap => structuredRangeGuardCost.property (index, acc) locals.2 heap)
    (fun index acc heap _ => structuredRangeBodyCost.property (index, acc) locals.2 heap)
    locals.1.1 locals.1.2 entry.heap
  simp only [locals, Prod.mk.eta, Equiv.symm_apply_apply, Std.Legacy.Range.size] at paid
  exact @paid

private def structuredRangeSumCost (start stop k : Nat) : { bound : Nat //
    FunctionCostBound StructuredRange.program StructuredRange.sumId
      (StructuredRange.sum_onArgs fun _ actualStart actualStop actualK _ =>
        actualStart = start ∧ actualStop = stop ∧ actualK = k)
      (fun _ _ => bound) } := ⟨_, by
  ram_source_cost_intro (initial actualStart actualStop actualK)
  rintro heap ⟨sameStart, sameStop, sameK⟩
  simp only [Env.head_cons, Env.tail_cons] at sameStart sameStop sameK
  subst actualStart actualStop actualK
  ram_source_cost_step using structured_range_add_costBound
  change StmtCostBound _ _ _
    (StmtCostBound.whileLinearBound structuredRangeGuardCost.val structuredRangeBodyCost.val
      ((stop - start + k) / (k + 1)))
  have loop := @structured_range_loop_costBound
  ram_source_locals StructuredRange.sum_loop1 at loop ⊢
  simp only [StructuredRange.sum_loop1.Code] at loop
  refine @loop _ ?_
  exact Nat.zero_lt_succ k⟩

/-- The complete source body includes its pre-loop helper call, range setup,
all iterations and final return, using the inferred compiler charges. -/
def structuredRangeSumBodyBound (start stop k : Nat) : Nat :=
  (structuredRangeSumCost start stop k).val

/-- The inferred budget is affine in the ordinary number of range elements.
Both its per-round coefficient and fixed overhead come from the same compiler
proof; the input structure, heap and step value do not change those constants. -/
theorem structuredRangeSumBodyBound_eq (start stop k : Nat) :
    structuredRangeSumBodyBound start stop k =
      (structuredRangeGuardCost.val + structuredRangeBodyCost.val + 10) *
        ((stop - start + k) / (k + 1)) + structuredRangeSumBodyBound 0 0 0 := by
  simp only [structuredRangeSumBodyBound, structuredRangeSumCost,
    StmtCostBound.whileLinearBound]
  omega

/-- The same full function has a bound in its ordinary numeric parameters;
the initial structure and calling heap do not alter this uniform bound. -/
theorem structured_range_sum_costBound :
    FunctionCostBound StructuredRange.program StructuredRange.sumId (fun _ _ => True)
      (StructuredRange.sum_onArgs fun _ start stop k _ => structuredRangeSumBodyBound start stop k) := by
  intro args heap _
  exact (structuredRangeSumCost args.tail.head args.tail.tail.head args.tail.tail.tail.head).property
    args heap ⟨rfl, rfl, rfl⟩

/-- The actual structure helper uses no nested calls. Both its computed sum
and the retained limit field must fit the selected word width. -/
theorem structured_range_add_realizable {w : Nat} :
    FunctionRealizable StructuredRange.program w 0 StructuredRange.addId
      (StructuredRange.add_onArgs fun input amount _ =>
        input.1 + amount < 2 ^ w ∧ input.2 < 2 ^ w) := by
  ram_source_realize (input amount)
  all_goals omega

private def structuredRangeInvariant (stop stride total cursor limit index : Nat)
    (acc : BoundedInput) (_heap : Heap) : Prop :=
  acc.value + (List.range' index ((stop - index + stride - 1) / stride) stride).sum = total ∧
    index + ((stop - index + stride - 1) / stride) * stride = cursor ∧
    acc.limit = limit

private theorem structuredRangeInvariant_step
    {stop stride total cursor limit index : Nat} {acc : BoundedInput} {heap : Heap}
    (positive : 0 < stride)
    (current : structuredRangeInvariant stop stride total cursor limit index acc heap)
    (inside : index < stop) :
    acc.value + index ≤ total ∧ index + stride ≤ cursor ∧
      structuredRangeInvariant stop stride total cursor limit (index + stride)
        (BoundedInput.mk (acc.value + index) acc.limit) heap := by
  have countStep : (stop - index + stride - 1) / stride =
      (stop - (index + stride) + stride - 1) / stride + 1 :=
    Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside
  rcases current with ⟨sumEq, cursorEq, limitEq⟩
  rw [countStep, List.range'_succ, List.sum_cons] at sumEq
  rw [countStep, Nat.add_mul, Nat.one_mul] at cursorEq
  refine ⟨by omega, by omega, ?_⟩
  exact ⟨by dsimp; omega, by omega, limitEq⟩

/-- Native coordinates expose the two actual guard operands; the other captured
fields do not introduce extra word operations in this guard. -/
theorem structured_range_guard_realizable {w : Nat} (hw : 0 < w)
    (captures : StructuredRange.sum_loop1.NativeCaptured) (index : Nat)
    (acc : BoundedInput) (heap : Heap)
    (indexFits : index < 2 ^ w)
    (stopFits : StructuredRange.sum_loop1.nativeRangeStop captures < 2 ^ w) :
    RealizationWP StructuredRange.program w 1 StructuredRange.sum_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨StructuredRange.sum_loop1.NativeCaptureView.symm ((index, acc, ()), captures), heap⟩ := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_locals StructuredRange.sum_loop1 at stopFits ⊢
  ram_source_realize_step
  all_goals first | omega | split <;> omega

/-- Realize the actual helper call, accumulator assignment and cursor increment.
The generated source contract supplies the helper's returned structure. -/
theorem structured_range_body_realizable {w : Nat}
    (captures : StructuredRange.sum_loop1.NativeCaptured) (index : Nat)
    (acc : BoundedInput) (heap : Heap)
    (sumFits : acc.value + index < 2 ^ w) (limitFits : acc.limit < 2 ^ w)
    (cursorFits : index + StructuredRange.sum_loop1.nativeRangeStep captures < 2 ^ w) :
    RealizationWP StructuredRange.program w 1 StructuredRange.sum_loop1.Body
      (fun _ => True) (fun _ _ => True)
      ⟨StructuredRange.sum_loop1.NativeCaptureView.symm ((index, acc, ()), captures), heap⟩ := by
  ram_source_locals StructuredRange.sum_loop1 at cursorFits ⊢
  ram_source_realize_step using structured_range_add_realizable, StructuredRange.add_total
  all_goals
    simp (config := { failIfUnchanged := false }) only [structured_range_add_eq] at *
  all_goals ram_source_locals StructuredRange.sum_loop1 at *
  all_goals omega

private theorem structured_range_loop_realizable {w : Nat} (hw : 0 < w)
    (total cursor limit : Nat) (entry : State _)
    (positive : 0 < StructuredRange.sum_loop1.nativeRangeStep
      (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2)
    (current : structuredRangeInvariant
      (StructuredRange.sum_loop1.nativeRangeStop
        (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2)
      (StructuredRange.sum_loop1.nativeRangeStep
        (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2)
      total cursor limit
      (StructuredRange.sum_loop1.NativeCaptureView entry.locals).1.1
      (StructuredRange.sum_loop1.NativeCaptureView entry.locals).1.2.1 entry.heap)
    (sumFits : total < 2 ^ w) (cursorFits : cursor < 2 ^ w) (limitFits : limit < 2 ^ w)
    (stopFits : StructuredRange.sum_loop1.nativeRangeStop
      (StructuredRange.sum_loop1.NativeCaptureView entry.locals).2 < 2 ^ w) :
    RealizationWP StructuredRange.program w 1 StructuredRange.sum_loop1.Code
      (fun finish =>
        (StructuredRange.sum_loop1.NativeCaptureView finish.locals).1.2.1.value < 2 ^ w ∧
        (StructuredRange.sum_loop1.NativeCaptureView finish.locals).1.2.1.limit < 2 ^ w)
      (fun _ _ => True) entry := by
  let locals := StructuredRange.sum_loop1.NativeCaptureView entry.locals
  have realized := RealizationWP.while_range_encoded_invariant (w := w) (depth := 1)
    StructuredRange.sum_loop1.NativeCaptureView
    StructuredRange.program StructuredRange.sum_loop1.Guard StructuredRange.sum_loop1.Body
    locals.2 _ _ positive BoundedInput.sourceEquiv
    (StructuredRange.sum_loop1.nativeBodyStep locals.2)
    (StructuredRange.sum_loop1.native_guard_eq locals.2)
    (StructuredRange.sum_loop1.native_body_eq locals.2)
    (fun index mutable heap => structuredRangeInvariant _ _ total cursor limit index mutable.1 heap)
    (fun index mutable heap invariant => by
      rcases mutable with ⟨acc, ⟨⟩⟩
      apply structured_range_guard_realizable hw locals.2 index acc heap _ stopFits
      rcases invariant with ⟨_, reached, _⟩
      omega)
    (fun index mutable heap invariant inside => by
      rcases mutable with ⟨acc, ⟨⟩⟩
      obtain ⟨sumBound, cursorBound, _⟩ := structuredRangeInvariant_step positive invariant inside
      apply structured_range_body_realizable locals.2 index acc heap
        (lt_of_le_of_lt sumBound sumFits) _ (lt_of_le_of_lt cursorBound cursorFits)
      have retained : acc.limit = limit := invariant.2.2
      simpa only [retained] using limitFits)
    (fun index mutable next heap invariant inside stepEq => by
      rcases mutable with ⟨acc, ⟨⟩⟩
      rcases next with ⟨next, ⟨⟩⟩
      have nextEq := congrArg (fun output => output.2.1) stepEq
      change BoundedInput.mk (acc.value + index) acc.limit = next at nextEq
      subst next
      exact (structuredRangeInvariant_step positive invariant inside).2.2)
    locals.1.1 locals.1.2 entry.heap current
  simp only [locals, Prod.mk.eta, Equiv.symm_apply_apply] at realized
  apply realized.mono_post
  · intro finish preserved
    rcases preserved.2 with ⟨sumEq, _, limitEq⟩
    exact ⟨by omega, by omega⟩
  · intro value finish _
    trivial

/-- One call level suffices for every iteration and the pre-loop helper call.
The final sum bounds all intermediate additions. The last cursor may exceed
`stop`, and its actual value and the eagerly computed stride remain explicit. -/
theorem structured_range_sum_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable StructuredRange.program w 1 StructuredRange.sumId
      (StructuredRange.sum_onArgs fun initial start stop k _ =>
        initial.1 + (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum < 2 ^ w ∧
        start + ((stop - start + k) / (k + 1)) * (k + 1) < 2 ^ w ∧
        k + 1 < 2 ^ w ∧ stop < 2 ^ w ∧ initial.2 < 2 ^ w) := by
  ram_source_realize (initial start stop k) using
    structured_range_add_realizable, StructuredRange.add_total
  all_goals
    rcases ‹_ ∧ _ ∧ k + 1 < 2 ^ w ∧ stop < 2 ^ w ∧ initial.2 < 2 ^ w› with
      ⟨sumFits, cursorFits, strideFits, stopFits, limitFits⟩
    simp (config := { failIfUnchanged := false }) only [structured_range_add_eq, Nat.add_zero] at *
    ram_source_locals StructuredRange.sum_loop1 at *
    first
    | omega
    | refine (structured_range_loop_realizable hw
        (initial.1 + (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum)
        (start + ((stop - start + k) / (k + 1)) * (k + 1)) initial.2 _
        ?_ ?_ sumFits cursorFits limitFits ?_).mono_post ?_ ?_
      · ram_source_locals StructuredRange.sum_loop1
        omega
      · simp only [structuredRangeInvariant]
        ram_source_locals StructuredRange.sum_loop1 at *
        simp_all only [Nat.add_succ_sub_one, Nat.add_zero, and_true]
      · ram_source_locals StructuredRange.sum_loop1 at stopFits ⊢
        exact stopFits
      · intro finish fits
        ram_source_locals StructuredRange.sum_loop1 at fits
        ram_source_realize_step
      · intro value finish _
        trivial

/-- The same inferred source budget includes the outer call, return and halt. -/
def structuredRangeSumSteps (start stop k : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl StructuredRange.program)
    (lowerFunc StructuredRange.program StructuredRange.sumId)
    (structuredRangeSumBodyBound start stop k) + 1

/-- The ordinary structure/range theorem and its independently derived budget
describe one actual halted RAM invocation. The launch retains the preloaded
input representation and code/stack capacity, while the three extra conditions
cover the actual sum, final cursor and computed stride, including empty ranges. -/
theorem structured_range_sum_execute_le {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (initial : BoundedInput) (start stop k : Nat) {heap : Heap} {entry : Ram.Source.State w}
    (launch : FunctionLaunch StructuredRange.program StructuredRange.sumId 1 heapLimit placement
      (StructuredRange.sum_inputEmbedding (initial, start, stop, k)) heap entry)
    (sumFits : initial.value +
      (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum < 2 ^ w)
    (cursorFits : start + ((stop - start + k) / (k + 1)) * (k + 1) < 2 ^ w)
    (strideFits : k + 1 < 2 ^ w) :
    ∃ outcome : FunctionExecution StructuredRange.program StructuredRange.sumId heapLimit placement
        (StructuredRange.sum_inputEmbedding (initial, start, stop, k)) heap entry,
      BoundedInput.sourceRepresentation.Rel
        (BoundedInput.mk (initial.value +
          (List.range' start ((stop - start + k) / (k + 1)) (k + 1)).sum) initial.limit)
        outcome.value outcome.heap ∧
      outcome.result.steps ≤ structuredRangeSumSteps start stop k := by
  have stopFits : stop < 2 ^ w := launch.arguments (.there (.there .here))
  have initialFits : ValueFits w (BoundedInput.sourceEncode initial) := launch.arguments .here
  have limitFits : initial.limit < 2 ^ w := initialFits.2
  obtain ⟨outcome, ⟨value, represented, property⟩, bounded⟩ :=
    (structured_range_sum_realizable launch.positive).execute_le
      (structured_range_sum_total (initial, start, stop, k) trivial)
      structured_range_sum_costBound launch
      ⟨sumFits, cursorFits, strideFits, stopFits, limitFits⟩ rfl trivial
  subst value
  exact ⟨outcome, represented, bounded⟩

end Complexity.Language.Examples.Scalar
