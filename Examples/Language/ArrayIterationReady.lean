/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.ArrayIterationCompiled
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendReady
import Complexity.Computability.Ram.Compiler.Language.Arena.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop.Models
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.LocalsTactic
import Complexity.Computability.Ram.Compiler.Language.Representation

/-!
# Cumulative allocation for the existing array-record loop

The unchanged `ArrayRangeNative.repeatAppend` allocates a new array each round
and retains earlier arrays. Its reserve is the sum of all new payload lengths,
not merely the final length. The current array layout charges no per-array
header cells.

The mathematical guard/body contracts transport observations at actual heaps.
The shared readiness rule reuses them on an existing source execution, with
word ranges and cumulative capacity explicit. This adds neither a second
termination proof nor a new implementation. The full-function result uses the
original source totality, the existing nonuniform time certificate and an actual
preloaded launch. Its typed outcome retains the original mathematical contract,
the exact cursor growth and the same halted runner's instruction bound. No
input-loading or exact peak-live-space claim follows from this retained allocation bound.
-/

namespace Complexity.Language.Examples.LinkedList.NativeRange.RepeatAppendReady

open Ram.LanguageCompiler
open ArrayRangeNative.Source.repeatAppend_loop1
open scoped BigOperators

/-- All fresh array cells allocated by the remaining rounds; old arrays remain allocated. -/
def reserve (count size chunk : Nat) : Nat :=
  ∑ index ∈ Finset.range count, (size + (index + 1) * chunk)

@[simp] theorem reserve_zero (size chunk : Nat) : reserve 0 size chunk = 0 := by
  simp only [reserve, Finset.sum_range_zero]

theorem reserve_succ (count size chunk : Nat) :
    reserve (count + 1) size chunk = size + chunk + reserve count (size + chunk) chunk := by
  unfold reserve
  rw [Finset.sum_range_succ']
  have shifted : (∑ index ∈ Finset.range count, (size + (index + 1 + 1) * chunk)) =
      ∑ index ∈ Finset.range count, (size + chunk + (index + 1) * chunk) := by
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [shifted]
  simp only [Nat.zero_add, Nat.one_mul]
  omega

/-- Conservation of the remaining reservation across one active round. -/
theorem reserve_model_step (model : Model) (active : modelGuard model = true) :
    (model_state model).values.size + (model_chunk model).size +
        reserve (model_remaining (modelStep model)) (model_state (modelStep model)).values.size
          (model_chunk (modelStep model)).size =
      reserve (model_remaining model) (model_state model).values.size (model_chunk model).size := by
  change decide (0 < model_remaining model) = true at active
  have positive : 0 < model_remaining model := of_decide_eq_true active
  change (model_state model).values.size + (model_chunk model).size +
      reserve (model_remaining model - 1)
        ((model_state model).values ++ model_chunk model).size (model_chunk model).size = _
  rw [Array.size_append, ← reserve_succ, Nat.sub_add_cancel positive]

/-- Word ranges and the cumulative unused reservation, expressed only in mathematical locals. -/
def invariant (w heapLimit : Nat) (model : Model) (cursor : Nat) : Prop :=
  model_remaining model < 2 ^ w ∧
  (model_state model).copies + model_remaining model < 2 ^ w ∧
  (model_state model).values.size + model_remaining model * (model_chunk model).size < 2 ^ w ∧
  (model_chunk model).size < 2 ^ w ∧
  (∀ i (hi : i < (model_state model).values.size), (model_state model).values[i] < 2 ^ w) ∧
  (∀ i (hi : i < (model_chunk model).size), (model_chunk model)[i] < 2 ^ w) ∧
  cursor + reserve (model_remaining model) (model_state model).values.size
    (model_chunk model).size ≤ heapLimit

/-- Mathematical ranges and sufficient remaining capacity survive an actual round. -/
theorem invariant_step {w heapLimit cursor : Nat} {model : Model}
    (valid : invariant w heapLimit model cursor) (active : modelGuard model = true) :
    invariant w heapLimit (modelStep model)
      (cursor + (model_state model).values.size + (model_chunk model).size) := by
  obtain ⟨remainingFits, copiesFit, sizeFit, chunkSizeFit, valuesFit, chunkFit, space⟩ := valid
  change decide (0 < model_remaining model) = true at active
  have positive : 0 < model_remaining model := of_decide_eq_true active
  have sizeStep : (model_state model).values.size + (model_chunk model).size +
      (model_remaining model - 1) * (model_chunk model).size =
      (model_state model).values.size + model_remaining model * (model_chunk model).size := by
    calc
      _ = (model_state model).values.size +
          (model_remaining model - 1 + 1) * (model_chunk model).size := by ring
      _ = _ := by rw [Nat.sub_add_cancel positive]
  have reserved := reserve_model_step model active
  change model_remaining model - 1 < 2 ^ w ∧
    (model_state model).copies + 1 + (model_remaining model - 1) < 2 ^ w ∧
    ((model_state model).values ++ model_chunk model).size +
      (model_remaining model - 1) * (model_chunk model).size < 2 ^ w ∧
    (model_chunk model).size < 2 ^ w ∧
    (∀ i (hi : i < ((model_state model).values ++ model_chunk model).size),
      ((model_state model).values ++ model_chunk model)[i] < 2 ^ w) ∧
    (∀ i (hi : i < (model_chunk model).size), (model_chunk model)[i] < 2 ^ w) ∧
    cursor + (model_state model).values.size + (model_chunk model).size +
      reserve (model_remaining model - 1)
        ((model_state model).values ++ model_chunk model).size (model_chunk model).size ≤ heapLimit
  refine ⟨by omega, by omega, ?_, chunkSizeFit, ?_, chunkFit, ?_⟩
  · simpa only [Array.size_append, sizeStep] using sizeFit
  · have stateMem : ∀ value ∈ (model_state model).values, value < 2 ^ w :=
      Array.forall_getElem.mp valuesFit
    have chunkMem : ∀ value ∈ model_chunk model, value < 2 ^ w :=
      Array.forall_getElem.mp chunkFit
    exact Array.forall_getElem.mpr (Array.forall_mem_append.mpr ⟨stateMem, chunkMem⟩)
  · change (model_state model).values.size + (model_chunk model).size +
        reserve (model_remaining model - 1)
          ((model_state model).values ++ model_chunk model).size (model_chunk model).size = _
      at reserved
    omega

/-- The current mathematical record has word-sized fields; any actual observation
inherits these ranges through the shared representation rules. -/
theorem invariant_state_fits {w heapLimit cursor : Nat} {model : Model}
    (valid : invariant w heapLimit model cursor) :
    RepresentationFits state_representation w (model_state model) := by
  have sizeFits := valid.2.2.1
  have copiesFits := valid.2.1
  apply RepresentationFits.comap
  apply RepresentationFits.prod
  · apply RepresentationFits.array
    change (model_state model).values.size < 2 ^ w
    omega
  · apply RepresentationFits.ofEmbedding
    change (model_state model).copies < 2 ^ w
    omega

/-- The actual guard does not allocate; its scalar comparison uses the represented count. -/
theorem guard_measured {w heapLimit cursor : Nat}
    (model : Model) (locals : Locals) (heap : Heap)
    (valid : invariant w heapLimit model cursor) (related : modelRel model locals heap) :
    ArenaMeasured ArrayRangeNative.Source.program w heapLimit 2 Guard
      (fun _ _ finalCursor _ => finalCursor = cursor)
      ⟨View.symm locals, heap⟩ cursor := by
  have remainingEq : model_remaining model = locals.1 := model_rel_remaining related
  have remainingFits : locals.1 < 2 ^ w := by have := valid.1; omega
  ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1 at *
  ram_source_arena_step
  all_goals first | omega | split <;> omega

/-- One actual append call followed by the existing scalar record update and decrement. -/
theorem body_measured {w heapLimit cursor : Nat} (positive : 0 < w)
    (model : Model) (locals : Locals) (heap : Heap)
    (valid : invariant w heapLimit model cursor) (active : modelGuard model = true)
    (related : modelRel model locals heap) :
    ArenaMeasured ArrayRangeNative.Source.program w heapLimit 2 Body
      (fun _ control finalCursor _ => control = .normal ∧
        finalCursor = cursor + (model_state model).values.size + (model_chunk model).size)
      ⟨View.symm locals, heap⟩ cursor := by
  have stateFits := RepresentationFits.valueFits (invariant_state_fits valid)
    (model_rel_state related)
  obtain ⟨remainingFits, copiesFit, sizeFit, chunkSizeFit, valuesFit, chunkFit, space⟩ := valid
  change decide (0 < model_remaining model) = true at active
  have activeCount : 0 < model_remaining model := of_decide_eq_true active
  have stateObserved := model_rel_state related
  have chunkObserved := model_rel_chunk related
  have leftObserved : locals.2.1.1.Contents heap (model_state model).values := stateObserved.1
  have copiesEq : (model_state model).copies = locals.2.1.2 := stateObserved.2
  have remainingEq : model_remaining model = locals.1 := model_rel_remaining related
  have chunkDescriptorFits := RepresentationFits.valueFits
    (RepresentationFits.array .nat chunkSizeFit) chunkObserved
  have roundSizeFits : (model_state model).values.size + (model_chunk model).size < 2 ^ w := by
    have multiple : (model_chunk model).size ≤
        model_remaining model * (model_chunk model).size := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (model_chunk model).size activeCount
    omega
  have roundSpace : cursor + (model_state model).values.size +
      (model_chunk model).size ≤ heapLimit := by
    have reserveStep := reserve_succ (model_remaining model - 1)
      (model_state model).values.size (model_chunk model).size
    rw [Nat.sub_add_cancel activeCount] at reserveStep
    rw [reserveStep] at space
    omega
  have nextCopiesFit : locals.2.1.2 + 1 < 2 ^ w := by omega
  have currentRemainingFit : locals.1 < 2 ^ w := by omega
  have appended := BufferCopy.append_arenaMeasured (w := w) (heapLimit := heapLimit)
    (cursor := cursor) positive locals.2.1.1 locals.2.2.2.1
    (model_state model).values (model_chunk model) heap leftObserved chunkObserved
    valuesFit chunkFit roundSizeFits roundSpace
  ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1 at *
  ram_source_arena_step
  ram_source_arena_call measured using appended
    as appendFinish target appendCursor appendSteps appendObserved targetFits via
    ArrayRangeNative.Source.imports.Complexity.Language.Buffer.Copy.embedding
  have cursorEq := appendObserved.1
  subst appendCursor
  ram_source_arena_step

/-- The same finite loop is ready, consuming exactly the sum of its fresh arrays. -/
theorem loop_ready {w heapLimit cursor : Nat} (positive : 0 < w)
    (model : Model) (entry : State _)
    (valid : invariant w heapLimit model cursor)
    (related : modelRel model (View entry.locals) entry.heap)
    {finish : State _} {control : Control _}
    (execution : Complexity.Language.Exec ArrayRangeNative.Source.program Code entry finish control)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ∃ finalCursor, ArenaReady execution w heapLimit 2 cursor finalCursor ∧
      finalCursor = cursor + reserve (model_remaining model) (model_state model).values.size
        (model_chunk model).size ∧ control = .normal ∧
      ∃ finalModel, modelRel finalModel (View finish.locals) finish.heap ∧
        invariant w heapLimit finalModel finalCursor ∧ modelGuard finalModel = false := by
  obtain ⟨finalCursor, ready, normal, finalModel, observed,
      ⟨finalValid, accounting⟩, stopped⟩ :=
    ArenaReady.while_model_of_exec View modelRel modelGuard modelStep
      guard_model (fun current _ => body_model current)
      (fun current _ currentCursor => invariant w heapLimit current currentCursor ∧
        currentCursor + reserve (model_remaining current) (model_state current).values.size
          (model_chunk current).size =
        cursor + reserve (model_remaining model) (model_state model).values.size (model_chunk model).size)
      (by
        intro current state currentCursor allowed related after decision tested _
        have measured : ArenaMeasured ArrayRangeNative.Source.program w heapLimit 2 Guard
            (fun _ _ finalCursor _ => finalCursor = currentCursor) state currentCursor := by
          simpa only [Equiv.symm_apply_apply] using
            guard_measured current (View state.locals) state.heap allowed.1 related
        obtain ⟨finalCursor, _, ready, _, sameCursor⟩ := measured.at_exec tested
        subst finalCursor
        exact ⟨currentCursor, ready, allowed⟩)
      (by
        intro current state currentCursor allowed active related after iterated _
        have measured : ArenaMeasured ArrayRangeNative.Source.program w heapLimit 2 Body
            (fun _ control finalCursor _ => control = .normal ∧
              finalCursor = currentCursor + (model_state current).values.size + (model_chunk current).size)
            state currentCursor := by
          simpa only [Equiv.symm_apply_apply] using
            body_measured positive current (View state.locals) state.heap allowed.1 active related
        obtain ⟨finalCursor, _, ready, _, _, sameCursor⟩ := measured.at_exec iterated
        subst finalCursor
        refine ⟨_, ready, invariant_step allowed.1 active, ?_⟩
        have stepReserve := reserve_model_step current active
        have conserved := allowed.2
        omega)
      execution related ⟨valid, rfl⟩ successful
  refine ⟨finalCursor, ready, ?_, normal, finalModel, observed, finalValid, stopped⟩
  change decide (0 < model_remaining finalModel) = false at stopped
  have empty : model_remaining finalModel = 0 := Nat.eq_zero_of_not_pos (of_decide_eq_false stopped)
  simpa only [empty, reserve_zero, Nat.add_zero] using accounting

/-- Obtain source termination from the existing correctness contract and measure
that very execution, with no additional termination or instruction-budget premise. -/
theorem function_measured {w heapLimit cursor : Nat} (positive : 0 < w)
    (count : Nat) (chunkValues : Array Nat) (initialValue : Payload)
    (chunk : Buffer .nat) (initial : Buffer .nat × Nat) (heap : Heap)
    (chunkObserved : chunk.Contents heap chunkValues)
    (initialObserved : state_representation.Rel initialValue initial heap)
    (valid : invariant w heapLimit
      (mkModel (remaining := count) (state := initialValue) (initial := initialValue)
        (chunk := chunkValues) (count := count)) cursor) :
    ArenaMeasured ArrayRangeNative.Source.program w heapLimit 2
      (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
      (fun _ control finalCursor _ => ∃ value, control = .returned value ∧
        finalCursor = cursor + reserve count initialValue.values.size chunkValues.size)
      ⟨ArrayRangeNative.Source.repeatAppend_args count chunk initial, heap⟩ cursor := by
  have total := (repeatAppend_copies count chunkValues initialValue).wp
    (ArrayRangeNative.Source.repeatAppend_args count chunk initial) heap
    ⟨rfl, chunkObserved, initialObserved⟩
  have loopTotal := (TotalWP.seq_iff _ _).mp
    ((TotalWP.letPrim_iff _ _).mp ((TotalWP.letPrim_iff _ _).mp total))
  let model := mkModel (remaining := count) (state := initialValue) (initial := initialValue)
    (chunk := chunkValues) (count := count)
  have measured := ArenaMeasured.of_totalWP
    (w := w) (heapLimit := heapLimit) (depth := 2) (cursor := cursor)
    (post := fun after control finalCursor =>
      finalCursor = cursor + reserve count initialValue.values.size chunkValues.size ∧
        control = .normal ∧ ∃ finalModel, modelRel finalModel (View after.locals) after.heap ∧
          invariant w heapLimit finalModel finalCursor ∧ modelGuard finalModel = false)
    loopTotal (by
      intro after control execution successful
      exact loop_ready positive model _ valid
        (by
          dsimp only [model]
          ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1
          simp_all [modelRel, mkModel, state_representation]) execution
        (by cases control <;> simp_all [Control.Satisfies]))
  have countFits : count < 2 ^ w := valid.1
  have initialFits := RepresentationFits.valueFits (invariant_state_fits valid) initialObserved
  ram_source_arena_step
  apply measured.mono_post
  rintro after control finalCursor steps ⟨cursorEq, rfl, finalModel, related, finalValid, _⟩
  have finalFits := RepresentationFits.valueFits (invariant_state_fits finalValid)
    (model_rel_state related)
  ram_source_locals ArrayRangeNative.Source.repeatAppend_loop1 at *
  ram_source_arena_step

/-- Attach the loop readiness to the unchanged function's two bindings and final return. -/
theorem body_ready {w heapLimit cursor : Nat} (positive : 0 < w)
    (count : Nat) (chunkValues : Array Nat) (initialValue : Payload)
    (chunk : Buffer .nat) (initial : Buffer .nat × Nat) (heap : Heap)
    (chunkObserved : chunk.Contents heap chunkValues)
    (initialObserved : state_representation.Rel initialValue initial heap)
    (valid : invariant w heapLimit
      (mkModel (remaining := count) (state := initialValue) (initial := initialValue)
        (chunk := chunkValues) (count := count)) cursor)
    {finish : State _} {value : Value (.prod (.buffer .nat) .nat)}
    (execution : Exec ArrayRangeNative.Source.program
      (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
      ⟨ArrayRangeNative.Source.repeatAppend_args count chunk initial, heap⟩ finish (.returned value)) :
    ArenaReady execution w heapLimit 2 cursor
      (cursor + reserve count initialValue.values.size chunkValues.size) := by
  obtain ⟨finalCursor, _, ready, _, _, _, cursorEq⟩ :=
    (function_measured positive count chunkValues initialValue chunk initial heap
      chunkObserved initialObserved valid).at_exec execution
  subst finalCursor
  exact ready

/-- Bound the original function's retained allocation by the cumulative fresh-array reservation.
Its source precondition retains actual handles and permits overlapping inputs. -/
theorem function_resources {w heapLimit : Nat} (positive : 0 < w)
    (count : Nat) (chunkValues : Array Nat) (initialValue : Payload)
    (copiesFit : initialValue.copies + count < 2 ^ w)
    (sizeFit : initialValue.values.size + count * chunkValues.size < 2 ^ w)
    (valuesFit : ∀ i (hi : i < initialValue.values.size), initialValue.values[i] < 2 ^ w)
    (chunkFit : ∀ i (hi : i < chunkValues.size), chunkValues[i] < 2 ^ w) :
    FunctionArenaResources ArrayRangeNative.Source.program
      (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
      (fun input : Buffer .nat × (Buffer .nat × Nat) =>
        ArrayRangeNative.Source.repeatAppend_args count input.1 input.2)
      (fun input heap => input.1.Contents heap chunkValues ∧
        state_representation.Rel initialValue input.2 heap)
      w heapLimit 2 (fun _ => reserve count initialValue.values.size chunkValues.size) := by
  intro input heap cursor observed arguments capacity finish value execution
  have countFits : count < 2 ^ w := arguments .here
  have chunkSizeFits : chunkValues.size < 2 ^ w := by
    rw [observed.1.size_eq]
    exact arguments (.there .here)
  have valid : invariant w heapLimit
      (mkModel (remaining := count) (state := initialValue) (initial := initialValue)
        (chunk := chunkValues) (count := count)) cursor :=
    ⟨countFits, copiesFit, sizeFit, chunkSizeFits, valuesFit, chunkFit, capacity⟩
  exact ⟨_, body_ready positive count chunkValues initialValue input.1 input.2 heap
    observed.1 observed.2 valid execution, Nat.le_refl _⟩

/-- Publish one complete invocation with the original mathematical contract,
the exact retained arena growth and the previously proved nonuniform time bound. -/
theorem execute {w heapLimit cursor : Nat} {placement : Nat → Ram.Word w}
    (count : Nat) (chunkValues : Array Nat) (initialValue : Payload)
    (chunk : Buffer .nat) (initial : Buffer .nat × Nat) {heap : Heap}
    (chunkObserved : chunk.Contents heap chunkValues)
    (initialObserved : state_representation.Rel initialValue initial heap)
    (copiesFit : initialValue.copies + count < 2 ^ w)
    (sizeFit : initialValue.values.size + count * chunkValues.size < 2 ^ w)
    (valuesFit : ∀ i (hi : i < initialValue.values.size), initialValue.values[i] < 2 ^ w)
    (chunkFit : ∀ i (hi : i < chunkValues.size), chunkValues[i] < 2 ^ w)
    {entry : Ram.Source.State w}
    (launch : FunctionArenaLaunch ArrayRangeNative.Source.program ArrayRangeNative.Source.repeatAppendId
      2 heapLimit placement (ArrayRangeNative.Source.repeatAppend_args count chunk initial)
      heap cursor entry)
    (capacity : cursor + reserve count initialValue.values.size chunkValues.size ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution ArrayRangeNative.Source.program
        ArrayRangeNative.Source.repeatAppendId 2 heapLimit placement
        (ArrayRangeNative.Source.repeatAppend_args count chunk initial) heap entry,
      outcome.cursor = cursor + reserve count initialValue.values.size chunkValues.size ∧
      (∃ output, state_representation.Rel output outcome.value outcome.heap ∧
        output.copies = initialValue.copies + count) ∧
      heap.ShapeExtends outcome.heap ∧
      outcome.bodySteps ≤ RepeatAppendCost.functionBodyBound count initialValue.values.size
        chunkValues.size ∧
      outcome.result.steps ≤ Ram.LocalCompiler.Function.callSteps
        (programControl ArrayRangeNative.Source.program)
        (lowerFunc ArrayRangeNative.Source.program ArrayRangeNative.Source.repeatAppendId)
        (RepeatAppendCost.functionBodyBound count initialValue.values.size chunkValues.size) + 1 := by
  have countFits : count < 2 ^ w := launch.arguments .here
  have chunkSizeFits : chunkValues.size < 2 ^ w := by
    rw [chunkObserved.size_eq]
    exact launch.arguments (.there .here)
  have valid : invariant w heapLimit
      (mkModel (remaining := count) (state := initialValue) (initial := initialValue)
        (chunk := chunkValues) (count := count)) cursor :=
    ⟨countFits, copiesFit, sizeFit, chunkSizeFits, valuesFit, chunkFit, capacity⟩
  have measured := function_measured launch.positive count chunkValues initialValue
    chunk initial heap chunkObserved initialObserved valid
  have bounded : StmtArenaCostBound ArrayRangeNative.Source.program w heapLimit 2
      (ArrayRangeNative.Source.program.body ArrayRangeNative.Source.repeatAppendId)
      ⟨ArrayRangeNative.Source.repeatAppend_args count chunk initial, heap⟩
      (RepeatAppendCost.functionCost count initialValue.values.size chunkValues.size).val :=
    (RepeatAppendCost.functionCost count initialValue.values.size chunkValues.size).property
      w heapLimit chunkValues initialValue chunk initial heap rfl rfl chunkObserved initialObserved
  simpa only [RepeatAppendCost.functionBodyBound] using
    measured.execute_le
      (P := fun _ _ finalCursor =>
        finalCursor = cursor + reserve count initialValue.values.size chunkValues.size)
      bounded (repeatAppend_copies count chunkValues initialValue) launch
      ⟨rfl, chunkObserved, initialObserved⟩

end Complexity.Language.Examples.LinkedList.NativeRange.RepeatAppendReady
