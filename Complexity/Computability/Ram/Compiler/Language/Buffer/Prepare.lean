/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prepare
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Computability.Ram.Compiler.Language.Buffer.Replicate

/-!
# Counted preparation of current natural arrays

The existing initialized allocation and actual scalar-write entry are invoked
in retained RAM memory. Each outcome supplies the next complete state; no
mathematical array is silently installed in memory. The final buffer observes
the original external array while all old objects and placements survive.

Costs include initialization, every write, and the real invocation wrappers.
External array traversal, scalar-port loading, transport and a continuous driver
are separate from this sum of preloaded invocations.
-/

namespace Ram.LanguageCompiler.Buffer.Prepare

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.Prepare

variable {w heapLimit : Nat}

/-- The compiler-derived complete invocation count for initialized allocation. -/
def allocationSteps (length : Nat) : Nat :=
  LocalCompiler.Function.callSteps (programControl Replicate.program)
    (lowerFunc Replicate.program Replicate.replicateNatId)
    (14 * length + 18 + (2 * fieldCount (.buffer .nat) + 2) + 2) + 1

/-- The compiler-derived count for a scalar write and unit return. -/
def writeSteps : Nat :=
  LocalCompiler.Function.callSteps (programControl writeProgram)
    (lowerFunc writeProgram writeEntry)
    (writeCodeSize + 2 + (2 * fieldCount .unit + 2) + 2) + 1

/-- The actual initialized-allocation count is affine in the array extent. -/
theorem allocationSteps_linear (length : Nat) :
    allocationSteps length = 14 * length + allocationSteps 0 := by
  simp only [allocationSteps, LocalCompiler.Function.callSteps]
  omega

private theorem allocate (length : Nat) (current : Session.State w heapLimit)
    (capacity : FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (lengthFits : length < 2 ^ w) (space : current.cursor + length ≤ heapLimit) :
    ∃ outcome : FunctionArenaExecution Replicate.program Replicate.replicateNatId 0 heapLimit
        current.placement (Replicate.replicateNat_args length 0) current.heap current.entry,
      outcome.value = (current.heap.alloc (τ := .nat) length 0).1 ∧
      outcome.heap = (current.heap.alloc (τ := .nat) length 0).2 ∧
      outcome.cursor = current.cursor + length ∧ outcome.result.steps = allocationSteps length := by
  let arguments := Replicate.replicateNat_args length 0
  let allocated := current.heap.alloc (τ := .nat) length 0
  let next : Complexity.Language.State [.buffer .nat, .nat, .nat] :=
    Complexity.Language.State.cons allocated.1 ⟨arguments, allocated.2⟩
  have executed : Complexity.Language.Exec Replicate.program
      (Replicate.program.body Replicate.replicateNatId)
      ⟨arguments, current.heap⟩ ⟨arguments, allocated.2⟩ (.returned allocated.1) :=
    .alloc (kind := .nat) (length := (.var .here : Atom [.nat, .nat] .nat))
      (initial := .var (.there .here)) (continuation := .ret (.var .here))
      (entry := ⟨arguments, current.heap⟩) (finish := next) (.ret (.var .here) next)
  let ready : ArenaReady executed w heapLimit 0 current.cursor (current.cursor + length) :=
    .alloc (kind := .nat) (length := (.var .here : Atom [.nat, .nat] .nat))
      (initial := .var (.there .here)) (continuation := .ret (.var .here))
      (entry := ⟨arguments, current.heap⟩) (finish := next)
      (Nat.two_pow_pos w) space (.ret (.var .here) next lengthFits)
  have cost : ArenaExecutionCost ready (14 * length + 18 + (2 * fieldCount (.buffer .nat) + 2)) :=
    .alloc (kind := .nat) (length := (.var .here : Atom [.nat, .nat] .nat))
      (initial := .var (.there .here)) (continuation := .ret (.var .here))
      (entry := ⟨arguments, current.heap⟩) (finish := next)
      (initialFits := Nat.two_pow_pos w) (capacity := space)
      (.ret (.var .here) next (fits := lengthFits))
  have fits : EnvFits w arguments :=
    EnvFits.cons (τ := .nat)
      (EnvFits.cons (τ := .nat) (EnvFits.empty w) 0 (Nat.two_pow_pos w)) length lengthFits
  have rooted : arguments.Rooted current.heap :=
    Env.Rooted.cons (τ := .nat)
      (Env.Rooted.cons (τ := .nat) (Env.Rooted.empty _) 0 trivial) length trivial
  let launch : FunctionArenaLaunch Replicate.program Replicate.replicateNatId 0 heapLimit
      current.placement arguments current.heap current.cursor current.entry :=
    ⟨capacity, fits, rooted, current.arena⟩
  obtain ⟨outcome, returned, heap, cursor, count⟩ := cost.execute launch
  refine ⟨outcome, returned, heap, cursor, ?_⟩
  rw [outcome.steps_eq, count]
  rfl

private theorem write (buffer : Buffer .nat) (index value : Nat)
    (current : Session.State w heapLimit) (finish : Heap)
    (capacity : FunctionCapacity writeProgram writeEntry w 0 heapLimit)
    (rooted : buffer.Rooted current.heap)
    (bufferFits : buffer.length < 2 ^ w) (indexFits : index < 2 ^ w)
    (valueFits : value < 2 ^ w)
    (written : current.heap.write buffer index value = .ok finish) :
    ∃ outcome : FunctionArenaExecution writeProgram writeEntry 0 heapLimit
        current.placement (writeArgs buffer index value) current.heap current.entry,
      outcome.heap = finish ∧ outcome.cursor = current.cursor ∧
        outcome.result.steps = writeSteps := by
  let arguments := writeArgs buffer index value
  let next : Complexity.Language.State writeSignature.params := ⟨arguments, finish⟩
  let executed := write_exec written
  let ready : ArenaReady executed w heapLimit 0 current.cursor current.cursor :=
    .seqNormal (.write (written := written) bufferFits indexFits valueFits)
      (.ret .unit next trivial)
  have cost : ArenaExecutionCost ready (writeCodeSize + 2 + (2 * fieldCount .unit + 2)) :=
    .seqNormal (.write (kind := .nat)
      (buffer := (.var .here : Atom writeSignature.params (.buffer .nat)))
      (index := .var (.there .here)) (value := .var (.there (.there .here)))
      (entry := ⟨arguments, current.heap⟩) (written := written) (bufferFits := bufferFits)
      (indexFits := indexFits) (valueFits := valueFits)) (.ret .unit next (fits := trivial))
  have fits : EnvFits w arguments :=
    EnvFits.cons (τ := .buffer .nat)
      (EnvFits.cons (τ := .nat)
        (EnvFits.cons (τ := .nat) (EnvFits.empty w) value valueFits) index indexFits)
      buffer bufferFits
  have argumentsRooted : arguments.Rooted current.heap :=
    Env.Rooted.cons (τ := .buffer .nat)
      (Env.Rooted.cons (τ := .nat)
        (Env.Rooted.cons (τ := .nat) (Env.Rooted.empty _) value trivial) index trivial)
      buffer rooted
  let launch : FunctionArenaLaunch writeProgram writeEntry 0 heapLimit
      current.placement arguments current.heap current.cursor current.entry :=
    ⟨capacity, fits, argumentsRooted, current.arena⟩
  obtain ⟨outcome, _, heap, cursor, count⟩ := cost.execute launch
  refine ⟨outcome, heap, cursor, ?_⟩
  rw [outcome.steps_eq, count]
  rfl

/-- Fill the first count cells through actual scalar-write invocations.
Complete memory is threaded through every call. -/
inductive Fill (values : Array Nat) (buffer : Buffer .nat) :
    Nat → Session.State w heapLimit → Session.State w heapLimit → Nat → Prop
  | zero (current) : Fill values buffer 0 current current 0
  | succ {count current middle steps}
      (rest : Fill values buffer count current middle steps)
      (bound : count < values.size)
      (outcome : FunctionArenaExecution writeProgram writeEntry 0 heapLimit
        middle.placement (writeArgs buffer count values[count]) middle.heap middle.entry) :
      Fill values buffer (count + 1) current (Session.State.ofExecution outcome)
        (steps + outcome.result.steps)

/-- Erase actual write invocations to their identical source writes. -/
theorem Fill.source {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    (run : Fill values buffer count current finish steps) :
    Complexity.Language.Buffer.Prepare.Fill values buffer count current.heap finish.heap := by
  induction run with
  | zero => exact .zero _
  | succ rest bound outcome ih =>
      apply Complexity.Language.Buffer.Prepare.Fill.succ ih bound
      apply write_eval_iff.mp
      have returned : outcome.value = () := by
        change (outcome.value : Unit) = ()
        exact Subsingleton.elim (α := Unit) _ _
      simpa only [returned] using outcome.source

/-- Each write keeps the previous placement; composition uses the actual
source shape frame, not a reconstruction of retained state. -/
theorem Fill.agreement {values : Array Nat} {buffer : Buffer .nat}
    {count steps : Nat} {current finish : Session.State w heapLimit}
    (run : Fill values buffer count current finish steps) :
    Placement.Agrees current.heap current.placement finish.placement := by
  induction run with
  | zero => exact Placement.Agrees.refl _ _
  | succ rest bound outcome ih =>
      exact ih.trans_of_shape outcome.agreement rest.source.shape

private theorem Fill.exists_run (values : Array Nat) (buffer : Buffer .nat)
    (count : Nat) (before : count ≤ values.size) (current : Session.State w heapLimit)
    (valid : buffer.Valid current.heap) (size : buffer.length = values.size)
    (capacity : FunctionCapacity writeProgram writeEntry w 0 heapLimit)
    (lengthFits : buffer.length < 2 ^ w)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w) :
    ∃ finish steps, Fill values buffer count current finish steps ∧
      finish.cursor = current.cursor ∧ steps = count * writeSteps := by
  induction count with
  | zero => exact ⟨current, 0, .zero _, rfl, by simp⟩
  | succ count ih =>
      obtain ⟨middle, steps, rest, cursor, countEq⟩ := ih (by omega)
      have nextValid := valid.mono rest.source.shape
      obtain ⟨contents, observed⟩ := nextValid.contents
      have bound : count < values.size := by omega
      obtain ⟨heap, written, _⟩ := observed.write_exists
        (index := count) (by rw [observed.size_eq, size]; exact bound) values[count]
      obtain ⟨outcome, heapEq, cursorEq, stepsEq⟩ :=
        write buffer count values[count] middle heap capacity nextValid.rooted lengthFits
          (by omega) (fits count bound) written
      refine ⟨Session.State.ofExecution outcome, steps + outcome.result.steps,
        .succ rest bound outcome, cursorEq.trans cursor, ?_⟩
      rw [countEq, stepsEq, Nat.add_mul, Nat.one_mul]

/-- A fresh initialized array followed by its real in-place scalar writes. -/
inductive Run (values : Array Nat) : Session.State w heapLimit →
    Buffer .nat → Session.State w heapLimit → Nat → Prop
  | intro (current : Session.State w heapLimit)
      (allocated : FunctionArenaExecution Replicate.program Replicate.replicateNatId 0 heapLimit
        current.placement (Replicate.replicateNat_args values.size 0) current.heap current.entry)
      {finish steps}
      (filled : Fill values allocated.value values.size (Session.State.ofExecution allocated)
        finish steps) :
      Run values current allocated.value finish (allocated.result.steps + steps)

/-- Preserve source preparation of the same current array and final heap. -/
theorem Run.source {values : Array Nat} {current finish : Session.State w heapLimit}
    {buffer : Buffer .nat} {steps : Nat} (run : Run values current buffer finish steps) :
    Complexity.Language.Buffer.Prepare.Run values current.heap buffer finish.heap := by
  cases run with
  | intro allocated filled =>
      exact ⟨allocated.heap, allocated.source, filled.source⟩

/-- The real preparation retains both exact old source objects and their
machine placement while exposing the original ordinary array. -/
theorem Run.observed {values : Array Nat} {current finish : Session.State w heapLimit}
    {buffer : Buffer .nat} {steps : Nat} (run : Run values current buffer finish steps) :
    buffer.Contents finish.heap values ∧
      _root_.List.IsPrefix current.heap.objects.toList finish.heap.objects.toList ∧
      current.heap.ShapeExtends finish.heap ∧
      Placement.Agrees current.heap current.placement finish.placement := by
  have observed := run.source.observed
  refine ⟨observed.1, observed.2.2.2.2.1, observed.2.2.2.2.2, ?_⟩
  cases run with
  | intro allocated filled =>
      have shape : current.heap.ShapeExtends allocated.heap := by
        have called := allocated.source
        rw [Replicate.replicateNat_observe, Replicate.replicateNat_eval] at called
        have same : allocated.heap = (current.heap.alloc (τ := .nat) values.size 0).2 :=
          (congrArg Prod.snd (Part.some_injective called)).symm
        rw [same]
        exact current.heap.shapeExtends_alloc _ _
      exact allocated.agreement.trans_of_shape filled.agreement shape

/-- Actual realization from ordinary cell ranges and enough fresh array cells.
The count is linear and includes the initialized allocation and every call. -/
theorem exists_le (values : Array Nat) (current : Session.State w heapLimit)
    (allocationCapacity :
      FunctionCapacity Replicate.program Replicate.replicateNatId w 0 heapLimit)
    (writeCapacity : FunctionCapacity writeProgram writeEntry w 0 heapLimit)
    (fits : ∀ index (bound : index < values.size), values[index] < 2 ^ w)
    (space : current.cursor + values.size ≤ heapLimit) :
    ∃ buffer finish steps, Run values current buffer finish steps ∧
      buffer.Contents finish.heap values ∧ finish.cursor = current.cursor + values.size ∧
      steps = allocationSteps values.size + values.size * writeSteps := by
  have lengthFits : values.size < 2 ^ w := by
    have := current.arena.limit_lt
    omega
  obtain ⟨allocated, bufferEq, heapEq, cursorEq, stepsEq⟩ :=
    allocate values.size current allocationCapacity lengthFits space
  have valid : allocated.value.Valid allocated.heap := by
    rw [bufferEq, heapEq]
    exact current.heap.alloc_valid _ _
  have lengthEq : allocated.value.length = values.size := by rw [bufferEq]; rfl
  obtain ⟨finish, steps, filled, finalCursor, count⟩ :=
    Fill.exists_run values allocated.value values.size (Nat.le_refl _)
      (Session.State.ofExecution allocated) valid lengthEq writeCapacity (by omega) fits
  have run := Run.intro current allocated filled
  exact ⟨allocated.value, finish, allocated.result.steps + steps, run,
    run.source.observed.1, finalCursor.trans cursorEq, by rw [stepsEq, count]⟩

end Ram.LanguageCompiler.Buffer.Prepare
