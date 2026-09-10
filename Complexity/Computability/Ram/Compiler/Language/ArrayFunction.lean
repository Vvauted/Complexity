/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ArrayFunction.Input
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Mathematical array tasks with actual RAM complexity

The source `ArrayFunction.Correct` statement and `ArrayFunction.TimeO` refer to
one fixed source function. Inputs use the library's fixed single-array arena
layout. An execution is the existing `FunctionArenaExecution`, including real
halt, source evaluation, returned words, final arena and code/stack capacity.

`TimeO` requires such an execution for every legal input and every sufficiently
large word width. The only implementation-dependent width adjustment is one
constant multiplier, uniform in the input; the library fixes the logarithmic input-width
term. Capacity is evidence inside each execution, never a condition that can
be made false to discard inputs. One size-bound function covers all those
actual instruction counts, and mathlib supplies its asymptotic relation.
The smallest admitted width remains a fixed multiple of the input bit-length
scale and permits polynomially many addresses. A candidate cannot replace that
rule with an arbitrary input-dependent width or an empty legality predicate.

This is a preloaded invocation track: input preparation and host scheduling are
outside its boundary. Costs include the real call/return/halt instructions and
all executed allocation or scratch reclamation. They are word-RAM costs, not
bit complexity. No source interpreter or alternative cost model is defined.
-/

namespace Complexity.Language.ArrayFunction

open Ram.LanguageCompiler

/-- The existing allocation-aware execution at the library's fixed array input.
The source function, input layout and emitted code cannot vary with word width. -/
abbrev Execution (f : ArrayFunction) (xs : Array Nat) (w depth : Nat) :=
  FunctionArenaExecution f.program f.fn depth
    (Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (Ram.LanguageCompiler.ArrayFunction.placement w)
    (f.args xs) (inputHeap xs) (Ram.LanguageCompiler.ArrayFunction.entry w xs)

/-- The shared input representation supplies range, rooting and arena facts at
the selected signature. Only the actual compiled function's capacity remains
to be established; it is not used to restrict the task's input domain. -/
theorem launch (f : ArrayFunction) {xs : Array Nat} {w depth : Nat}
    (width : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth xs ≤ w)
    (capacity : FunctionCapacity f.program f.fn w depth
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) :
    FunctionArenaLaunch f.program f.fn depth (Ram.LanguageCompiler.ArrayFunction.heapLimit w)
      (Ram.LanguageCompiler.ArrayFunction.placement w) (f.args xs) (inputHeap xs)
      (Ram.LanguageCompiler.ArrayFunction.cursor xs)
      (Ram.LanguageCompiler.ArrayFunction.entry w xs) := by
  refine ⟨capacity, ?_, ?_, Ram.LanguageCompiler.ArrayFunction.input_arenaRep width⟩
  · have transport : ∀ {Γ : List Ty} (same : [.buffer .nat] = Γ),
        EnvFits w (cast (congrArg Env same) (inputArgs xs)) := by
      rintro Γ rfl
      exact Ram.LanguageCompiler.ArrayFunction.inputArgs_fits width
    intro τ v
    exact transport f.parameterTypes.symm v
  · have transport : ∀ {Γ : List Ty} (same : [.buffer .nat] = Γ),
        (cast (congrArg Env same) (inputArgs xs)).Rooted (inputHeap xs) := by
      rintro Γ rfl
      exact Ram.LanguageCompiler.ArrayFunction.inputArgs_rooted xs
    intro τ v
    exact transport f.parameterTypes.symm v

/-- The mathematical result of the actual typed execution; only the declared
result-type equality is transported, with no specification-based decoding. -/
def Execution.output {f : ArrayFunction} {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) : Nat :=
  f.resultEquiv execution.value

/-- The emitted instruction list is fixed before choosing an input or word width. -/
def code (f : ArrayFunction) : Ram.Code := lowerCode f.program f.fn

/-- The existing function trampoline starts on the fixed, preloaded array arena. -/
def start (f : ArrayFunction) (xs : Array Nat) (w : Nat) : Ram.State w :=
  Ram.LocalCompiler.Function.start (programControl f.program)
    (Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (envWords (Ram.LanguageCompiler.ArrayFunction.placement w) (f.args xs))
    (Ram.LanguageCompiler.ArrayFunction.entry w xs)

/-- A published array execution is a halted run of that exact fixed code, with
its reported number of real RAM transitions and its actual final machine state. -/
theorem Execution.machine_exec {f : ArrayFunction} {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) :
    Ram.Exec f.code execution.result.steps (f.start xs w) execution.result.state ∧
      execution.result.state.status = .halted := by
  apply Ram.runUntil_halted_iff.mp
  have executed := execution.run_halted
  simp only [Ram.LocalCompiler.Function.runUntil, envWords_length, ↓reduceIte] at executed
  have compiled := compile_eq_some f.program f.fn
  simp only [Fin.getElem_fin] at compiled
  rw [compiled] at executed
  simpa only [Option.bind_some, code, start] using executed

/-- The minimal width allowed by a uniform implementation constant. Its fixed
logarithmic input scale permits polynomial addressing without a candidate-chosen
input-dependent width function. -/
def width (overhead : Nat) (xs : Array Nat) : Nat :=
  (overhead + 1) * (Ram.LanguageCompiler.ArrayFunction.inputWordWidth xs + 1)

/-- Even the zero-overhead policy supplies the extra bit used by the fixed
initial arena representation. -/
theorem width_base (overhead : Nat) (xs : Array Nat) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth xs ≤ width overhead xs := by
  simpa only [width, Nat.add_comm 1] using
    (Nat.le_mul_of_pos_left (Ram.LanguageCompiler.ArrayFunction.inputWordWidth xs + 1)
      (Nat.succ_pos overhead))

/-- Every mathematical input has an admitted width for every fixed overhead.
The quantified machine domain therefore cannot be emptied by that overhead. -/
theorem exists_width (overhead : Nat) (xs : Array Nat) :
    ∃ w, width overhead xs ≤ w :=
  ⟨width overhead xs, Nat.le_refl _⟩

/-- Larger machine widths remain in the same fixed input domain. -/
theorem width_mono {overhead w w' : Nat} {xs : Array Nat}
    (admitted : width overhead xs ≤ w) (larger : w ≤ w') :
    width overhead xs ≤ w' := admitted.trans larger

/-- A size envelope for actual halted executions of the one compiled source
function. The constant overhead is uniform over every input and width; the
asymptotic bound is mathlib's ordinary `IsBigO` of the supplied size envelope. -/
def TimeO (f : ArrayFunction) (valid : Array Nat → Prop) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ xs, valid xs → ∀ w, width overhead xs ≤ w →
      ∃ depth, ∃ execution : f.Execution xs w depth,
        execution.result.steps ≤ bound xs.size

/-- A separately stated source specification identifies the actual RAM result
without another simulation proof or an independently selected result witness. -/
theorem Correct.output_eq {f : ArrayFunction} {valid : Array Nat → Prop}
    {answer : Array Nat → Nat} (correct : f.Correct valid answer)
    {xs : Array Nat} (legal : valid xs) {w depth : Nat}
    (execution : f.Execution xs w depth) : Execution.output execution = answer xs :=
  (correct xs legal).result_eq execution.source

/-- The runtime requirement supplies an actual machine execution on every legal
mathematical input, not merely a bound conditional on an execution existing. -/
theorem TimeO.runs {f : ArrayFunction} {valid : Array Nat → Prop} {growth : Nat → Nat}
    (time : f.TimeO valid growth) {xs : Array Nat} (legal : valid xs) :
    ∃ w depth, Nonempty (f.Execution xs w depth) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨depth, execution, bounded⟩ := runs xs legal (width overhead xs) (Nat.le_refl _)
  exact ⟨width overhead xs, depth, ⟨execution⟩⟩

/-- A runtime certificate already entails successful source evaluation at each
legal input. Functional correctness still supplies the independent answer. -/
theorem TimeO.source_total {f : ArrayFunction} {valid : Array Nat → Prop}
    {growth : Nat → Nat} (time : f.TimeO valid growth)
    {xs : Array Nat} (legal : valid xs) : ∃ result, f.Returns xs result := by
  obtain ⟨w, depth, ⟨execution⟩⟩ := time.runs legal
  refine ⟨Execution.output execution, execution.heap, ?_⟩
  simpa only [Execution.output, Equiv.symm_apply_apply] using execution.source

/-- Combine the two task obligations against the same actual outcome and its
uniform instruction bound. Source correctness acquires no width or budget
premise; it is only applied to the already recorded source evaluation. -/
theorem TimeO.runs_correct {f : ArrayFunction} {valid : Array Nat → Prop}
    {answer : Array Nat → Nat} {growth : Nat → Nat}
    (time : f.TimeO valid growth) (correct : f.Correct valid answer) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
        (fun n => (growth n : ℝ)) ∧
      ∀ xs, valid xs → ∀ w, width overhead xs ≤ w →
        ∃ depth, ∃ execution : f.Execution xs w depth,
          Execution.output execution = answer xs ∧ execution.result.steps ≤ bound xs.size := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro xs legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs xs legal w admitted
  exact ⟨depth, execution, correct.output_eq legal execution, bounded⟩

end Complexity.Language.ArrayFunction
