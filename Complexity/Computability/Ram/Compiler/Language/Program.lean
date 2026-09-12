/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Input
import Complexity.Computability.Ram.Compiler.Language.ArrayFunction

/-!
# RAM execution of mathematical input/output programs

`Complexity.Program` selects one fixed source function. `RamInput` supplies a
preloaded representation for its externally fixed mathematical input interface;
it is not part of a candidate program. The representation's range, rooting and
arena facts hold at every width admitted by the library's logarithmic policy.
The actual function's code, stack and subsequent allocation capacity are still
obligations of its execution, never premises that exclude mathematical inputs.

The runtime certificate uses the existing `FunctionArenaExecution` and counts
that same compiled program's actual instructions. Input size is an explicit
mathematical function fixed by the task, not necessarily a serialized length.
Output relations observe the actual returned value and final heap. No host
decoder executes an algorithm, and no second interpreter or cost model is added.
-/

namespace Complexity.Program

open Language
open Ram.LanguageCompiler

universe u v

/-- A fixed physical realization of a public input interface. Interface authors
must use raw structural data in `words`, not specification-dependent advice.
Registered interfaces and this metadata are fixed before choosing a candidate. -/
class RamInput (α : Type u) [Input α] where
  words : α → Array Nat
  placement : (x : α) → (w : Nat) → Nat → Ram.Word w
  entry : (x : α) → (w : Nat) → Ram.Source.State w
  cursor : α → Nat
  rooted : ∀ x : α, (Input.args x).Rooted (Input.heap x)
  fits : ∀ (x : α) w, 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (words x) ≤ w →
    EnvFits w (Input.args x)
  arena : ∀ (x : α) w, 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (words x) ≤ w →
    ArenaRep (placement x w) (cursor x)
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) (Input.heap x) (entry x w)

variable {α : Type u} {β : Type v} [Input α] [Output β] [RamInput α]

/-- One global width multiplier on the library's fixed input bit-length scale.
There is no candidate-chosen input-dependent width function. -/
def width (overhead : Nat) (x : α) : Nat :=
  Language.ArrayFunction.width overhead (RamInput.words x)

/-- The width policy always admits a machine for every mathematical input. -/
theorem exists_width (overhead : Nat) (x : α) : ∃ w, width overhead x ≤ w :=
  ⟨width overhead x, Nat.le_refl _⟩

/-- Every admitted width meets the fixed input representation's base condition. -/
theorem width_base {overhead w : Nat} {x : α} (admitted : width overhead x ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (RamInput.words x) ≤ w :=
  (Language.ArrayFunction.width_base overhead (RamInput.words x)).trans admitted

/-- Fixed input facts automatically supply the input side of a launch. Code and
stack capacity remain a proof about the selected implementation, not a task
precondition restricting the mathematical domain. -/
theorem launch (program : Complexity.Program α β) {x : α} {w depth : Nat}
    (base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (RamInput.words x) ≤ w)
    (capacity : FunctionCapacity program.source program.fn w depth
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) :
    FunctionArenaLaunch program.source program.fn depth
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) (RamInput.placement x w)
      (program.args x) (Input.heap x) (RamInput.cursor x) (RamInput.entry x w) := by
  refine ⟨capacity, ?_, ?_, RamInput.arena x w base⟩
  · have transport : ∀ {Γ : List Ty} (same : Input.params α = Γ),
        EnvFits w (cast (congrArg Env same) (Input.args x)) := by
      intro Γ same
      cases same
      exact RamInput.fits x w base
    intro τ v
    exact transport (congrArg Signature.params program.signature).symm v
  · have transport : ∀ {Γ : List Ty} (same : Input.params α = Γ),
        (cast (congrArg Env same) (Input.args x)).Rooted (Input.heap x) := by
      intro Γ same
      cases same
      exact RamInput.rooted x
    intro τ v
    exact transport (congrArg Signature.params program.signature).symm v

/-- The existing typed, allocation-aware execution of this selected function. -/
abbrev Execution (program : Complexity.Program α β) (x : α) (w depth : Nat) :=
  FunctionArenaExecution program.source program.fn depth
    (Ram.LanguageCompiler.ArrayFunction.heapLimit w) (RamInput.placement x w)
    (program.args x) (Input.heap x) (RamInput.entry x w)

/-- One instruction list, independent of the input, word width and specification. -/
def code (program : Complexity.Program α β) : Ram.Code :=
  lowerCode program.source program.fn

/-- The fixed function trampoline on the input interface's preloaded state. -/
def start (program : Complexity.Program α β) (x : α) (w : Nat) : Ram.State w :=
  Ram.LocalCompiler.Function.start (programControl program.source)
    (Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (envWords (RamInput.placement x w) (program.args x)) (RamInput.entry x w)

/-- Mathematical observation of this execution's actual returned value and heap.
This is not an executable output decoder or a choice of a desired answer. -/
def Execution.Represents {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) (output : β) : Prop :=
  program.resultRepresentation.Rel output execution.value execution.heap

/-- This published result is a halted execution of the very same compiled code. -/
theorem Execution.machine_exec {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) :
    Ram.Exec program.code execution.result.steps (program.start x w) execution.result.state ∧
      execution.result.state.status = .halted := by
  apply Ram.runUntil_halted_iff.mp
  have executed := execution.run_halted
  simp only [Ram.LocalCompiler.Function.runUntil, envWords_length, ↓reduceIte] at executed
  have compiled := compile_eq_some program.source program.fn
  simp only [Fin.getElem_fin] at compiled
  rw [compiled] at executed
  simpa only [Option.bind_some, code, start] using executed

/-- Independent source correctness identifies the output of this same run. -/
theorem Correct.post_of_execution {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} (correct : program.Correct valid post)
    {x : α} (legal : valid x) {w depth : Nat} (execution : program.Execution x w depth) :
    ∃ output, execution.Represents output ∧ post x output := by
  obtain ⟨output, returned, property⟩ := correct x legal
  exact ⟨output, returned.result_of_eval execution.source, property⟩

/-- Uniform worst-case time over a task's mathematical size measure. An envelope
bounds actual halted runs at every legal input and admitted width. `IsBigO` is
mathlib's ordinary asymptotic relation; finite input-size domains still need an
explicit unbounded family if the task is intended to distinguish asymptotics. -/
def TimeO (program : Complexity.Program α β) (valid : α → Prop)
    (size : α → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ∃ depth, ∃ execution : program.Execution x w depth,
        execution.result.steps ≤ bound (size x)

/-- The runtime obligation includes existence; it is not conditional on a
successful run or on a candidate-supplied capacity precondition. -/
theorem TimeO.runs {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth : Nat → Nat}
    (time : program.TimeO valid size growth)
    {x : α} (legal : valid x) : ∃ w depth, Nonempty (program.Execution x w depth) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  obtain ⟨depth, execution, bounded⟩ := runs x legal (width overhead x) (Nat.le_refl _)
  exact ⟨width overhead x, depth, ⟨execution⟩⟩

/-- Publish mathematical correctness and the independent instruction bound for
one actual run, without a per-problem heap or compiler connection theorem. -/
theorem TimeO.runs_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} {size : α → Nat} {growth : Nat → Nat}
    (time : program.TimeO valid size growth) (correct : program.Correct valid post) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
        (fun n => (growth n : ℝ)) ∧
      ∀ x, valid x → ∀ w, width overhead x ≤ w →
        ∃ depth, ∃ execution : program.Execution x w depth,
          (∃ output, execution.Represents output ∧ post x output) ∧
            execution.result.steps ≤ bound (size x) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs x legal w admitted
  exact ⟨depth, execution, correct.post_of_execution legal execution, bounded⟩

end Complexity.Program
