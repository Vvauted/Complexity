/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program
import Complexity.Computability.Ram.Execution.Space

/-!
# Physical-word space of mathematical input/output programs

The fixed preloaded input arena prefix, including metadata and any padding,
seeds the footprint. It conservatively counts reservation, not just live cells.
Actual heap accesses of the same complete compiled invocation extend this set.
Repeated or reclaimed addresses are counted once. Neither the address-space
capacity nor the highest stack address is the space count. This cumulative
physical footprint is not exact peak reachable-live storage. Registers, code,
I/O streams and extra host preprocessing storage/time are outside this
observation; the preloaded input arena itself is included.

`SpaceBound` requires an actual execution at one fixed width for every legal
input. `SpaceO` follows `TimeO`'s uniform width policy and mathlib asymptotics.
Capacity and word-fit obligations cannot filter the mathematical legal domain.
-/

namespace Complexity.Program

universe u v
variable {α : Type u} {β : Type v} [Input α] [Output β] [RamInput α]

/-- The fixed preloaded input arena reservation/prefix, including padding,
not the entire reserved machine capacity. -/
def inputSeed (x : α) (w : Nat) : Finset (Ram.Word w) :=
  Ram.initialSegment w (RamInput.cursor x)

/-- Actual input and accessed physical addresses of this same invocation. -/
def Execution.spaceFootprint {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) : Finset (Ram.Word w) :=
  Ram.spaceFootprint program.code execution.result.steps (program.start x w) (inputSeed x w)

/-- Distinct physical words, including the preloaded input arena prefix. -/
def Execution.spaceWords {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) : Nat := execution.spaceFootprint.card

/-- Every transition accesses at most one heap word. This general upper bound
counts the input reservation/prefix as well; it does not substitute time for a sharper
independent space proof. -/
theorem Execution.spaceWords_le_input_add_steps {program : Complexity.Program α β}
    {x : α} {w depth : Nat} (execution : program.Execution x w depth) :
    execution.spaceWords ≤ RamInput.cursor x + execution.result.steps := by
  exact (Ram.spaceWords_le_card_add_steps program.code execution.result.steps
    (program.start x w) (inputSeed x w)).trans
      (Nat.add_le_add_right (Ram.initialSegment_card_le w (RamInput.cursor x)) _)

/-- The physical observation is attached to an actual halted machine run. -/
theorem Execution.spaceBound {program : Complexity.Program α β} {x : α} {w depth : Nat}
    (execution : program.Execution x w depth) :
    Ram.SpaceBound program.code execution.result.steps (program.start x w)
      execution.result.state (inputSeed x w) execution.spaceWords :=
  ⟨execution.machine_exec.1, execution.machine_exec.2, Nat.le_refl _⟩

/-- Call-depth proof witnesses do not select a different runtime result. -/
theorem Execution.result_eq {program : Complexity.Program α β} {x : α} {w d e : Nat}
    (left : program.Execution x w d) (right : program.Execution x w e) :
    left.result = right.result :=
  Option.some.inj (left.run.symm.trans right.run)

/-- Different certificates for the same invocation observe the same space. -/
theorem Execution.spaceWords_eq {program : Complexity.Program α β} {x : α} {w d e : Nat}
    (left : program.Execution x w d) (right : program.Execution x w e) :
    left.spaceWords = right.spaceWords := by
  unfold Execution.spaceWords Execution.spaceFootprint
  rw [left.result_eq right]

/-- A finite physical-word budget at an author-fixed width. Width admission
and existence of a successful same-program run are obligations at every legal
input, not hypotheses used to exclude inputs from the specification. -/
def SpaceBound (program : Complexity.Program α β) (valid : α → Prop)
    (wordWidth : Nat) (budget : α → Nat) : Prop :=
  ∀ x, valid x → ∃ admitted : width 0 x ≤ wordWidth,
    ∃ depth, ∃ execution : program.Execution x wordWidth depth,
      execution.spaceWords ≤ budget x

/-- Uniform worst-case physical-word space, including preloaded input reservation. -/
def SpaceO (program : Complexity.Program α β) (valid : α → Prop)
    (size : α → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ∃ depth, ∃ execution : program.Execution x w depth,
        execution.spaceWords ≤ bound (size x)

/-- A possibly multivariate space target on the mathematical input. -/
abbrev SpaceOOn (program : Complexity.Program α β) (valid : α → Prop)
    (growth : α → Nat) : Prop := program.SpaceO valid growth id

/-- Restrict legal inputs and increase a fixed finite space budget. -/
theorem SpaceBound.mono {program : Complexity.Program α β}
    {valid valid' : α → Prop} {w : Nat} {budget budget' : α → Nat}
    (space : program.SpaceBound valid w budget)
    (inputs : ∀ x, valid' x → valid x)
    (budgets : ∀ x, valid' x → budget x ≤ budget' x) :
    program.SpaceBound valid' w budget' := by
  intro x legal
  obtain ⟨admitted, depth, execution, bounded⟩ := space x (inputs x legal)
  exact ⟨admitted, depth, execution, bounded.trans (budgets x legal)⟩

/-- Reuse a finite bound on a subtask without changing the execution. -/
theorem SpaceBound.mono_valid {program : Complexity.Program α β}
    {valid valid' : α → Prop} {w : Nat} {budget : α → Nat}
    (space : program.SpaceBound valid w budget)
    (inputs : ∀ x, valid' x → valid x) : program.SpaceBound valid' w budget :=
  space.mono inputs (fun _ _ => Nat.le_refl _)

/-- Every finite-budget legal instance has an actual successful execution. -/
theorem SpaceBound.runs {program : Complexity.Program α β}
    {valid : α → Prop} {w : Nat} {budget : α → Nat}
    (space : program.SpaceBound valid w budget) {x : α} (legal : valid x) :
    ∃ depth, Nonempty (program.Execution x w depth) := by
  obtain ⟨_, depth, execution, _⟩ := space x legal
  exact ⟨depth, ⟨execution⟩⟩

/-- Independent correctness observes this finite-budget execution's output. -/
theorem SpaceBound.runs_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} {w : Nat} {budget : α → Nat}
    (space : program.SpaceBound valid w budget) (correct : program.Correct valid post) :
    ∀ x, valid x → ∃ admitted : width 0 x ≤ w,
      ∃ depth, ∃ execution : program.Execution x w depth,
        (∃ output, execution.Represents output ∧ post x output) ∧
          execution.spaceWords ≤ budget x := by
  intro x legal
  obtain ⟨admitted, depth, execution, bounded⟩ := space x legal
  exact ⟨admitted, depth, execution, correct.post_of_execution legal execution, bounded⟩

/-- Restrict the input domain and weaken an asymptotic space target. -/
theorem SpaceO.mono {program : Complexity.Program α β}
    {valid valid' : α → Prop} {size : α → Nat} {growth growth' : Nat → Nat}
    (space : program.SpaceO valid size growth)
    (inputs : ∀ x, valid' x → valid x)
    (growthBound : Asymptotics.IsBigO Filter.atTop
      (fun n => (growth n : ℝ)) (fun n => (growth' n : ℝ))) :
    program.SpaceO valid' size growth' := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  exact ⟨overhead, bound, asymptotic.trans growthBound,
    fun x legal => runs x (inputs x legal)⟩

/-- Reuse a uniform space certificate on a mathematical subtask. -/
theorem SpaceO.mono_valid {program : Complexity.Program α β}
    {valid valid' : α → Prop} {size : α → Nat} {growth : Nat → Nat}
    (space : program.SpaceO valid size growth)
    (inputs : ∀ x, valid' x → valid x) : program.SpaceO valid' size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  exact ⟨overhead, bound, asymptotic, fun x legal => runs x (inputs x legal)⟩

/-- Publish an independently bounded family of actual same-program runs. -/
theorem SpaceO.of_runs {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth bound : Nat → Nat} {overhead : Nat}
    (runs : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ∃ depth, ∃ execution : program.Execution x w depth,
        execution.spaceWords ≤ bound (size x))
    (asymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    program.SpaceO valid size growth := ⟨overhead, bound, asymptotic, runs⟩

/-- A space certificate includes termination, not merely a conditional count. -/
theorem SpaceO.runs {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth : Nat → Nat}
    (space : program.SpaceO valid size growth) {x : α} (legal : valid x) :
    ∃ w depth, Nonempty (program.Execution x w depth) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨depth, execution, _⟩ := runs x legal (width overhead x) (Nat.le_refl _)
  exact ⟨width overhead x, depth, ⟨execution⟩⟩

/-- The independent mathematical postcondition and the space envelope hold
for one actual run at every admitted width. -/
theorem SpaceO.runs_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} {size : α → Nat} {growth : Nat → Nat}
    (space : program.SpaceO valid size growth) (correct : program.Correct valid post) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
        (fun n => (growth n : ℝ)) ∧
      ∀ x, valid x → ∀ w, width overhead x ≤ w →
        ∃ depth, ∃ execution : program.Execution x w depth,
          (∃ output, execution.Represents output ∧ post x output) ∧
            execution.spaceWords ≤ bound (size x) := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs x legal w admitted
  exact ⟨depth, execution, correct.post_of_execution legal execution, bounded⟩

end Complexity.Program
