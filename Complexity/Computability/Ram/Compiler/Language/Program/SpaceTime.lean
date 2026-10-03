/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Space

/-!
# Time and physical space of the same program execution

Independent uniform time and space certificates may use different global width
constants and call-depth witnesses. Their maximum width policy admits both.
Determinism of the existing runner identifies their complete runtime results,
so the published execution satisfies both bounds, not just one of two unrelated
existence statements. Source correctness can observe that same returned heap.
-/

namespace Complexity.Program

universe u v
variable {α : Type u} {β : Type v} [Input α] [Output β] [RamInput α]

/-- Increase the global width overhead without choosing an input-dependent
width policy or changing the fixed physical input presentation. -/
theorem width_mono_overhead {left right : Nat} (overheads : left ≤ right) (x : α) :
    width left x ≤ width right x := by
  change (left + 1) * _ ≤ (right + 1) * _
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right overheads 1)

/-- Uniform time and physical-space envelopes hold for a single actual run.
Their size measures and asymptotic targets may be different. -/
theorem TimeO.runs_space {program : Complexity.Program α β}
    {valid : α → Prop} {timeSize spaceSize : α → Nat} {timeGrowth spaceGrowth : Nat → Nat}
    (time : program.TimeO valid timeSize timeGrowth)
    (space : program.SpaceO valid spaceSize spaceGrowth) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
        (fun n => (timeGrowth n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
        (fun n => (spaceGrowth n : ℝ)) ∧
      ∀ x, valid x → ∀ w, width overhead x ≤ w →
        ∃ depth, ∃ execution : program.Execution x w depth,
          execution.result.steps ≤ timeBound (timeSize x) ∧
            execution.spaceWords ≤ spaceBound (spaceSize x) := by
  obtain ⟨timeOverhead, timeBound, timeAsymptotic, timeRuns⟩ := time
  obtain ⟨spaceOverhead, spaceBound, spaceAsymptotic, spaceRuns⟩ := space
  refine ⟨max timeOverhead spaceOverhead, timeBound, spaceBound,
    timeAsymptotic, spaceAsymptotic, ?_⟩
  intro x legal w admitted
  obtain ⟨depth, execution, timeBounded⟩ := timeRuns x legal w
    ((width_mono_overhead (Nat.le_max_left _ _) x).trans admitted)
  obtain ⟨otherDepth, other, spaceBounded⟩ := spaceRuns x legal w
    ((width_mono_overhead (Nat.le_max_right _ _) x).trans admitted)
  refine ⟨depth, execution, timeBounded, ?_⟩
  rw [execution.spaceWords_eq other]
  exact spaceBounded

/-- Mathematical correctness, time and physical space describe one execution
and its actual returned value/final heap. -/
theorem TimeO.runs_space_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop}
    {timeSize spaceSize : α → Nat} {timeGrowth spaceGrowth : Nat → Nat}
    (time : program.TimeO valid timeSize timeGrowth)
    (space : program.SpaceO valid spaceSize spaceGrowth)
    (correct : program.Correct valid post) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
        (fun n => (timeGrowth n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
        (fun n => (spaceGrowth n : ℝ)) ∧
      ∀ x, valid x → ∀ w, width overhead x ≤ w →
        ∃ depth, ∃ execution : program.Execution x w depth,
          (∃ output, execution.Represents output ∧ post x output) ∧
          execution.result.steps ≤ timeBound (timeSize x) ∧
            execution.spaceWords ≤ spaceBound (spaceSize x) := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ :=
    time.runs_space space
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro x legal w admitted
  obtain ⟨depth, execution, timeBounded, spaceBounded⟩ := runs x legal w admitted
  exact ⟨depth, execution, correct.post_of_execution legal execution, timeBounded, spaceBounded⟩

/-- Given an independent instruction bound on every completed run, a fixed
finite space certificate supplies one execution satisfying both finite caps. -/
theorem SpaceBound.runs_time {program : Complexity.Program α β}
    {valid : α → Prop} {w : Nat} {spaceBudget timeBudget : α → Nat}
    (space : program.SpaceBound valid w spaceBudget)
    (time : ∀ x, valid x → ∀ depth, ∀ execution : program.Execution x w depth,
      execution.result.steps ≤ timeBudget x) :
    ∀ x, valid x → ∃ admitted : width 0 x ≤ w,
      ∃ depth, ∃ execution : program.Execution x w depth,
        execution.result.steps ≤ timeBudget x ∧ execution.spaceWords ≤ spaceBudget x := by
  intro x legal
  obtain ⟨admitted, depth, execution, bounded⟩ := space x legal
  exact ⟨admitted, depth, execution, time x legal depth execution, bounded⟩

/-- A uniform time bound gives a conservative physical-space bound when the
preloaded input reservation/prefix is independently bounded in the same asymptotic class.
No capacity interval or free input-size assumption is used as the count. -/
theorem SpaceO.of_time {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth inputBound : Nat → Nat}
    (time : program.TimeO valid size growth)
    (input : ∀ x, valid x → RamInput.cursor x ≤ inputBound (size x))
    (inputAsymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => (inputBound n : ℝ)) (fun n => (growth n : ℝ))) :
    program.SpaceO valid size growth := by
  obtain ⟨overhead, timeBound, asymptotic, runs⟩ := time
  refine ⟨overhead, fun n => inputBound n + timeBound n, ?_, ?_⟩
  · simpa only [Nat.cast_add] using inputAsymptotic.add asymptotic
  · intro x legal w admitted
    obtain ⟨depth, execution, bounded⟩ := runs x legal w admitted
    exact ⟨depth, execution, execution.spaceWords_le_input_add_steps.trans
      (Nat.add_le_add (input x legal) bounded)⟩

end Complexity.Program
