/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceTime

/-!
# Joint resources with time-derived word width

The declared mathematical time target fixes the logarithmic word-width scale,
together with the raw input representation. A single global multiplier admits
every sufficiently wide machine; neither a candidate-selected width function,
a loose execution envelope nor the space target enlarges that scale. The same
actual execution supplies both instruction and physical-word observations.

This is a time-bounded word-RAM convention: increasing the declared time class
can increase unit-cost arithmetic width as well as address capacity. Bounds are
uniform even at widths larger than the minimum. Physical space keeps the fixed
input seed and distinct accessed addresses; it is not peak-live storage or bits.

The existing `TimeO`, `SpaceO` and budget-independent source `Correct` contracts
are unchanged. Existing input-width certificates imply this joint interface.
Finite domains should use `TimeSpaceBound` when concrete resource distinctions,
rather than arbitrary asymptotic constants, are intended.
-/

namespace Complexity.Program

universe u v
variable {α : Type u} {β : Type v} [Input α] [Output β] [RamInput α]

/-- One global multiplier on the raw-input and declared-time bit-length scales.
The argument is the declared time target, not a fitted execution envelope. -/
def timeWidth (overhead : Nat) (x : α) (timeTarget : Nat) : Nat :=
  width overhead x + (overhead + 1) * (2 + Nat.log2 (1 + timeTarget))

/-- The time-derived policy retains all original raw-input admission facts. -/
theorem width_le_timeWidth (overhead : Nat) (x : α) (timeTarget : Nat) :
    width overhead x ≤ timeWidth overhead x timeTarget :=
  Nat.le_add_right _ _

/-- Increasing the one global width multiplier preserves admission. -/
theorem timeWidth_mono_overhead {left right : Nat} (overheads : left ≤ right)
    (x : α) (timeTarget : Nat) :
    timeWidth left x timeTarget ≤ timeWidth right x timeTarget := by
  exact Nat.add_le_add (width_mono_overhead overheads x)
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right overheads 1))

/-- A time-admitted machine fits the fixed raw input representation. -/
theorem timeWidth_base {overhead wordWidth timeTarget : Nat} {x : α}
    (admitted : timeWidth overhead x timeTarget ≤ wordWidth) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (RamInput.words x) ≤ wordWidth :=
  width_base ((width_le_timeWidth overhead x timeTarget).trans admitted)

/-- Uniform joint resources at the declared time-derived word scale. The two
numeric envelopes are global and linearly bounded in their respective targets.
They do not participate in choosing the machine word width. -/
def TimeSpaceOOn (program : Complexity.Program α β) (valid : α → Prop)
    (timeGrowth spaceGrowth : α → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
    ∀ x, valid x → ∀ wordWidth, timeWidth overhead x (timeGrowth x) ≤ wordWidth →
      ∃ depth, ∃ execution : program.Execution x wordWidth depth,
        execution.result.steps ≤ timeBound (timeGrowth x) ∧
          execution.spaceWords ≤ spaceBound (spaceGrowth x)

/-- Restrict the mathematical domain without changing its time-derived machine
policy, numeric envelopes or actual executions. -/
theorem TimeSpaceOOn.mono_valid {program : Complexity.Program α β}
    {valid valid' : α → Prop} {timeGrowth spaceGrowth : α → Nat}
    (bounds : program.TimeSpaceOOn valid timeGrowth spaceGrowth)
    (inputs : ∀ x, valid' x → valid x) :
    program.TimeSpaceOOn valid' timeGrowth spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  exact ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic,
    fun x legal => runs x (inputs x legal)⟩

/-- Existing, stronger input-width time and space certificates remain usable.
Their actual runtime results are aligned by the existing determinism theorem. -/
theorem TimeSpaceOOn.of_time_space {program : Complexity.Program α β}
    {valid : α → Prop} {timeGrowth spaceGrowth : α → Nat}
    (time : program.TimeOOn valid timeGrowth)
    (space : program.SpaceOOn valid spaceGrowth) :
    program.TimeSpaceOOn valid timeGrowth spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ :=
    time.runs_space space
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro x legal wordWidth admitted
  exact runs x legal wordWidth
    ((width_le_timeWidth overhead x (timeGrowth x)).trans admitted)

/-- Joint resources include an actual successful execution on every legal input. -/
theorem TimeSpaceOOn.runs {program : Complexity.Program α β}
    {valid : α → Prop} {timeGrowth spaceGrowth : α → Nat}
    (bounds : program.TimeSpaceOOn valid timeGrowth spaceGrowth)
    {x : α} (legal : valid x) : ∃ wordWidth depth,
      Nonempty (program.Execution x wordWidth depth) := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  obtain ⟨depth, execution, _⟩ :=
    runs x legal (timeWidth overhead x (timeGrowth x)) (Nat.le_refl _)
  exact ⟨timeWidth overhead x (timeGrowth x), depth, ⟨execution⟩⟩

/-- Independent source correctness and both resources describe the same actual
run at every width admitted by the declared time target. -/
theorem TimeSpaceOOn.runs_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} {timeGrowth spaceGrowth : α → Nat}
    (bounds : program.TimeSpaceOOn valid timeGrowth spaceGrowth)
    (correct : program.Correct valid post) :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ)) (fun n => (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ)) (fun n => (n : ℝ)) ∧
      ∀ x, valid x → ∀ wordWidth, timeWidth overhead x (timeGrowth x) ≤ wordWidth →
        ∃ depth, ∃ execution : program.Execution x wordWidth depth,
          (∃ output, execution.Represents output ∧ post x output) ∧
          execution.result.steps ≤ timeBound (timeGrowth x) ∧
            execution.spaceWords ≤ spaceBound (spaceGrowth x) := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounds
  refine ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, ?_⟩
  intro x legal wordWidth admitted
  obtain ⟨depth, execution, timed, spaced⟩ := runs x legal wordWidth admitted
  exact ⟨depth, execution, correct.post_of_execution legal execution, timed, spaced⟩

/-- Concrete joint budgets at one author-fixed width. Every legal input must
fit and have one actual successful execution satisfying both exact caps.
There are no existential cost coefficients or asymptotic exceptions. -/
def TimeSpaceBound (program : Complexity.Program α β) (valid : α → Prop)
    (wordWidth : Nat) (timeBudget spaceBudget : α → Nat) : Prop :=
  ∀ x, valid x → ∃ admitted : width 0 x ≤ wordWidth,
    ∃ depth, ∃ execution : program.Execution x wordWidth depth,
      execution.result.steps ≤ timeBudget x ∧ execution.spaceWords ≤ spaceBudget x

/-- Restrict legal inputs and enlarge author-fixed concrete resource budgets. -/
theorem TimeSpaceBound.mono {program : Complexity.Program α β}
    {valid valid' : α → Prop} {wordWidth : Nat}
    {timeBudget spaceBudget timeBudget' spaceBudget' : α → Nat}
    (bounds : program.TimeSpaceBound valid wordWidth timeBudget spaceBudget)
    (inputs : ∀ x, valid' x → valid x)
    (times : ∀ x, valid' x → timeBudget x ≤ timeBudget' x)
    (spaces : ∀ x, valid' x → spaceBudget x ≤ spaceBudget' x) :
    program.TimeSpaceBound valid' wordWidth timeBudget' spaceBudget' := by
  intro x legal
  obtain ⟨admitted, depth, execution, timed, spaced⟩ := bounds x (inputs x legal)
  exact ⟨admitted, depth, execution, timed.trans (times x legal),
    spaced.trans (spaces x legal)⟩

/-- A concrete joint certificate retains the existing physical-space contract. -/
theorem TimeSpaceBound.space {program : Complexity.Program α β}
    {valid : α → Prop} {wordWidth : Nat} {timeBudget spaceBudget : α → Nat}
    (bounds : program.TimeSpaceBound valid wordWidth timeBudget spaceBudget) :
    program.SpaceBound valid wordWidth spaceBudget := by
  intro x legal
  obtain ⟨admitted, depth, execution, _, spaced⟩ := bounds x legal
  exact ⟨admitted, depth, execution, spaced⟩

/-- Source correctness observes the very execution satisfying the concrete caps. -/
theorem TimeSpaceBound.runs_correct {program : Complexity.Program α β}
    {valid : α → Prop} {post : α → β → Prop} {wordWidth : Nat}
    {timeBudget spaceBudget : α → Nat}
    (bounds : program.TimeSpaceBound valid wordWidth timeBudget spaceBudget)
    (correct : program.Correct valid post) :
    ∀ x, valid x → ∃ admitted : width 0 x ≤ wordWidth,
      ∃ depth, ∃ execution : program.Execution x wordWidth depth,
        (∃ output, execution.Represents output ∧ post x output) ∧
        execution.result.steps ≤ timeBudget x ∧ execution.spaceWords ≤ spaceBudget x := by
  intro x legal
  obtain ⟨admitted, depth, execution, timed, spaced⟩ := bounds x legal
  exact ⟨admitted, depth, execution, correct.post_of_execution legal execution, timed, spaced⟩

end Complexity.Program
