/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayFunction
import Complexity.Computability.Ram.Compiler.Language.Program.Space

/-!
# Physical-word space for the single-array interface

The array interface is the general program interface at the same preloaded
array, code, execution and width policy. Its space observation counts the union
of the initialized input prefix (including metadata) and actual heap accesses.
It is neither reserved address capacity nor peak live storage. No wrapper,
input conversion, second execution relation or independent cost model is added.
-/

namespace Complexity.Language.ArrayFunction

/-- The same invocation's initialized input and actually accessed words. -/
abbrev Execution.spaceFootprint {f : ArrayFunction} {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) : Finset (Ram.Word w) :=
  Complexity.Program.Execution.spaceFootprint (program := f.toProgram) execution

/-- Distinct physical words in the same general-program space observation. -/
abbrev Execution.spaceWords {f : ArrayFunction} {xs : Array Nat} {w depth : Nat}
    (execution : f.Execution xs w depth) : Nat :=
  Complexity.Program.Execution.spaceWords (program := f.toProgram) execution

/-- A finite space budget at an author-fixed width, including input metadata.
Admission and successful execution must be proved for every legal array. -/
abbrev SpaceBound (f : ArrayFunction) (valid : Array Nat → Prop)
    (wordWidth : Nat) (budget : Array Nat → Nat) : Prop :=
  f.toProgram.SpaceBound valid wordWidth budget

/-- Uniform array-length-indexed physical-word space of the same program. -/
abbrev SpaceO (f : ArrayFunction) (valid : Array Nat → Prop)
    (growth : Nat → Nat) : Prop := f.toProgram.SpaceO valid Array.size growth

/-- Write a possibly multivariate space target directly on the input array. -/
abbrev SpaceOOn (f : ArrayFunction) (valid : Array Nat → Prop)
    (growth : Array Nat → Nat) : Prop := f.toProgram.SpaceOOn valid growth

/-- Restrict the finite input domain and increase its space allowance. -/
theorem SpaceBound.mono {f : ArrayFunction} {valid valid' : Array Nat → Prop}
    {w : Nat} {budget budget' : Array Nat → Nat}
    (space : f.SpaceBound valid w budget)
    (inputs : ∀ xs, valid' xs → valid xs)
    (budgets : ∀ xs, valid' xs → budget xs ≤ budget' xs) :
    f.SpaceBound valid' w budget' :=
  Complexity.Program.SpaceBound.mono space inputs budgets

/-- Reuse a finite space bound on a mathematical subtask. -/
theorem SpaceBound.mono_valid {f : ArrayFunction} {valid valid' : Array Nat → Prop}
    {w : Nat} {budget : Array Nat → Nat} (space : f.SpaceBound valid w budget)
    (inputs : ∀ xs, valid' xs → valid xs) : f.SpaceBound valid' w budget :=
  Complexity.Program.SpaceBound.mono_valid space inputs

/-- A finite space certificate entails a successful actual array execution. -/
theorem SpaceBound.runs {f : ArrayFunction} {valid : Array Nat → Prop}
    {w : Nat} {budget : Array Nat → Nat} (space : f.SpaceBound valid w budget)
    {xs : Array Nat} (legal : valid xs) : ∃ depth, Nonempty (f.Execution xs w depth) :=
  Complexity.Program.SpaceBound.runs space legal

/-- Independently proved correctness belongs to this finite-space execution. -/
theorem SpaceBound.runs_correct {f : ArrayFunction} {valid : Array Nat → Prop}
    {answer : Array Nat → Nat} {w : Nat} {budget : Array Nat → Nat}
    (space : f.SpaceBound valid w budget) (correct : f.Correct valid answer) :
    ∀ xs, valid xs → ∃ admitted : width 0 xs ≤ w,
      ∃ depth, ∃ execution : f.Execution xs w depth,
        Execution.output execution = answer xs ∧ execution.spaceWords ≤ budget xs := by
  intro xs legal
  obtain ⟨admitted, depth, execution, bounded⟩ := space xs legal
  exact ⟨admitted, depth, execution, correct.output_eq legal execution, bounded⟩

/-- Restrict legal arrays and weaken the uniform space target. -/
theorem SpaceO.mono {f : ArrayFunction} {valid valid' : Array Nat → Prop}
    {growth growth' : Nat → Nat} (space : f.SpaceO valid growth)
    (inputs : ∀ xs, valid' xs → valid xs)
    (growthBound : Asymptotics.IsBigO Filter.atTop
      (fun n => (growth n : ℝ)) (fun n => (growth' n : ℝ))) :
    f.SpaceO valid' growth' := Complexity.Program.SpaceO.mono space inputs growthBound

/-- Reuse a uniform space certificate on a mathematical subtask. -/
theorem SpaceO.mono_valid {f : ArrayFunction} {valid valid' : Array Nat → Prop}
    {growth : Nat → Nat} (space : f.SpaceO valid growth)
    (inputs : ∀ xs, valid' xs → valid xs) : f.SpaceO valid' growth :=
  Complexity.Program.SpaceO.mono_valid space inputs

/-- Uniform space includes termination at an admitted word width. -/
theorem SpaceO.runs {f : ArrayFunction} {valid : Array Nat → Prop} {growth : Nat → Nat}
    (space : f.SpaceO valid growth) {xs : Array Nat} (legal : valid xs) :
    ∃ w depth, Nonempty (f.Execution xs w depth) :=
  Complexity.Program.SpaceO.runs space legal

/-- The space envelope and independent array answer hold for the same run. -/
theorem SpaceO.runs_correct {f : ArrayFunction} {valid : Array Nat → Prop}
    {answer : Array Nat → Nat} {growth : Nat → Nat}
    (space : f.SpaceO valid growth) (correct : f.Correct valid answer) :
    ∃ overhead : Nat, ∃ bound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
        (fun n => (growth n : ℝ)) ∧
      ∀ xs, valid xs → ∀ w, width overhead xs ≤ w →
        ∃ depth, ∃ execution : f.Execution xs w depth,
          Execution.output execution = answer xs ∧ execution.spaceWords ≤ bound xs.size := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro xs legal w admitted
  obtain ⟨depth, execution, bounded⟩ := runs xs legal w admitted
  exact ⟨depth, execution, correct.output_eq legal execution, bounded⟩

end Complexity.Language.ArrayFunction
