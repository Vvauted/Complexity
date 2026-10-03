/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Space
import Complexity.Computability.Ram.Compiler.Language.Program.Time
import Complexity.Computability.Ram.Compiler.Language.Arena.Space

/-!
# Uniform program space from independently bounded source arenas

Source readiness in a smaller arena bounds actual heap accesses. The machine
still uses its original, larger heap/stack separator: changing a resource proof
does not relocate its stack or select another compiled execution. The physical
bound adds the small heap region and live call-frame reservation, not the large
stack-base address. Measured source termination is independent of time bounds.

The small arena, word ranges and capacity hold at every legal mathematical
input and admitted width. They are obligations, not filters on the legal domain.
-/

namespace Complexity.Program

open Language Ram.LanguageCompiler

universe u v
variable {α : Type u} {β : Type v} [Input α] [Output β] [RamInput α]

/-- Publish a fixed-width finite budget directly from independently bounded
source readiness. The base width, source arena and actual machine capacity are
proved for every legal input; they cannot restrict the mathematical domain.
The resulting run uses the original machine heap/stack separator, not the
smaller heap resource bound used in the proof. -/
theorem SpaceBound.of_measured_depth {program : Complexity.Program α β}
    {valid : α → Prop} {w : Nat} {heapBound budget depth : α → Nat}
    {P : α → Heap → Value program.signatures[program.fn].result → Nat → Nat → Prop}
    (admitted : ∀ x, valid x → width 0 x ≤ w)
    (measured : ∀ x, valid x →
      ArenaMeasured program.source w (heapBound x) (depth x)
        (program.source.body program.fn)
        (fun finish control finalCursor steps =>
          ∃ value, control = .returned value ∧ P x finish.heap value finalCursor steps)
        ⟨program.args x, Input.heap x⟩ (RamInput.cursor x))
    (capacity : ∀ x, valid x →
      FunctionCapacity program.source program.fn w (depth x)
        (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
    (separated : ∀ x, valid x →
      heapBound x ≤ Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (inputArena : ∀ x, valid x →
      ArenaRep (RamInput.placement x w) (RamInput.cursor x) (heapBound x)
        (Input.heap x) (RamInput.entry x w))
    (bounded : ∀ x, valid x → heapBound x + (depth x + 1) *
      Ram.ABI.frameSize (programControl program.source) ≤ budget x) :
    program.SpaceBound valid w budget := by
  intro x legal
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, property⟩ :=
    ArenaMeasured.exists_returned_iff.mp (measured x legal)
  obtain ⟨outcome, _, _, _, physical⟩ := ready.execute_space
    (program.launch (width_base (admitted x legal)) (capacity x legal))
    (separated x legal) (inputArena x legal)
  exact ⟨admitted x legal, depth x, outcome, physical.trans (bounded x legal)⟩

/-- Publish independent uniform space from the same measured source execution
at input-dependent depth, keeping the original actual stack separator. -/
theorem SpaceO.of_measured_depth {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth heapBound framesBound : Nat → Nat}
    {depth : α → Nat} {overhead : Nat}
    {P : α → Heap → Value program.signatures[program.fn].result → Nat → Nat → Prop}
    (measured : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaMeasured program.source w (heapBound (size x)) (depth x)
        (program.source.body program.fn)
        (fun finish control finalCursor steps =>
          ∃ value, control = .returned value ∧ P x finish.heap value finalCursor steps)
        ⟨program.args x, Input.heap x⟩ (RamInput.cursor x))
    (capacity : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      FunctionCapacity program.source program.fn w (depth x)
        (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
    (separated : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      heapBound (size x) ≤ Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (inputArena : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaRep (RamInput.placement x w) (RamInput.cursor x) (heapBound (size x))
        (Input.heap x) (RamInput.entry x w))
    (frames : ∀ x, valid x → depth x + 1 ≤ framesBound (size x))
    (asymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => ((heapBound n + framesBound n *
        Ram.ABI.frameSize (programControl program.source) : Nat) : ℝ))
      (fun n => (growth n : ℝ))) : program.SpaceO valid size growth := by
  refine ⟨overhead, fun n => heapBound n + framesBound n *
    Ram.ABI.frameSize (programControl program.source), asymptotic, ?_⟩
  intro x legal w admitted
  obtain ⟨finish, value, finalCursor, steps, execution, ready, cost, property⟩ :=
    ArenaMeasured.exists_returned_iff.mp (measured x legal w admitted)
  obtain ⟨outcome, _, _, _, bounded⟩ := ready.execute_space
    (program.launch (width_base admitted) (capacity x legal w admitted))
    (separated x legal w admitted) (inputArena x legal w admitted)
  refine ⟨depth x, outcome, ?_⟩
  exact bounded.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (frames x legal)) _)

/-- Fixed-depth independent space publication, without a time budget. -/
theorem SpaceO.of_measured {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth heapBound : Nat → Nat}
    {depth overhead : Nat}
    {P : α → Heap → Value program.signatures[program.fn].result → Nat → Nat → Prop}
    (measured : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaMeasured program.source w (heapBound (size x)) depth
        (program.source.body program.fn)
        (fun finish control finalCursor steps =>
          ∃ value, control = .returned value ∧ P x finish.heap value finalCursor steps)
        ⟨program.args x, Input.heap x⟩ (RamInput.cursor x))
    (capacity : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      FunctionCapacity program.source program.fn w depth
        (Ram.LanguageCompiler.ArrayFunction.heapLimit w))
    (separated : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      heapBound (size x) ≤ Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (inputArena : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaRep (RamInput.placement x w) (RamInput.cursor x) (heapBound (size x))
        (Input.heap x) (RamInput.entry x w))
    (asymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => ((heapBound n + (depth + 1) *
        Ram.ABI.frameSize (programControl program.source) : Nat) : ℝ))
      (fun n => (growth n : ℝ))) : program.SpaceO valid size growth :=
  SpaceO.of_measured_depth (depth := fun _ => depth) (framesBound := fun _ => depth + 1)
    measured capacity separated inputArena (fun _ _ => Nat.le_refl _) asymptotic

/-- Fixed code and stack capacity are supplied by one larger uniform width
constant. Small-arena readiness and input representation retain their original
width requirement; no mathematical instance is removed. -/
theorem SpaceO.of_measured_auto {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth heapBound : Nat → Nat}
    {depth overhead : Nat}
    {P : α → Heap → Value program.signatures[program.fn].result → Nat → Nat → Prop}
    (measured : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaMeasured program.source w (heapBound (size x)) depth
        (program.source.body program.fn)
        (fun finish control finalCursor steps =>
          ∃ value, control = .returned value ∧ P x finish.heap value finalCursor steps)
        ⟨program.args x, Input.heap x⟩ (RamInput.cursor x))
    (separated : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      heapBound (size x) ≤ Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (inputArena : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaRep (RamInput.placement x w) (RamInput.cursor x) (heapBound (size x))
        (Input.heap x) (RamInput.entry x w))
    (asymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => ((heapBound n + (depth + 1) *
        Ram.ABI.frameSize (programControl program.source) : Nat) : ℝ))
      (fun n => (growth n : ℝ))) : program.SpaceO valid size growth := by
  let combined := max overhead (program.capacityOverhead depth)
  have smaller (x : α) : width overhead x ≤ width combined x := by
    change (overhead + 1) * _ ≤ (combined + 1) * _
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
  apply SpaceO.of_measured (overhead := combined)
    (fun x legal w admitted => measured x legal w ((smaller x).trans admitted))
    (fun _ _ _ admitted => program.capacity_of_le depth (Nat.le_max_right _ _) admitted)
    (fun x legal w admitted => separated x legal w ((smaller x).trans admitted))
    (fun x legal w admitted => inputArena x legal w ((smaller x).trans admitted))
    asymptotic

/-- Input-dependent call depth with automatic uniform polynomial capacity.
The actual frame count has its own space envelope, independently of time. -/
theorem SpaceO.of_measured_depth_auto {program : Complexity.Program α β}
    {valid : α → Prop} {size : α → Nat} {growth heapBound framesBound : Nat → Nat}
    {depth : α → Nat} {overhead coefficient degree : Nat}
    {P : α → Heap → Value program.signatures[program.fn].result → Nat → Nat → Prop}
    (measured : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaMeasured program.source w (heapBound (size x)) (depth x)
        (program.source.body program.fn)
        (fun finish control finalCursor steps =>
          ∃ value, control = .returned value ∧ P x finish.heap value finalCursor steps)
        ⟨program.args x, Input.heap x⟩ (RamInput.cursor x))
    (separated : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      heapBound (size x) ≤ Ram.LanguageCompiler.ArrayFunction.heapLimit w)
    (inputArena : ∀ x, valid x → ∀ w, width overhead x ≤ w →
      ArenaRep (RamInput.placement x w) (RamInput.cursor x) (heapBound (size x))
        (Input.heap x) (RamInput.entry x w))
    (depthBound : ∀ x, valid x → depth x + 1 ≤ coefficient *
      ((RamInput.words x).size + Ram.LanguageCompiler.ArrayFunction.inputMax
        (RamInput.words x) + 2) ^ degree)
    (frames : ∀ x, valid x → depth x + 1 ≤ framesBound (size x))
    (asymptotic : Asymptotics.IsBigO Filter.atTop
      (fun n => ((heapBound n + framesBound n *
        Ram.ABI.frameSize (programControl program.source) : Nat) : ℝ))
      (fun n => (growth n : ℝ))) : program.SpaceO valid size growth := by
  let combined := max overhead (program.capacityOverheadPow coefficient degree)
  have smaller (x : α) : width overhead x ≤ width combined x := by
    change (overhead + 1) * _ ≤ (combined + 1) * _
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
  apply SpaceO.of_measured_depth (overhead := combined)
    (fun x legal w admitted => measured x legal w ((smaller x).trans admitted))
    (fun x legal _ admitted => program.capacity_of_depth_le_pow (depthBound x legal)
      (Nat.le_max_right _ _) admitted)
    (fun x legal w admitted => separated x legal w ((smaller x).trans admitted))
    (fun x legal w admitted => inputArena x legal w ((smaller x).trans admitted))
    frames asymptotic

end Complexity.Program
