/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program

/-!
# Canonical preloaded program inputs

Natural arrays retain the fixed contiguous input arena. Scalar inputs have an
empty source heap and only the allocator metadata cell; scalar parameters are
passed through the existing call frame. A scalar prefix retains its tail's
physical heap and extends the fixed mathematical word-width scale.

These instances prove initialization at every width admitted by that scale.
They select neither legal inputs nor function, code, stack or allocation capacity.
Input preparation remains outside the preloaded-invocation execution boundary.
-/

namespace Complexity.Program

open Complexity.Language Ram.LanguageCompiler

namespace RamInput

universe u v

private theorem inputWordWidth_cons (head : Nat) (tail : Array Nat) :
    Ram.LanguageCompiler.ArrayFunction.inputWordWidth tail ≤
      Ram.LanguageCompiler.ArrayFunction.inputWordWidth (#[head] ++ tail) := by
  have maximum : Ram.LanguageCompiler.ArrayFunction.inputMax tail ≤
      Ram.LanguageCompiler.ArrayFunction.inputMax (#[head] ++ tail) := by
    simp only [Ram.LanguageCompiler.ArrayFunction.inputMax, Array.toList_append]
    change tail.toList.max?.getD 0 ≤ (head :: tail.toList).max?.getD 0
    cases found : tail.toList.max? <;> simp [List.max?_cons, found]
  have size : (#[head] ++ tail).size = 1 + tail.size := by simp
  unfold Ram.LanguageCompiler.ArrayFunction.inputWordWidth
  apply Nat.add_le_add_left
  apply (Nat.le_log2 (by omega)).2
  have base := Nat.log2_self_le
    (n := tail.size + Ram.LanguageCompiler.ArrayFunction.inputMax tail + 2) (by omega)
  omega

private theorem tail_width {head : Nat} {tail : Array Nat} {w : Nat}
    (width : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (#[head] ++ tail) ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth tail ≤ w := by
  have mono := inputWordWidth_cons head tail
  omega

private theorem head_lt_word {head : Nat} {tail : Array Nat} {w : Nat}
    (width : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth (#[head] ++ tail) ≤ w) :
    head < 2 ^ w := by
  simpa using Ram.LanguageCompiler.ArrayFunction.cell_lt_word
    (xs := #[head] ++ tail) width 0 (by simp)

private theorem empty_arenaRep {words : Array Nat} {w : Nat}
    (width : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth words ≤ w) :
    ArenaRep (Ram.LanguageCompiler.ArrayFunction.placement w) 1
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) Input.emptyHeap
      (Ram.LanguageCompiler.ArrayFunction.entry w #[]) := by
  refine ⟨HeapRep.empty _ _ _, by decide, ?_,
    Ram.LanguageCompiler.ArrayFunction.heapLimit_lt_word
      (Ram.LanguageCompiler.ArrayFunction.width_pos width), ?_, ?_⟩
  · have bound := Ram.LanguageCompiler.ArrayFunction.cursor_le_heapLimit width
    unfold Ram.LanguageCompiler.ArrayFunction.cursor at bound
    omega
  · simp [Ram.LanguageCompiler.ArrayFunction.entry,
      Ram.LanguageCompiler.ArrayFunction.cursor]
  · intro id object found
    simp [Input.emptyHeap] at found

/-- Arrays use the existing complete one-object input representation. -/
instance arrayNat : RamInput (Array Nat) where
  words := id
  placement := fun _ w => Ram.LanguageCompiler.ArrayFunction.placement w
  entry := fun xs w => Ram.LanguageCompiler.ArrayFunction.entry w xs
  cursor := Ram.LanguageCompiler.ArrayFunction.cursor
  rooted := Ram.LanguageCompiler.ArrayFunction.inputArgs_rooted
  fits := fun _ _ width => Ram.LanguageCompiler.ArrayFunction.inputArgs_fits width
  arena := fun _ _ width => Ram.LanguageCompiler.ArrayFunction.input_arenaRep width

/-- A natural parameter has no heap object; its actual value fixes the scale. -/
instance nat : RamInput Nat where
  words := fun n => #[n]
  placement := fun _ w => Ram.LanguageCompiler.ArrayFunction.placement w
  entry := fun _ w => Ram.LanguageCompiler.ArrayFunction.entry w #[]
  cursor := fun _ => 1
  rooted := by
    intro n
    change (Env.cons (τ := .nat) n Env.empty).Rooted Input.emptyHeap
    exact Env.Rooted.cons (τ := .nat) (Env.Rooted.empty _) n trivial
  fits := by
    intro n w width
    change EnvFits w (Env.cons (τ := .nat) n Env.empty)
    rw [EnvFits.cons_nat_iff]
    refine ⟨?_, EnvFits.empty w⟩
    simpa using Ram.LanguageCompiler.ArrayFunction.cell_lt_word
      (xs := #[n]) width 0 (by simp)
  arena := fun _ _ width => empty_arenaRep width

/-- A Boolean parameter contributes its canonical zero-or-one input word. -/
instance bool : RamInput Bool where
  words := fun b => #[if b then 1 else 0]
  placement := fun _ w => Ram.LanguageCompiler.ArrayFunction.placement w
  entry := fun _ w => Ram.LanguageCompiler.ArrayFunction.entry w #[]
  cursor := fun _ => 1
  rooted := by
    intro b
    change (Env.cons (τ := .bool) b Env.empty).Rooted Input.emptyHeap
    exact Env.Rooted.cons (τ := .bool) (Env.Rooted.empty _) b trivial
  fits := by
    intro b w width
    change EnvFits w (Env.cons (τ := .bool) b Env.empty)
    rw [EnvFits.cons_bool_iff]
    refine ⟨?_, EnvFits.empty w⟩
    simpa using Ram.LanguageCompiler.ArrayFunction.cell_lt_word
      (xs := #[if b then 1 else 0]) width 0 (by simp)
  arena := fun _ _ width => empty_arenaRep width

/-- Unit occupies no input word and retains the empty initialized arena. -/
instance unit : RamInput Unit where
  words := fun _ => #[]
  placement := fun _ w => Ram.LanguageCompiler.ArrayFunction.placement w
  entry := fun _ w => Ram.LanguageCompiler.ArrayFunction.entry w #[]
  cursor := fun _ => 1
  rooted := by
    intro value
    change (Env.cons (τ := .unit) value Env.empty).Rooted Input.emptyHeap
    exact Env.Rooted.cons (τ := .unit) (Env.Rooted.empty _) value trivial
  fits := by
    intro value w width
    change EnvFits w (Env.cons (τ := .unit) value Env.empty)
    simp only [EnvFits.cons_unit_iff, EnvFits.empty]
  arena := fun _ _ width => empty_arenaRep width

/-- A natural prefix contributes one actual input word and keeps the tail arena. -/
instance natProd {β : Type v} [Input β] [RamInput β] : RamInput (Nat × β) where
  words := fun x => #[x.1] ++ RamInput.words x.2
  placement := fun x w => RamInput.placement x.2 w
  entry := fun x w => RamInput.entry x.2 w
  cursor := fun x => RamInput.cursor x.2
  rooted := by
    intro x
    change (Env.cons (τ := .nat) x.1 (Input.args x.2)).Rooted (Input.heap x.2)
    exact Env.Rooted.cons (τ := .nat) (RamInput.rooted x.2) x.1 trivial
  fits := by
    intro x w width
    change EnvFits w (Env.cons (τ := .nat) x.1 (Input.args x.2))
    rw [EnvFits.cons_nat_iff]
    exact ⟨head_lt_word width, RamInput.fits x.2 w (tail_width width)⟩
  arena := fun x w width => RamInput.arena x.2 w (tail_width width)

/-- A Boolean prefix adds its zero-or-one word without moving any tail object. -/
instance boolProd {β : Type v} [Input β] [RamInput β] : RamInput (Bool × β) where
  words := fun x => #[if x.1 then 1 else 0] ++ RamInput.words x.2
  placement := fun x w => RamInput.placement x.2 w
  entry := fun x w => RamInput.entry x.2 w
  cursor := fun x => RamInput.cursor x.2
  rooted := by
    intro x
    change (Env.cons (τ := .bool) x.1 (Input.args x.2)).Rooted (Input.heap x.2)
    exact Env.Rooted.cons (τ := .bool) (RamInput.rooted x.2) x.1 trivial
  fits := by
    intro x w width
    change EnvFits w (Env.cons (τ := .bool) x.1 (Input.args x.2))
    rw [EnvFits.cons_bool_iff]
    exact ⟨head_lt_word width, RamInput.fits x.2 w (tail_width width)⟩
  arena := fun x w width => RamInput.arena x.2 w (tail_width width)

/-- Unit adds no width information or storage to the tail's fixed input layout. -/
instance unitProd {β : Type v} [Input β] [RamInput β] : RamInput (Unit × β) where
  words := fun x => RamInput.words x.2
  placement := fun x w => RamInput.placement x.2 w
  entry := fun x w => RamInput.entry x.2 w
  cursor := fun x => RamInput.cursor x.2
  rooted := by
    intro x
    change (Env.cons (τ := .unit) x.1 (Input.args x.2)).Rooted (Input.heap x.2)
    exact Env.Rooted.cons (τ := .unit) (RamInput.rooted x.2) x.1 trivial
  fits := by
    intro x w width
    change EnvFits w (Env.cons (τ := .unit) x.1 (Input.args x.2))
    rw [EnvFits.cons_unit_iff]
    exact RamInput.fits x.2 w width
  arena := fun x w width => RamInput.arena x.2 w width

/-- Reuse a registered physical layout through a fixed lossless input presentation.
This changes no physical data and introduces no executable host transformation. -/
def comap {α : Type u} {β : Type v} [input : Input α] [RamInput α]
    (view : β ↪ α) : @RamInput β (Input.comap input view) := by
  letI : Input β := Input.comap input view
  exact {
    words := fun x => RamInput.words (view x)
    placement := fun x w => RamInput.placement (view x) w
    entry := fun x w => RamInput.entry (view x) w
    cursor := fun x => RamInput.cursor (view x)
    rooted := fun x => RamInput.rooted (view x)
    fits := fun x w width => RamInput.fits (view x) w width
    arena := fun x w width => RamInput.arena (view x) w width }

end RamInput
end Complexity.Program
