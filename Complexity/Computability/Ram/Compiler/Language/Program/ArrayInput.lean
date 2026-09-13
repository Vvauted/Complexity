/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayInput
import Complexity.Computability.Ram.Compiler.Language.Program.Input
import Complexity.Computability.Ram.Compiler.Language.Arena.Allocation

/-!
# Composing preloaded array inputs

An array prefix appends one source object and one physical interval after the
tail input's existing arena. Old object identifiers, arguments and memory cells
are retained. The input-width scale records the old structural cursor together
with all original scalar data; it remains the library's logarithmic scale.

These are initial-state representations, not executable loaders. The generic
arena extension theorem also underlies actual allocation, whose initialization
and instruction costs remain separately proved by the existing compiler.
-/

namespace Complexity.Program.RamInput

open Language Ram Ram.LanguageCompiler
open Ram.LanguageCompiler.ArrayFunction

universe u

/-- Raw input cells and the already reserved structural extent fix the width
needed when another array is appended. No candidate computation supplies them. -/
def arrayWords {kind : CellTy} (next : Nat) (xs : Array (CellValue kind))
    (tail : Array Nat) : Array Nat :=
  #[next] ++ (xs.map cellToNat ++ tail)

private theorem arrayWords_tail_width {kind : CellTy} {next w : Nat}
    {xs : Array (CellValue kind)} {tail : Array Nat}
    (width : 1 + inputWordWidth (arrayWords next xs tail) ≤ w) :
    1 + inputWordWidth tail ≤ w := by
  have first := inputWordWidth_append_right (xs.map cellToNat) tail
  have second := inputWordWidth_append_right #[next] (xs.map cellToNat ++ tail)
  change 1 + inputWordWidth (#[next] ++ (xs.map cellToNat ++ tail)) ≤ w at width
  omega

private theorem arrayWords_capacity {kind : CellTy} {next w : Nat}
    {xs : Array (CellValue kind)} {tail : Array Nat}
    (width : 1 + inputWordWidth (arrayWords next xs tail) ≤ w) :
    next + xs.size ≤ heapLimit w := by
  have extent : next ≤ inputMax (arrayWords next xs tail) :=
    List.le_max?_getD_of_mem (by simp [arrayWords])
  have size : xs.size ≤ (arrayWords next xs tail).size := by
    simp [arrayWords]
    omega
  have bound := size_add_max_lt_heapLimit width
  omega

private theorem arrayWords_cell_fits {kind : CellTy} {next w : Nat}
    {xs : Array (CellValue kind)} {tail : Array Nat}
    (width : 1 + inputWordWidth (arrayWords next xs tail) ≤ w)
    (index : Nat) (bound : index < xs.size) : cellToNat xs[index] < 2 ^ w := by
  have present : cellToNat xs[index] ∈ (arrayWords next xs tail).toList := by
    simp only [arrayWords, Array.toList_append, Array.toList_map, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr
      ⟨xs[index], Array.getElem_mem_toList bound, rfl⟩))
  have cell : cellToNat xs[index] ≤ inputMax (arrayWords next xs tail) :=
    List.le_max?_getD_of_mem present
  have capacity := size_add_max_lt_heapLimit width
  have limit := heapLimit_lt_word (width_pos width)
  omega

/-- The mathematical initial state with one additional preloaded interval.
This is not an in-program bulk store or a claim of free initialization. -/
def appendEntry {kind : CellTy} {w : Nat} (entry : Ram.Source.State w)
    (next : Nat) (xs : Array (CellValue kind)) : Ram.Source.State w :=
  { entry with mem := fun address =>
      if address.toNat = 0 then BitVec.ofNat w (next + xs.size)
      else if next ≤ address.toNat ∧ address.toNat < next + xs.size then
        (objectWords w xs)[address.toNat - next]?.getD 0
      else entry.mem address }

private theorem appendEntry_cursor {kind : CellTy} {w : Nat} (entry : Ram.Source.State w)
    (next : Nat) (xs : Array (CellValue kind)) :
    (appendEntry entry next xs).mem 0 = BitVec.ofNat w (next + xs.size) := by
  simp [appendEntry]

private theorem appendEntry_frame {kind : CellTy} {w : Nat} (entry : Ram.Source.State w)
    (next : Nat) (xs : Array (CellValue kind)) (address : Word w)
    (positive : 0 < address.toNat) (old : address.toNat < next) :
    (appendEntry entry next xs).mem address = entry.mem address := by
  have outside : ¬(next ≤ address.toNat ∧ address.toNat < next + xs.size) := by omega
  simp only [appendEntry, if_neg (Nat.ne_of_gt positive), if_neg outside]

private theorem appendEntry_arrayAt {kind : CellTy} {w next limit : Nat}
    (entry : Ram.Source.State w) (xs : Array (CellValue kind))
    (positive : 0 < next) (capacity : next + xs.size ≤ limit) (fits : limit < 2 ^ w) :
    Ram.Source.ArrayAt limit (BitVec.ofNat w next) (objectWords w xs).toList
      (appendEntry entry next xs) := by
  have base : (BitVec.ofNat w next).toNat = next :=
    Word.ofNat_toNat_of_lt (by omega)
  have length : (objectWords w xs).toList.length = xs.size := by simp [objectWords]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [base, length]
    omega
  · intro index bound
    have inBounds : index < xs.size := by simpa only [length] using bound
    have address : (arrayAddr (BitVec.ofNat w next) index).toNat = next + index := by
      rw [arrayAddr_toNat (by rw [base]; omega), base]
    have nonzero : next + index ≠ 0 := by omega
    have inside : next ≤ next + index ∧ next + index < next + xs.size := by omega
    simp only [appendEntry, address, if_neg nonzero, if_pos inside, Nat.add_sub_cancel_left,
      Array.getElem?_eq_getElem (xs := objectWords w xs) (i := index)
        (by simpa [objectWords] using inBounds),
      Option.getD_some, Array.getElem_toList]
  · simpa only [base, length] using capacity

/-- Append a preloaded array while retaining the complete old arena and its
object placement. The same rule represents all scalar array kinds. -/
theorem appendEntry_arena {kind : CellTy} {w next limit : Nat}
    {placement : Nat → Word w} {heap : Language.Heap} {entry : Ram.Source.State w}
    (arena : ArenaRep placement next limit heap entry) (xs : Array (CellValue kind))
    (cells : ∀ index, (bound : index < xs.size) → cellToNat xs[index] < 2 ^ w)
    (capacity : next + xs.size ≤ limit) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + xs.size) limit (Input.arrayHeap kind heap xs) (appendEntry entry next xs) := by
  exact arena.push_buffer cells capacity (appendEntry_cursor entry next xs)
    (appendEntry_arrayAt entry xs arena.cursor_pos capacity arena.limit_lt)
    (appendEntry_frame entry next xs)

/-- Reuse a registered tail layout while adding an independent scalar-array
argument. The tail's source objects and physical addresses do not move. -/
def consArray (kind : CellTy) {β : Type u} [tail : Input β]
    [Input.PrefixClosed β] [RamInput β] :
    @RamInput (Array (CellValue kind) × β) (Input.consArray kind tail) := by
  letI : Input (Array (CellValue kind) × β) := Input.consArray kind tail
  exact {
    words := fun x => arrayWords (kind := kind) (RamInput.cursor x.2) x.1 (RamInput.words x.2)
    placement := fun x w => Function.update (RamInput.placement x.2 w)
      (Input.heap x.2).objects.size (BitVec.ofNat w (RamInput.cursor x.2))
    entry := fun x w => appendEntry (kind := kind)
      (RamInput.entry x.2 w) (RamInput.cursor x.2) x.1
    cursor := fun x => RamInput.cursor x.2 + x.1.size
    rooted := by
      intro x
      apply Env.Rooted.cons (τ := .buffer kind)
      · exact Env.Rooted.mono (RamInput.rooted x.2)
          (Input.arrayHeap_shapeExtends kind (Input.heap x.2) x.1)
      · exact Input.arrayBuffer_rooted kind (Input.heap x.2) x.1
    fits := by
      intro x w width
      change EnvFits w
        (Env.cons (τ := .buffer kind) (Input.arrayBuffer kind (Input.heap x.2) x.1) (Input.args x.2))
      rw [EnvFits.cons_buffer_iff]
      refine ⟨?_, RamInput.fits x.2 w (arrayWords_tail_width width)⟩
      change x.1.size < 2 ^ w
      have capacity := arrayWords_capacity width
      have limit := heapLimit_lt_word (width_pos width)
      omega
    arena := fun x w width =>
      appendEntry_arena (kind := kind) (RamInput.arena x.2 w (arrayWords_tail_width width)) x.1
        (arrayWords_cell_fits width) (arrayWords_capacity width) }

/-- Any finite right-associated combination of natural arrays and registered
prefix-stable inputs uses the same proved append layout. -/
instance arrayNatProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (Array Nat × β) := consArray .nat

/-- Boolean arrays compose with the same physical layout and exact zero-or-one cells. -/
instance arrayBoolProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (Array Bool × β) := consArray .bool

/-- A terminal Boolean array uses the same proved append into the empty arena,
without introducing a trailing source parameter. -/
instance arrayBool : RamInput (Array Bool) where
  words xs := arrayWords (kind := .bool) 1 xs #[]
  placement _ w := Function.update (Ram.LanguageCompiler.ArrayFunction.placement w) 0
    (BitVec.ofNat w 1)
  entry xs w := appendEntry (kind := .bool)
    (Ram.LanguageCompiler.ArrayFunction.entry w #[]) 1 xs
  cursor xs := 1 + xs.size
  rooted := by
    intro xs
    exact Env.Rooted.cons (τ := .buffer .bool) (Env.Rooted.empty _)
      (Input.arrayBuffer .bool Input.emptyHeap xs)
      (Input.arrayBuffer_rooted .bool Input.emptyHeap xs)
  fits := by
    intro xs w width
    change EnvFits w
      (Env.cons (τ := .buffer .bool) (Input.arrayBuffer .bool Input.emptyHeap xs) Env.empty)
    rw [EnvFits.cons_buffer_iff]
    refine ⟨?_, EnvFits.empty w⟩
    change xs.size < 2 ^ w
    have capacity := arrayWords_capacity width
    have limit := heapLimit_lt_word (width_pos width)
    omega
  arena := fun xs w width => appendEntry_arena (kind := .bool)
    (empty_arenaRep (words := arrayWords (kind := .bool) 1 xs #[]) width) xs
    (arrayWords_cell_fits width) (arrayWords_capacity width)

end Complexity.Program.RamInput
