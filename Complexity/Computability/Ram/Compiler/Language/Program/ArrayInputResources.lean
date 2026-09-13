/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInput
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendReady

/-!
# Uniform allocation space for preloaded array inputs

One extra bit above the input representation's base requirement leaves room for
as many fresh cells as there are raw input words. The proof reuses the registered
arena at the smaller width; its structural cursor is independent of word width.
The global width policy with overhead at least one always supplies this bit.

For the canonical pair of natural arrays, these facts discharge the range and
allocation premises of the existing append execution. The actual input heap and
arguments are retained, and allocation still executes the library's real body.
This neither changes input preparation nor supplies a second append algorithm.
-/

namespace Complexity.Program

open Language
open Language.Buffer
open Ram.LanguageCompiler
open Ram.LanguageCompiler.ArrayFunction

universe u

/-- A fixed overhead of at least one supplies an extra bit beyond the input
representation's already sufficient base width. -/
theorem width_extraBit {α : Type u} [Input α] [RamInput α]
    {overhead w : Nat} {x : α} (large : 1 ≤ overhead)
    (admitted : width overhead x ≤ w) :
    2 + inputWordWidth (RamInput.words x) ≤ w := by
  have doubled := Nat.mul_le_mul_right
    (inputWordWidth (RamInput.words x) + 1) (by omega : 2 ≤ overhead + 1)
  change (overhead + 1) * (inputWordWidth (RamInput.words x) + 1) ≤ w at admitted
  omega

/-- The width-independent initial cursor plus one fresh cell per raw input word
fits the fixed arena. This uses only the existing input representation contract. -/
theorem width_reserve_words {α : Type u} [Input α] [RamInput α]
    {overhead w : Nat} {x : α} (large : 1 ≤ overhead)
    (admitted : width overhead x ≤ w) :
    RamInput.cursor x + (RamInput.words x).size ≤ heapLimit w := by
  have extra := width_extraBit large admitted
  have smaller : 1 + inputWordWidth (RamInput.words x) ≤ w - 1 := by omega
  have oldCursor := (RamInput.arena x (w - 1) smaller).cursor_le
  have oldWords := size_add_max_lt_heapLimit smaller
  have halves : heapLimit (w - 1) + heapLimit (w - 1) = heapLimit w := by
    unfold heapLimit
    calc
      2 ^ (w - 1 - 1) + 2 ^ (w - 1 - 1) = 2 ^ (w - 1 - 1 + 1) :=
        (Nat.two_pow_succ _).symm
      _ = 2 ^ (w - 1) := by congr 1; omega
  omega

namespace RamInput

/-- A pair's raw width data are its old cursor followed by the original arrays. -/
@[simp] theorem arrayPair_words (left right : Array Nat) :
    RamInput.words (left, right) = #[right.size + 1] ++ (left ++ right) := by
  change #[right.size + 1] ++ (left.map (fun value => value) ++ right) = _
  rw [Array.map_id']

/-- The canonical pair reserves exactly its two arrays and the arena metadata. -/
@[simp] theorem arrayPair_cursor (left right : Array Nat) :
    RamInput.cursor (left, right) = 1 + left.size + right.size := by
  change right.size + 1 + left.size = _
  omega

end RamInput

/-- Both actual input arguments observe their mathematical arrays in the same
registered initial heap; no separate contents construction is needed. -/
theorem arrayPair_contents (left right : Array Nat) :
    (Input.args (left, right)).head.Contents (Input.heap (left, right)) left ∧
      (Input.args (left, right)).tail.head.Contents (Input.heap (left, right)) right :=
  Input.represented (left, right)

/-- One uniform width premise supplies both cell ranges, the combined length,
and capacity for an output as long as the two input arrays together. -/
theorem arrayPair_resources {overhead w : Nat} {left right : Array Nat}
    (large : 1 ≤ overhead) (admitted : width overhead (left, right) ≤ w) :
    0 < w ∧
      (∀ i (hi : i < left.size), left[i] < 2 ^ w) ∧
      (∀ i (hi : i < right.size), right[i] < 2 ^ w) ∧
      left.size + right.size < 2 ^ w ∧
      RamInput.cursor (left, right) + left.size + right.size ≤ heapLimit w := by
  have base := width_base admitted
  rw [RamInput.arrayPair_words] at base
  have combinedWidth : 1 + inputWordWidth (left ++ right) ≤ w := by
    have included := inputWordWidth_append_right #[right.size + 1] (left ++ right)
    omega
  have leftWidth : 1 + inputWordWidth left ≤ w := by
    have included := inputWordWidth_append_left left right
    omega
  have rightWidth : 1 + inputWordWidth right ≤ w := by
    have included := inputWordWidth_append_right left right
    omega
  refine ⟨width_pos combinedWidth, cell_lt_word leftWidth,
    cell_lt_word rightWidth, ?_, ?_⟩
  · simpa only [Array.size_append] using size_lt_word combinedWidth
  · have reserved := width_reserve_words large admitted
    have wordsSize : (RamInput.words (left, right)).size = 1 + (left.size + right.size) := by
      simp
    rw [wordsSize] at reserved
    omega

/-- The canonical pair can run the existing allocating append at every admitted
width. Its actual final heap, fresh object, exact cursor growth and old contents
are retained. There is no input-dependent capacity precondition or time budget. -/
theorem arrayPair_append_arenaMeasured {overhead w : Nat} (left right : Array Nat)
    (large : 1 ≤ overhead) (admitted : width overhead (left, right) ≤ w) :
    ArenaMeasured Copy.program w (heapLimit w) 1 (Copy.program.body Copy.appendId)
      (fun finish control finalCursor _ => ∃ target, control = .returned target ∧
        finalCursor = RamInput.cursor (left, right) + left.size + right.size ∧
        target.Contents finish.heap (left ++ right) ∧
        target.object = (Input.heap (left, right)).objects.size ∧
        PreservesContents (Input.heap (left, right)) finish.heap)
      ⟨Input.args (left, right), Input.heap (left, right)⟩
      (RamInput.cursor (left, right)) := by
  obtain ⟨positive, leftFits, rightFits, sizeFits, space⟩ := arrayPair_resources large admitted
  obtain ⟨observedLeft, observedRight⟩ := arrayPair_contents left right
  exact BufferCopy.append_arenaMeasured positive
    (Input.args (left, right)).head (Input.args (left, right)).tail.head
    left right (Input.heap (left, right)) observedLeft observedRight
    leftFits rightFits sizeFits space

end Complexity.Program
