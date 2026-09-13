/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.ArrayFunction
import Complexity.Language.Rooted
import Complexity.Computability.Ram.Compiler.Language.Arena.Basic
import Complexity.Computability.Ram.Compiler.Language.Layout
import Init.Data.List.Nat.Basic

/-!
# Fixed preloaded array inputs

The input array occupies addresses `1` through its length. Address zero holds
the arena cursor, and the upper half of the word address space is reserved for
the stack. These are fixed mathematical initial states, not an executable
loader or an assertion that loading is free. Neither the selected function nor
its proposed answer participates in the representation or width policy.

One extra bit beyond `inputWordWidth` is enough for the initial arena and exact
input values. Code, subsequent allocation and stack capacity remain separate
obligations of an execution theorem.
-/

namespace Ram.LanguageCompiler.ArrayFunction

open Complexity.Language
open Complexity.Language.ArrayFunction

/-- The largest input cell, with zero for an empty input. -/
def inputMax (xs : Array Nat) : Nat := xs.toList.max?.getD 0

/-- A fixed bit-length scale for the input length and its largest value. -/
def inputWordWidth (xs : Array Nat) : Nat :=
  1 + Nat.log2 (xs.size + inputMax xs + 2)

/-- The input object's fixed base. Only object zero exists initially. -/
def placement (w : Nat) : Nat → Word w := fun _ => BitVec.ofNat w 1

/-- The fixed boundary between the arena and the call stack. -/
def heapLimit (w : Nat) : Nat := 2 ^ (w - 1)

/-- The first free address after the input, retaining the metadata cell. -/
def cursor (xs : Array Nat) : Nat := xs.size + 1

/-- A preloaded invocation state with the complete input and arena metadata. -/
def entry (w : Nat) (xs : Array Nat) : Source.State w where
  regs := fun _ => 0
  mem := fun address =>
    if address.toNat = 0 then BitVec.ofNat w (cursor xs)
    else BitVec.ofNat w (xs[address.toNat - 1]?.getD 0)
  input := []
  outputRev := []

/-- Every mathematical input has a positive base width. -/
theorem inputWordWidth_pos (xs : Array Nat) : 0 < inputWordWidth xs := by
  unfold inputWordWidth
  omega

/-- Including every old input word cannot decrease the largest input value. -/
theorem inputMax_mono {xs ys : Array Nat}
    (included : ∀ value, value ∈ xs.toList → value ∈ ys.toList) :
    inputMax xs ≤ inputMax ys := by
  cases found : xs.toList.max? with
  | none => simp [inputMax, found]
  | some value =>
      simpa only [inputMax, found, Option.getD_some] using
        (List.le_max?_getD_of_mem (k := 0) (included value (List.max?_mem found)))

/-- The fixed width scale is monotone in input length and retained word values. -/
theorem inputWordWidth_mono {xs ys : Array Nat} (size : xs.size ≤ ys.size)
    (included : ∀ value, value ∈ xs.toList → value ∈ ys.toList) :
    inputWordWidth xs ≤ inputWordWidth ys := by
  have maximum := inputMax_mono included
  unfold inputWordWidth
  apply Nat.add_le_add_left
  apply (Nat.le_log2 (by omega)).2
  have base := Nat.log2_self_le (n := xs.size + inputMax xs + 2) (by omega)
  omega

/-- Appending words retains the width required by the left input. -/
theorem inputWordWidth_append_left (xs ys : Array Nat) :
    inputWordWidth xs ≤ inputWordWidth (xs ++ ys) := by
  apply inputWordWidth_mono (by simp)
  intro value present
  simp only [Array.toList_append, List.mem_append]
  exact Or.inl present

/-- Appending words retains the width required by the right input. -/
theorem inputWordWidth_append_right (xs ys : Array Nat) :
    inputWordWidth ys ≤ inputWordWidth (xs ++ ys) := by
  apply inputWordWidth_mono (by simp)
  intro value present
  simp only [Array.toList_append, List.mem_append]
  exact Or.inr present

/-- The policy leaves a genuine, nonzero machine word width. -/
theorem width_pos {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : 0 < w := by
  have := inputWordWidth_pos xs
  omega

/-- Every actual input cell is at most the library's standard list maximum. -/
theorem cell_le_inputMax (xs : Array Nat) (index : Nat) (bound : index < xs.size) :
    xs[index] ≤ inputMax xs :=
  List.le_max?_getD_of_mem (Array.getElem_mem_toList bound)

private theorem input_lt_base (xs : Array Nat) :
    xs.size + inputMax xs + 2 < 2 ^ inputWordWidth xs := by
  simpa only [inputWordWidth, Nat.add_comm 1] using
    (Nat.lt_log2_self (n := xs.size + inputMax xs + 2))

/-- The fixed input scale accommodates its length together with any represented
structural extent, such as the cursor of an already preloaded input layout. -/
theorem size_add_max_lt_heapLimit {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : xs.size + inputMax xs + 2 < heapLimit w := by
  have base := input_lt_base xs
  have grows : 2 ^ inputWordWidth xs ≤ 2 ^ (w - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact base.trans_le grows

/-- The initial cursor fits strictly inside the fixed lower-half arena. -/
theorem cursor_lt_heapLimit {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : cursor xs < heapLimit w := by
  have base := input_lt_base xs
  have grows : 2 ^ inputWordWidth xs ≤ 2 ^ (w - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold cursor heapLimit
  omega

/-- The input plus its metadata always fits the initial arena. -/
theorem cursor_le_heapLimit {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : cursor xs ≤ heapLimit w :=
  Nat.le_of_lt (cursor_lt_heapLimit width)

/-- The arena boundary itself is an exact word address. -/
theorem heapLimit_lt_word {w : Nat} (positive : 0 < w) : heapLimit w < 2 ^ w :=
  Nat.pow_lt_pow_right (by decide) (by omega)

/-- The input length is represented exactly, including for an empty array. -/
theorem size_lt_word {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : xs.size < 2 ^ w := by
  have fits := cursor_le_heapLimit width
  have limit := heapLimit_lt_word (width_pos width)
  unfold cursor at fits
  omega

/-- Every supplied natural cell is represented exactly, not modulo the word width. -/
theorem cell_lt_word {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) (index : Nat) (bound : index < xs.size) :
    xs[index] < 2 ^ w := by
  have cell := cell_le_inputMax xs index bound
  have base := input_lt_base xs
  have grows : 2 ^ inputWordWidth xs ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The canonical source argument meets the existing backend range predicate. -/
theorem inputArgs_fits {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) : EnvFits w (inputArgs xs) := by
  simpa only [inputArgs, EnvFits.cons_buffer_iff, inputBuffer, EnvFits.empty, and_true]
    using size_lt_word width

/-- The input view names the sole existing source object. -/
theorem inputArgs_rooted (xs : Array Nat) : (inputArgs xs).Rooted (inputHeap xs) := by
  simp [inputArgs, Env.Rooted.cons_iff, ValueRooted, Buffer.Rooted, inputBuffer, inputHeap]

private theorem inputHeap_object_eq {xs : Array Nat} {id : Nat} {object : HeapObject}
    (found : (inputHeap xs).objects[id]? = some object) :
    id = 0 ∧ object = .buffer .nat xs := by
  have bound := (Array.getElem?_eq_some_iff.mp found).choose
  have zero : id = 0 := by
    change id < 1 at bound
    omega
  refine ⟨zero, ?_⟩
  subst id
  simpa [inputHeap] using found.symm

private theorem placement_toNat {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) (object : Nat) :
    (placement w object).toNat = 1 :=
  Word.ofNat_toNat_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt (width_pos width)))

private theorem input_arrayAt {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) :
    Source.ArrayAt (heapLimit w) (placement w 0)
      (objectWords w (τ := .nat) xs).toList (entry w xs) := by
  have placed := placement_toNat width 0
  have capacity := cursor_le_heapLimit width
  have limit := heapLimit_lt_word (width_pos width)
  have length : (objectWords w (τ := .nat) xs).toList.length = xs.size := by
    simp [objectWords]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [placed, length]
    unfold cursor at capacity
    omega
  · intro index bound
    have inBounds : index < xs.size := by simpa only [length] using bound
    have address : (arrayAddr (placement w 0) index).toNat = 1 + index := by
      rw [arrayAddr_toNat, placed]
      rw [placed]
      unfold cursor at capacity
      omega
    simp only [entry, address, Nat.add_sub_cancel_left, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, false_and, ↓reduceIte, Array.getElem?_eq_getElem inBounds,
      Option.getD_some, objectWords, Array.getElem_toList, Array.getElem_map,
      cellWord, cellToNat]
  · rw [placed, length]
    simpa only [cursor, Nat.add_comm] using capacity

/-- The fixed physical input represents the complete source heap and a valid
arena cursor. This establishes initialization without assuming candidate behavior. -/
theorem input_arenaRep {xs : Array Nat} {w : Nat}
    (width : 1 + inputWordWidth xs ≤ w) :
    ArenaRep (placement w) (cursor xs) (heapLimit w) (inputHeap xs) (entry w xs) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by unfold cursor; omega,
    cursor_le_heapLimit width, heapLimit_lt_word (width_pos width), ?_, ?_⟩
  · intro id object found
    obtain ⟨rfl, rfl⟩ := inputHeap_object_eq found
    exact input_arrayAt width
  · intro id object found
    obtain ⟨rfl, rfl⟩ := inputHeap_object_eq found
    intro index bound
    exact cell_lt_word width index bound
  · intro id other object otherObject found otherFound different
    exact (different ((inputHeap_object_eq found).1.trans
      (inputHeap_object_eq otherFound).1.symm)).elim
  · intro kind id head tail found
    have impossible := (inputHeap_object_eq (Heap.node?_eq_some_iff.mp found)).2
    cases impossible
  · simp [entry]
  · intro id object found index bound
    obtain ⟨rfl, rfl⟩ := inputHeap_object_eq found
    have inBounds : index < xs.size := by
      simpa only [heapObjectWords_buffer_size] using bound
    have address := (input_arrayAt width).1.addr_toNat
      (by simpa only [objectWords, Array.length_toList, Array.size_map] using inBounds)
    rw [placement_toNat width] at address
    rw [address]
    unfold cursor
    constructor <;> omega

end Ram.LanguageCompiler.ArrayFunction
