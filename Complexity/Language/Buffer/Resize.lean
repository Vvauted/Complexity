/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Init.Data.Array.Extract

/-!
# Resizing borrowed buffers into fresh storage

`Resize.resize` allocates initialized storage of the requested length, then
calls the existing source copy routine. Shrinking first forms a borrowed prefix
view; growing copies the original contents and retains the initialized suffix.
The source declaration contains the actual allocation, slice and copying calls.

The mathematical result is an ordinary array prefix followed by zero padding.
Every old contents observation is preserved, including aliases of the input.
The result is a borrowed handle to fresh retained storage: its contents contract
describes the actual return heap, not permanent immutability. Correctness and
termination impose no machine capacity or time-budget premise.
-/

namespace Complexity.Language.Buffer

open scoped Std.Do Part.TotalCorrectness

/-- A fitting relative slice observes the corresponding ordinary array extract
in the same heap. Its descriptor is the one returned by `Buffer.slice_eq`. -/
theorem Contents.slice {kind : CellTy} {buffer : Buffer kind} {heap : Heap}
    {contents : Array (CellValue kind)} (observed : buffer.Contents heap contents)
    {offset length : Nat} (bound : offset + length ≤ buffer.length) :
    (⟨buffer.object, buffer.offset + offset, length⟩ : Buffer kind).Contents
      heap (contents.extract offset (offset + length)) := by
  obtain ⟨values, found, extent, rfl⟩ := observed
  refine ⟨values, found, by dsimp; omega, ?_⟩
  change
    (values.extract buffer.offset (buffer.offset + buffer.length)).extract
        offset (offset + length) =
      values.extract (buffer.offset + offset) ((buffer.offset + offset) + length)
  have stopBound : buffer.offset + (offset + length) ≤ buffer.offset + buffer.length := by
    omega
  simp only [Array.extract_extract, Nat.min_eq_left stopBound, Nat.add_assoc]

/-- Copying into a longer initialized array leaves its initialized suffix.
This is ordinary array mathematics, not a second resize implementation. -/
theorem copied_replicate_extend {α : Type} (input : Array α) (length : Nat)
    (initial : α) (fits : input.size ≤ length) :
    copied input (Array.replicate length initial) 0 input.size =
      input ++ Array.replicate (length - input.size) initial := by
  apply Array.ext
  · simp only [copied_size, Array.size_replicate, Array.size_append]
    omega
  intro index leftBound rightBound
  by_cases inside : index < input.size
  · have active : 0 ≤ index ∧ index < 0 + input.size ∧ index - 0 < input.size := by
      omega
    simp only [copied, Array.getElem_mapIdx]
    rw [dif_pos active, Array.getElem_append_left inside]
    simp only [Nat.sub_zero]
  · have inactive : ¬(0 ≤ index ∧ index < 0 + input.size ∧ index - 0 < input.size) := by
      omega
    simp only [copied, Array.getElem_mapIdx]
    rw [dif_neg inactive, Array.getElem_append_right (by omega : input.size ≤ index)]
    simp only [Array.getElem_replicate]

source_program Resize importing Copy where
  def resize (source : Buffer Nat) (length : Nat) : Buffer Nat := do
    let target ← Buffer.alloc length 0
    if source.length ≤ length then
      Copy.copyInto source target 0
    else
      let retainedPrefix ← source.slice 0 length
      Copy.copyInto retainedPrefix target 0
    return target

/-- The actual source resize returns the requested prefix and zero padding in
fresh storage, framing every view outside that storage in the arbitrary entry heap. -/
theorem resize_spec (source : Buffer .nat) (length : Nat) (input : Array Nat)
    (initial : Heap) (observed : source.Contents initial input) :
    ⦃fun heap => ⌜heap = initial⌝⦄ Resize.resize source length
    ⦃⇓ target finish => ⌜target.Contents finish
        (input.extract 0 length ++ Array.replicate (length - input.size) 0) ∧
      target.object = initial.objects.size ∧ target.PreservesOutside initial finish⌝⦄ := by
  rw [Resize.resize_eq]
  mvcgen
  rename_i heap same
  subst heap
  intro target allocated allocation initialized shape fresh
  have sourceNow : source.Contents allocated input := by
    simpa only [allocation] using observed.alloc (τ := .nat) length 0
  have initialFrame : target.PreservesOutside initial allocated := by
    intro kind other values separated contents
    simpa only [allocation] using contents.alloc (τ := .nat) length 0
  have separated : target.Disjoint source :=
    Or.inl (by rw [fresh]; exact Nat.ne_of_gt observed.valid.rooted)
  by_cases enough : source.length ≤ length
  · have inputBound : input.size ≤ length := by
      simpa only [observed.size_eq] using enough
    have callSpec := Copy.copyInto_spec
      (copyInto_total input (Array.replicate length 0)) source target 0
    simp only [enough, decide_true, if_true]
    mvcgen [callSpec]
    simp only [Copy.copyInto_onArgs, Env.head_cons, Env.tail_cons]
    refine ⟨⟨sourceNow, initialized, separated, ?_⟩, ?_⟩
    · simpa only [Nat.zero_add, Array.size_replicate] using inputBound
    · intro value finish sourceKept updated frame
      mvcgen
      refine ⟨?_, fresh, Buffer.PreservesOutside.trans initialFrame frame⟩
      simpa only [copied_replicate_extend input length 0 inputBound,
        Array.extract_eq_self_of_le inputBound] using updated
  · have prefixBound : length ≤ source.length := by omega
    have inputBound : length ≤ input.size := by
      simpa only [observed.size_eq] using prefixBound
    let retainedPrefix : Buffer .nat := ⟨source.object, source.offset + 0, length⟩
    have prefixNow : retainedPrefix.Contents allocated (input.extract 0 length) := by
      simpa only [retainedPrefix, Nat.zero_add] using
        sourceNow.slice (offset := 0) (length := length) (by omega)
    have prefixSize : (input.extract 0 length).size = length := by
      simp only [Array.size_extract, Nat.min_eq_left inputBound, Nat.sub_zero]
    have separatedPrefix : target.Disjoint retainedPrefix := by
      apply Or.inl
      change target.object ≠ source.object
      rw [fresh]
      exact Nat.ne_of_gt observed.valid.rooted
    have sliced : source.sliceM 0 length =
        (pure retainedPrefix : ExceptT Fault (StateT Heap Part) (Buffer .nat)) := by
      funext current
      exact Buffer.sliceM_eq_ok (source.slice_eq (by omega)) current
    have callSpec := Copy.copyInto_spec
      (copyInto_total (input.extract 0 length) (Array.replicate length 0)) retainedPrefix target 0
    simp only [enough, decide_false, Bool.false_eq_true, if_false, sliced, pure_bind]
    mvcgen [callSpec]
    simp only [Copy.copyInto_onArgs, Env.head_cons, Env.tail_cons]
    refine ⟨⟨prefixNow, initialized, separatedPrefix, ?_⟩, ?_⟩
    · simp only [Nat.zero_add, prefixSize, Array.size_replicate]
      exact Nat.le_refl _
    · intro value finish prefixKept updated frame
      mvcgen
      refine ⟨?_, fresh, Buffer.PreservesOutside.trans initialFrame frame⟩
      have filled : copied (input.extract 0 length) (Array.replicate length 0) 0
          (input.extract 0 length).size = input.extract 0 length := by
        simpa only [prefixSize] using copied_replicate (input.extract 0 length) (0 : Nat)
      simpa only [filled, Nat.sub_eq_zero_of_le inputBound, Array.replicate_zero,
        Array.append_empty] using updated

/-- Resize has the ordinary array-prefix/zero-padding result, successful
termination, fresh returned storage and preservation of every old contents observation.
The returned storage remains mutable; this is not a persistent-value interface. -/
theorem resize_total (input : Array Nat) :
    Resize.resize_contract
      (fun source _ heap => source.Contents heap input)
      (fun _ length initial target finish => target.Contents finish
          (input.extract 0 length ++ Array.replicate (length - input.size) 0) ∧
        target.object = initial.objects.size ∧ PreservesContents initial finish) := by
  apply (Resize.resize_total_iff _ _).mpr
  intro source length heap observed
  obtain ⟨target, finish, executed, contents, fresh, frame⟩ :=
    (triple_iff_eval _ _ _).mp (resize_spec source length input heap observed) heap rfl
  exact ⟨target, finish, executed, contents, fresh, preservesContents_of_fresh fresh frame⟩

end Complexity.Language.Buffer
