/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Locals.Verification
import Complexity.Language.Heap.Prefix
import Complexity.Language.Heap.Tactic
import Complexity.Control.Triple
import Init.Data.Array.MapIdx
import Std.Tactic.Do

/-!
# Copying borrowed scalar buffers into fresh storage

The source declarations below perform their actual allocations, reads and writes.
`Copy.copyInto` copies into a disjoint destination; `Copy.copy` and `Copy.append`
allocate that destination themselves. Their specifications use ordinary native
arrays and preserve every initially observed view, including overlapping inputs.

The returned value is a borrowed handle to fresh, retained arena storage. Its
contents assertion describes the actual return heap, not permanent immutability.
This module currently instantiates the source interface at natural-number cells.
-/

namespace Complexity.Language.Buffer

open scoped Std.Do Part.TotalCorrectness

source_program Copy where
  def copyInto (source : Buffer Nat) (target : Buffer Nat) (offset : Nat) : Unit := do
    for i in [:source.length] do
      let value ← source.get i
      target.set (offset + i) value
    return

  def copy (source : Buffer Nat) : Buffer Nat := do
    let target ← Buffer.alloc source.length 0
    copyInto source target 0
    return target

  def append (left : Buffer Nat) (right : Buffer Nat) : Buffer Nat := do
    let target ← Buffer.alloc (left.length + right.length) 0
    copyInto left target 0
    copyInto right target left.length
    return target

/-- The already-copied segment, expressed with native indexed array mapping.
The bounds test makes this mathematical view total even away from the invariant. -/
def copied {α : Type} (source target : Array α) (offset count : Nat) : Array α :=
  target.mapIdx fun index previous =>
    if bound : offset ≤ index ∧ index < offset + count ∧ index - offset < source.size then
      source[index - offset]
    else previous

@[simp] theorem copied_size {α : Type} (source target : Array α) (offset count : Nat) :
    (copied source target offset count).size = target.size := by
  simp only [copied, Array.size_mapIdx]

@[simp] theorem copied_zero {α : Type} (source target : Array α) (offset : Nat) :
    copied source target offset 0 = target := by
  apply Array.ext (by simp)
  intro index leftBound rightBound
  have outside : ¬(offset ≤ index ∧ index < offset + 0 ∧ index - offset < source.size) := by
    omega
  simp only [copied, Array.getElem_mapIdx, dif_neg outside]

/-- One actual target write advances the mathematical copied segment. -/
theorem copied_step {α : Type} (source target : Array α) (offset : Nat)
    {index : Nat} (available : index < source.size)
    (extent : offset + source.size ≤ target.size) :
    (copied source target offset index).set (offset + index) source[index]
        (by simp only [copied_size]; omega) =
      copied source target offset (index + 1) := by
  apply Array.ext (by simp)
  intro next leftBound rightBound
  simp only [Array.getElem_set, copied, Array.getElem_mapIdx]
  by_cases same : offset + index = next
  · subst next
    have active : offset ≤ offset + index ∧ offset + index < offset + (index + 1) ∧
        offset + index - offset < source.size := by omega
    rw [if_pos rfl, dif_pos active]
    simp only [Nat.add_sub_cancel_left]
  · have active :
        (offset ≤ next ∧ next < offset + (index + 1) ∧ next - offset < source.size) ↔
        (offset ≤ next ∧ next < offset + index ∧ next - offset < source.size) := by omega
    simp only [if_neg same, active]

/-- Copying an entire array over equally-sized initialized storage gives that array. -/
theorem copied_replicate {α : Type} (source : Array α) (initial : α) :
    copied source (Array.replicate source.size initial) 0 source.size = source := by
  apply Array.ext (by simp)
  intro index leftBound rightBound
  have active : 0 ≤ index ∧ index < 0 + source.size ∧ index - 0 < source.size := by omega
  simp only [copied, Array.getElem_mapIdx]
  rw [dif_pos active]
  simp only [Nat.sub_zero]

/-- The two disjoint copied segments are the ordinary native append. -/
theorem copied_append {α : Type} (left right : Array α) (initial : α) :
    copied right
      (copied left (Array.replicate (left.size + right.size) initial) 0 left.size)
      left.size right.size = left ++ right := by
  apply Array.ext (by simp)
  intro index leftBound rightBound
  have bound : index < left.size + right.size := by
    simpa only [Array.size_append] using rightBound
  by_cases first : index < left.size
  · have inactive : ¬(left.size ≤ index ∧ index < left.size + right.size ∧
        index - left.size < right.size) := by omega
    have active : 0 ≤ index ∧ index < 0 + left.size ∧ index - 0 < left.size := by omega
    simp only [copied, Array.getElem_mapIdx]
    rw [dif_neg inactive, dif_pos active, Array.getElem_append_left first]
    simp only [Nat.sub_zero]
  · have active : left.size ≤ index ∧ index < left.size + right.size ∧
        index - left.size < right.size := by omega
    simp only [copied, Array.getElem_mapIdx]
    rw [dif_pos active, Array.getElem_append_right (by omega : left.size ≤ index)]

/-- A caller's old observations, without requiring those old views to be disjoint. -/
def PreservesContents (initial finish : Heap) : Prop :=
  ∀ {kind : CellTy} (view : Buffer kind) (values : Array (CellValue kind)),
    view.Contents initial values → view.Contents finish values

/-- Fresh-result framing preserves every old alias, not merely the named inputs. -/
theorem preservesContents_of_fresh {initial finish : Heap} {kind : CellTy}
    {target : Buffer kind} (fresh : target.object = initial.objects.size)
    (frame : target.PreservesOutside initial finish) : PreservesContents initial finish := by
  intro otherKind view values observed
  apply frame view values
  · exact Or.inl (by rw [fresh]; exact Nat.ne_of_gt observed.valid.rooted)
  · exact observed

private def copyInvariant (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) (index : Nat) (heap : Heap) : Prop :=
  index ≤ input.size ∧ source.Contents heap input ∧
    target.Contents heap (copied input output offset index)

private theorem copyInvariant_done (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) {index : Nat} {heap : Heap}
    (current : copyInvariant source target offset input output index heap)
    (finished : input.size ≤ index) :
    source.Contents heap input ∧
      target.Contents heap (copied input output offset input.size) := by
  have complete : index = input.size := Nat.le_antisymm current.1 finished
  exact ⟨current.2.1, complete ▸ current.2.2⟩

private theorem copy_guard (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) :
    Copy.copyInto_loop1.guard_contract source target offset
      (copyInvariant source target offset input output) (fun _ _ _ _ => False)
      (fun index heap again next finish => next = index ∧ finish = heap ∧
        copyInvariant source target offset input output next finish ∧
        (again = true ↔ next < input.size)) := by
  rw [Copy.copyInto_loop1.guard_contract_iff]
  intro index heap current
  rw [Copy.copyInto_loop1.guard_eq]
  apply Std.Do.Triple.pure
  intro finish same
  subst finish
  exact ⟨rfl, rfl, current, by simp only [decide_eq_true_eq, current.2.1.size_eq]⟩

private theorem copy_body (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) (separated : target.Disjoint source)
    (extent : offset + input.size ≤ output.size) :
    Copy.copyInto_loop1.body_contract source target offset
      (fun index heap => copyInvariant source target offset input output index heap ∧
        index < input.size)
      (fun index heap next finish => next = index + 1 ∧
        copyInvariant source target offset input output next finish ∧
        target.PreservesOutside heap finish)
      (fun _ _ _ _ _ => False) := by
  rw [Copy.copyInto_loop1.body_contract_iff]
  rintro index heap ⟨current, available⟩
  rw [Copy.copyInto_loop1.body_eq]
  mvcgen
  rename_i entry same
  subst entry
  refine ⟨input, available, current.2.1, ?_⟩
  mvcgen
  refine ⟨copied input output offset index, by simp only [copied_size]; omega,
    current.2.2, ?_⟩
  intro finish written updated
  mvcgen
  have advanced : copyInvariant source target offset input output (index + 1) finish := by
    refine ⟨by omega, current.2.1.write_of_disjoint written separated, ?_⟩
    simpa only [copied_step input output offset available extent] using updated
  simpa using And.intro advanced
    (fun {kind : CellTy} => Buffer.PreservesOutside.write written (σ := kind))

private theorem copy_loop (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) (initial : Heap) (separated : target.Disjoint source)
    (extent : offset + input.size ≤ output.size) :
    Copy.copyInto_loop1.contract source target offset
      (fun index heap => copyInvariant source target offset input output index heap ∧
        target.PreservesOutside initial heap)
      (fun _ _ _ heap => source.Contents heap input ∧
        target.Contents heap (copied input output offset input.size) ∧
        target.PreservesOutside initial heap)
      (fun _ _ _ _ _ => False) := by
  refine Copy.copyInto_loop1.variant_contract source target offset
    (fun index heap => copyInvariant source target offset input output index heap ∧
      target.PreservesOutside initial heap)
    (fun index _ => input.size - index)
    (fun index heap next finish => next = index ∧ finish = heap ∧ next < input.size)
    (fun _ heap => source.Contents heap input ∧
      target.Contents heap (copied input output offset input.size) ∧
      target.PreservesOutside initial heap) (fun _ _ _ => False) ?_ ?_
  · apply Stmt.BlockSpec.mono (copy_guard source target offset input output)
    · intro _ _ current; exact current.1
    · intro _ _ _ _ _ impossible; exact impossible
    · intro start heap again finish finalHeap current tested
      rcases tested with ⟨sameIndex, rfl, prefixState, available⟩
      by_cases active : again = true
      · simp only [if_pos active]
        exact ⟨sameIndex, trivial, available.mp active⟩
      · simp only [if_neg active]
        have complete := copyInvariant_done source target offset input output prefixState
          (Nat.le_of_not_gt (fun bound => active (available.mpr bound)))
        exact ⟨complete.1, complete.2, current.2⟩
  · intro index heap current
    apply Stmt.BlockSpec.mono (copy_body source target offset input output separated extent)
    · rintro start afterGuard ⟨sameIndex, rfl, active⟩
      exact ⟨by simpa only [sameIndex] using current.1, active⟩
    · rintro start afterGuard finish finalHeap ⟨sameIndex, rfl, available⟩
        ⟨next, updated, preserved⟩
      exact ⟨⟨updated, Buffer.PreservesOutside.trans current.2 preserved⟩,
        by dsimp only; omega⟩
    · intro _ _ _ _ _ _ impossible; exact impossible

/-- Copy the source into the specified target interval. The source and all
views disjoint from the target retain their actual contents. -/
theorem copyInto_spec (source target : Buffer .nat) (offset : Nat)
    (input output : Array Nat) (initial : Heap)
    (separated : target.Disjoint source) (extent : offset + input.size ≤ output.size) :
    ⦃fun heap => ⌜source.Contents heap input ∧ target.Contents heap output ∧
      target.PreservesOutside initial heap⌝⦄ Copy.copyInto source target offset
    ⦃⇓ _ finish => ⌜source.Contents finish input ∧
      target.Contents finish (copied input output offset input.size) ∧
      target.PreservesOutside initial finish⌝⦄ := by
  have loopSpec := Copy.copyInto_loop1.spec source target offset
    (copy_loop source target offset input output initial separated extent)
  rw [Copy.copyInto_eq]
  mvcgen [loopSpec]
  all_goals simp_all [copyInvariant]

/-- The same source copy loop has a callable mathematical array/frame contract. -/
theorem copyInto_total (input output : Array Nat) :
    Copy.copyInto_contract
      (fun source target offset heap => source.Contents heap input ∧
        target.Contents heap output ∧ target.Disjoint source ∧
        offset + input.size ≤ output.size)
      (fun source target offset heap _ finish => source.Contents finish input ∧
        target.Contents finish (copied input output offset input.size) ∧
        target.PreservesOutside heap finish) := by
  apply (Copy.copyInto_total_iff _ _).mpr
  rintro source target offset heap ⟨sourceContents, targetContents, separated, extent⟩
  exact (triple_iff_eval _ _ _).mp
    (copyInto_spec source target offset input output heap separated extent) heap
    ⟨sourceContents, targetContents, Buffer.PreservesOutside.refl target heap⟩

/-- Allocation and the actual copying call produce a fresh retained view.
Every outside observation is framed relative to the arbitrary entry heap. -/
theorem copy_spec (source : Buffer .nat) (input : Array Nat) (initial : Heap)
    (observed : source.Contents initial input) :
    ⦃fun heap => ⌜heap = initial⌝⦄ Copy.copy source
    ⦃⇓ target finish => ⌜target.Contents finish input ∧
      target.object = initial.objects.size ∧ target.PreservesOutside initial finish⌝⦄ := by
  rw [Copy.copy_eq]
  mvcgen
  rename_i heap same
  subst heap
  intro target allocated allocation initialized shape fresh
  have sourceNow : source.Contents allocated input := by
    simpa only [allocation] using observed.alloc (τ := .nat) source.length 0
  have initialFrame : target.PreservesOutside initial allocated := by
    intro kind other values separated contents
    simpa only [allocation] using contents.alloc (τ := .nat) source.length 0
  have separated : target.Disjoint source :=
    Or.inl (by rw [fresh]; exact Nat.ne_of_gt observed.valid.rooted)
  have innerSpec := Copy.copyInto_spec
    (copyInto_total input (Array.replicate source.length 0)) source target 0
  mvcgen [innerSpec]
  simp only [Copy.copyInto_onArgs, Env.head_cons, Env.tail_cons]
  refine ⟨⟨sourceNow, initialized, separated, ?_⟩, ?_⟩
  · simp only [Array.size_replicate, Nat.zero_add]
    exact observed.size_eq.le
  · intro value finish sourceKept updated frame
    mvcgen
    refine ⟨?_, fresh, Buffer.PreservesOutside.trans initialFrame frame⟩
    simpa only [← observed.size_eq, copied_replicate] using updated

/-- Copying preserves all old aliases and returns fresh storage containing the
same ordinary array. This does not grant permanent immutability of that storage. -/
theorem copy_total (input : Array Nat) :
    Copy.copy_contract
      (fun source heap => source.Contents heap input)
      (fun _ initial target finish => target.Contents finish input ∧
        target.object = initial.objects.size ∧ PreservesContents initial finish) := by
  apply (Copy.copy_total_iff _ _).mpr
  intro source heap observed
  obtain ⟨target, finish, executed, contents, fresh, frame⟩ :=
    (triple_iff_eval _ _ _).mp (copy_spec source input heap observed) heap rfl
  exact ⟨target, finish, executed, contents, fresh, preservesContents_of_fresh fresh frame⟩

/-- Two actual copying calls fill a fresh result with native array append.
The left and right inputs may coincide or be overlapping views. -/
theorem append_spec (left right : Buffer .nat) (leftValues rightValues : Array Nat)
    (initial : Heap) (observedLeft : left.Contents initial leftValues)
    (observedRight : right.Contents initial rightValues) :
    ⦃fun heap => ⌜heap = initial⌝⦄ Copy.append left right
    ⦃⇓ target finish => ⌜target.Contents finish (leftValues ++ rightValues) ∧
      target.object = initial.objects.size ∧ target.PreservesOutside initial finish⌝⦄ := by
  rw [Copy.append_eq]
  mvcgen
  rename_i heap same
  subst heap
  intro target allocated allocation initialized shape fresh
  simp only [Nat.add_eq] at allocation
  let initialValues : Array Nat := Array.replicate (left.length + right.length) 0
  have leftNow : left.Contents allocated leftValues := by
    simpa only [allocation] using observedLeft.alloc (τ := .nat) (left.length + right.length) 0
  have rightNow : right.Contents allocated rightValues := by
    simpa only [allocation] using observedRight.alloc (τ := .nat) (left.length + right.length) 0
  have initialFrame : target.PreservesOutside initial allocated := by
    intro kind other values separated contents
    simpa only [allocation] using contents.alloc (τ := .nat) (left.length + right.length) 0
  have separatedLeft : target.Disjoint left :=
    Or.inl (by rw [fresh]; exact Nat.ne_of_gt observedLeft.valid.rooted)
  have separatedRight : target.Disjoint right :=
    Or.inl (by rw [fresh]; exact Nat.ne_of_gt observedRight.valid.rooted)
  have leftSpec := Copy.copyInto_spec (copyInto_total leftValues initialValues) left target 0
  mvcgen [leftSpec]
  simp only [Copy.copyInto_onArgs, Env.head_cons, Env.tail_cons]
  refine ⟨⟨leftNow, initialized, separatedLeft, ?_⟩, ?_⟩
  · simp only [initialValues, Array.size_replicate, Nat.zero_add, observedLeft.size_eq]
    omega
  · intro value middle leftKept copiedLeft frameLeft
    have rightSpec := Copy.copyInto_spec
      (copyInto_total rightValues (copied leftValues initialValues 0 leftValues.size))
      right target left.length
    mvcgen [rightSpec]
    simp only [Copy.copyInto_onArgs, Env.head_cons, Env.tail_cons]
    refine ⟨⟨?_, copiedLeft, separatedRight, ?_⟩, ?_⟩
    · buffer_frame
    · simp only [copied_size, initialValues, Array.size_replicate, observedRight.size_eq]
      exact Nat.le_refl _
    · intro value finish rightKept appended frameRight
      mvcgen
      refine ⟨?_, fresh, ?_⟩
      · simpa only [initialValues, ← observedLeft.size_eq, ← observedRight.size_eq,
          copied_append] using appended
      · buffer_frame

/-- Public append uses ordinary `Array.append`, fresh output storage, and an
arbitrary-old-heap frame. No separation assumption is imposed between inputs. -/
theorem append_total (leftValues rightValues : Array Nat) :
    Copy.append_contract
      (fun left right heap => left.Contents heap leftValues ∧ right.Contents heap rightValues)
      (fun _ _ initial target finish => target.Contents finish (leftValues ++ rightValues) ∧
        target.object = initial.objects.size ∧ PreservesContents initial finish) := by
  apply (Copy.append_total_iff _ _).mpr
  rintro left right heap ⟨observedLeft, observedRight⟩
  obtain ⟨target, finish, executed, contents, fresh, frame⟩ :=
    (triple_iff_eval _ _ _).mp
      (append_spec left right leftValues rightValues heap observedLeft observedRight) heap rfl
  exact ⟨target, finish, executed, contents, fresh, preservesContents_of_fresh fresh frame⟩

end Complexity.Language.Buffer
