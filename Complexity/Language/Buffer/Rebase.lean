/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Language.Verification.Heap

/-!
# Copying natural offsets relative to a base

The source program allocates actual output storage and subtracts the supplied
base during each real read/write round. Correctness uses ordinary `Array.map`
and the existing copied-prefix and counted-loop proofs. All old views survive,
including overlapping input aliases. This does not price rebasing as a free
slice, nor change the source's truncated natural subtraction into integer subtraction.
-/

namespace Complexity.Language.Buffer

open scoped Std.Do Part.TotalCorrectness

source_program% Rebase where
  def copyInto (source : Buffer Nat) (target : Buffer Nat) (base : Nat) : Unit := do
    for i in [:source.length] do
      let value ← source.get i
      target.set i (value - base)
    return

  def copy (source : Buffer Nat) (base : Nat) : Buffer Nat := do
    let target ← Buffer.alloc source.length 0
    copyInto source target base
    return target

/-- Preserve the source while filling the destination with the rebased prefix. -/
def rebaseInvariant (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) (index : Nat) (heap : Heap) : Prop :=
  index ≤ input.size ∧ source.Contents heap input ∧
    target.Contents heap (copied (input.map (· - base)) output 0 index)

/-- The real length guard observes the remaining source cells. -/
theorem rebase_guard (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) :
    Rebase.copyInto_loop1.guard_contract source target base
      (rebaseInvariant source target base input output) (fun _ _ _ _ => False)
      (fun index heap again next finish => next = index ∧ finish = heap ∧
        rebaseInvariant source target base input output next finish ∧
        (again = true ↔ next < input.size)) := by
  rw [Rebase.copyInto_loop1.guard_contract_iff]
  intro index heap current
  rw [Rebase.copyInto_loop1.guard_eq]
  apply Std.Do.Triple.pure
  intro finish same
  subst finish
  exact ⟨rfl, rfl, current, by simp only [decide_eq_true_eq, current.2.1.size_eq]⟩

/-- A genuine read, subtraction and disjoint write advance the ordinary prefix. -/
theorem rebase_body (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) (separated : target.Disjoint source)
    (extent : input.size ≤ output.size) :
    Rebase.copyInto_loop1.body_contract source target base
      (fun index heap => rebaseInvariant source target base input output index heap ∧
        index < input.size)
      (fun index heap next finish => next = index + 1 ∧
        rebaseInvariant source target base input output next finish ∧
        target.PreservesOutside heap finish)
      (fun _ _ _ _ _ => False) := by
  rw [Rebase.copyInto_loop1.body_contract_iff]
  rintro index heap ⟨current, available⟩
  rw [Rebase.copyInto_loop1.body_eq]
  mvcgen
  rename_i entry same
  subst entry
  refine ⟨input, available, current.2.1, ?_⟩
  mvcgen
  refine ⟨copied (input.map (· - base)) output 0 index,
    by simp only [copied_size]; omega, current.2.2, ?_⟩
  intro finish written updated
  mvcgen
  have advanced : rebaseInvariant source target base input output (index + 1) finish := by
    refine ⟨by omega, current.2.1.write_of_disjoint written separated, ?_⟩
    have step := copied_step (input.map (· - base)) output 0
      (by simpa only [Array.size_map] using available)
      (by simpa only [Array.size_map, Nat.zero_add] using extent)
    simp only [Nat.zero_add, Array.getElem_map] at step
    simpa only [step] using updated
  simpa using And.intro advanced
    (fun {kind : CellTy} => Buffer.PreservesOutside.write written (σ := kind))

/-- Counted-loop composition supplies termination and the transitive write frame. -/
theorem rebase_loop (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) (initial : Heap) (separated : target.Disjoint source)
    (extent : input.size ≤ output.size) :
    Rebase.copyInto_loop1.contract source target base
      (fun index heap => rebaseInvariant source target base input output index heap ∧
        target.PreservesOutside initial heap)
      (fun _ _ _ heap => source.Contents heap input ∧
        target.Contents heap (copied (input.map (· - base)) output 0 input.size) ∧
        target.PreservesOutside initial heap)
      (fun _ _ _ _ _ => False) := by
  simpa only [and_assoc] using Rebase.copyInto_loop1.count_frame_contract source target base
    (fun index => index) input.size (rebaseInvariant source target base input output)
    target.PreservesOutside Buffer.PreservesOutside.trans
    (fun heap => source.Contents heap input ∧
      target.Contents heap (copied (input.map (· - base)) output 0 input.size))
    (rebase_guard source target base input output)
    (rebase_body source target base input output separated extent)
    (fun index heap current finished => by
      have same : index = input.size := Nat.le_antisymm current.1 finished
      exact ⟨current.2.1, same ▸ current.2.2⟩) initial

/-- Copy the rebased values into existing disjoint storage. -/
theorem rebaseInto_spec (source target : Buffer .nat) (base : Nat)
    (input output : Array Nat) (initial : Heap)
    (separated : target.Disjoint source) (extent : input.size ≤ output.size) :
    ⦃fun heap => ⌜source.Contents heap input ∧ target.Contents heap output ∧
      target.PreservesOutside initial heap⌝⦄ Rebase.copyInto source target base
    ⦃⇓ _ finish => ⌜source.Contents finish input ∧
      target.Contents finish (copied (input.map (· - base)) output 0 input.size) ∧
      target.PreservesOutside initial finish⌝⦄ := by
  have loopSpec := Rebase.copyInto_loop1.spec source target base
    (rebase_loop source target base input output initial separated extent)
  rw [Rebase.copyInto_eq]
  mvcgen [loopSpec]
  all_goals simp_all [rebaseInvariant]

/-- The actual copying function's mathematical contract is independent of cost. -/
theorem rebaseInto_total (input output : Array Nat) :
    Rebase.copyInto_contract
      (fun source target _ heap => source.Contents heap input ∧
        target.Contents heap output ∧ target.Disjoint source ∧ input.size ≤ output.size)
      (fun source target base heap _ finish => source.Contents finish input ∧
        target.Contents finish (copied (input.map (· - base)) output 0 input.size) ∧
        target.PreservesOutside heap finish) := by
  apply (Rebase.copyInto_total_iff _ _).mpr
  rintro source target base heap ⟨sourceContents, targetContents, separated, extent⟩
  exact (triple_iff_eval _ _ _).mp
    (rebaseInto_spec source target base input output heap separated extent) heap
    ⟨sourceContents, targetContents, Buffer.PreservesOutside.refl target heap⟩

/-- Actual allocation and filling return the ordinary mapped array in fresh storage. -/
theorem rebase_spec (source : Buffer .nat) (base : Nat) (input : Array Nat) (initial : Heap)
    (observed : source.Contents initial input) :
    ⦃fun heap => ⌜heap = initial⌝⦄ Rebase.copy source base
    ⦃⇓ target finish => ⌜target.Contents finish (input.map (· - base)) ∧
      target.object = initial.objects.size ∧ target.PreservesOutside initial finish⌝⦄ := by
  rw [Rebase.copy_eq]
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
  have innerSpec := Rebase.copyInto_spec
    (rebaseInto_total input (Array.replicate source.length 0)) source target base
  mvcgen [innerSpec]
  simp only [Rebase.copyInto_onArgs, Env.head_cons, Env.tail_cons]
  refine ⟨⟨sourceNow, initialized, separated, ?_⟩, ?_⟩
  · simpa only [Array.size_replicate] using observed.size_eq.le
  · intro value finish sourceKept updated frame
    mvcgen
    refine ⟨?_, fresh, Buffer.PreservesOutside.trans initialFrame frame⟩
    have complete := copied_replicate (input.map (· - base)) (0 : Nat)
    simp only [Array.size_map] at complete
    simpa only [← observed.size_eq, complete] using updated

/-- Rebasing preserves every old view; the result is fresh mutable retained storage. -/
theorem rebase_total (input : Array Nat) :
    Rebase.copy_contract
      (fun source _ heap => source.Contents heap input)
      (fun _ base initial target finish => target.Contents finish (input.map (· - base)) ∧
        target.object = initial.objects.size ∧ PreservesContents initial finish) := by
  apply (Rebase.copy_total_iff _ _).mpr
  intro source base heap observed
  obtain ⟨target, finish, executed, contents, fresh, frame⟩ :=
    (triple_iff_eval _ _ _).mp (rebase_spec source base input heap observed) heap rfl
  exact ⟨target, finish, executed, contents, fresh, preservesContents_of_fresh fresh frame⟩

namespace Rebase

/-- The same source invocation retains contents and heap shape at its real return heap. -/
theorem copy_eval_exists_preserving (input : Array Nat) (source : Buffer .nat)
    (base : Nat) (heap : Heap) (observed : source.Contents heap input) :
    ∃ returned finish,
      copy source base heap = Part.some (.ok returned, finish) ∧
      returned.Contents finish (input.map (· - base)) ∧
      heap.ShapeExtends finish ∧ PreservesContents heap finish := by
  obtain ⟨returned, finish, evaluated, ⟨contents, _, preserved⟩, shape⟩ :=
    (rebase_total input).with_heap_shapeExtends.eval_spec
      (args := Env.cons source (Env.cons base Env.empty)) (initialHeap := heap) observed
  exact ⟨returned, finish, evaluated, contents, shape, preserved⟩

end Rebase
end Complexity.Language.Buffer
