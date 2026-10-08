/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prepare
import Complexity.Analysis.Amortized.Geometric

/-!
# Reusable current-request buffers

A protocol carries its own cache explicitly. A request fitting the cached
allocation overwrites that allocation's prefix; a larger request allocates the
geometrically grown capacity. The returned view has exactly the current request's
length. The cache is never selected existentially from candidate-owned storage.

The current view is borrowed and may be overwritten by a later preparation.
Disjoint candidate-owned contents and all existing object shapes survive.
Growth does not reclaim candidate allocations or invalidate their identities.
External traversal and transport remain outside these source-operation relations.
-/

namespace Complexity.Language.Buffer.PrepareReuse

open Complexity.Language.Buffer

/-- A protocol-owned allocation retained between requests. -/
abbrev Cache := Option (Buffer .nat)

/-- The physical cell capacity retained by the protocol. -/
def capacity : Cache → Nat
  | none => 0
  | some buffer => buffer.length

/-- A cache must still name its actual valid allocation at the current heap. -/
def Valid (cache : Cache) (heap : Heap) : Prop :=
  ∀ buffer, cache = some buffer → buffer.Valid heap

/-- Initial preparation allocates even for an empty request; later requests
allocate only when the actual retained capacity is insufficient. -/
def NeedsGrowth (cache : Cache) (length : Nat) : Prop :=
  cache = none ∨ capacity cache < length

instance (cache : Cache) (length : Nat) : Decidable (NeedsGrowth cache length) :=
  inferInstanceAs (Decidable (cache = none ∨ capacity cache < length))

/-- Descriptor of the current prefix; no cells are copied by forming this view. -/
def requestView (buffer : Buffer .nat) (length : Nat) : Buffer .nat :=
  ⟨buffer.object, buffer.offset, length⟩

/-- A fitting request view is valid in the cache's actual heap. -/
theorem valid_prefix {buffer : Buffer .nat} {heap : Heap} {length : Nat}
    (valid : buffer.Valid heap) (bound : length ≤ buffer.length) :
    (requestView buffer length).Valid heap := by
  simpa only [requestView, Nat.add_zero] using valid.slice (offset := 0) (length := length)
    (by omega)

/-- Cell writes preserve every observation disjoint from their real target. -/
theorem fill_frame {values : Array Nat} {buffer : Buffer .nat}
    {count : Nat} {heap finish : Heap}
    (run : Prepare.Fill values buffer count heap finish) :
    buffer.PreservesOutside heap finish := by
  induction run with
  | zero => exact Buffer.PreservesOutside.refl _ _
  | succ rest bound written ih =>
      exact Buffer.PreservesOutside.trans ih (Buffer.PreservesOutside.write written)

/-- The exact retained buffer is reused, or a real initialized allocation is
made according to the fixed growth policy before writing the current request. -/
inductive Run (values : Array Nat) : Cache → Heap → Cache → Buffer .nat → Heap → Prop
  | reuse {buffer heap finish}
      (valid : buffer.Valid heap) (fits : values.size ≤ buffer.length)
      (filled : Prepare.Fill values (requestView buffer values.size) values.size heap finish) :
      Run values (some buffer) heap (some buffer) (requestView buffer values.size) finish
  | grow {cache heap allocated buffer finish}
      (needed : NeedsGrowth cache values.size)
      (called : Replicate.program.eval Replicate.replicateNatId
        (Replicate.replicateNat_args
          (Complexity.GeometricCapacity.next (capacity cache) values.size) 0) heap =
        Part.some (.ok buffer, allocated))
      (filled : Prepare.Fill values (requestView buffer values.size) values.size allocated finish) :
      Run values cache heap (some buffer) (requestView buffer values.size) finish

private theorem allocated_eq {length : Nat} {heap allocated : Heap} {buffer : Buffer .nat}
    (called : Replicate.program.eval Replicate.replicateNatId
      (Replicate.replicateNat_args length 0) heap = Part.some (.ok buffer, allocated)) :
    buffer = (heap.alloc (τ := .nat) length 0).1 ∧
      allocated = (heap.alloc (τ := .nat) length 0).2 := by
  rw [Replicate.replicateNat_observe, Replicate.replicateNat_eval] at called
  have same := Part.some_injective called
  exact ⟨(Except.ok.inj (congrArg Prod.fst same)).symm, (congrArg Prod.snd same).symm⟩

/-- Preparation exposes the actual request, retains cache validity, and preserves
all existing shapes and contents outside the borrowed current view. -/
theorem Run.observed {values : Array Nat} {cache nextCache : Cache}
    {heap finish : Heap} {view : Buffer .nat}
    (run : Run values cache heap nextCache view finish) :
    view.Contents finish values ∧ Valid nextCache finish ∧
      heap.ShapeExtends finish ∧ view.PreservesOutside heap finish := by
  cases run with
  | reuse valid fits filled =>
      refine ⟨Contents.of_read ((valid_prefix valid fits).mono filled.shape) rfl
        (fun _ bound => filled.read bound bound), ?_, filled.shape, fill_frame filled⟩
      intro other same
      cases Option.some.inj same
      exact valid.mono filled.shape
  | @grow cache heap allocated buffer finish needed called filled =>
      obtain ⟨rfl, rfl⟩ := allocated_eq called
      have fits : values.size ≤ Complexity.GeometricCapacity.next (capacity cache) values.size := by
        unfold Complexity.GeometricCapacity.next
        split <;> omega
      have valid := heap.alloc_valid (τ := .nat)
        (Complexity.GeometricCapacity.next (capacity cache) values.size) 0
      refine ⟨Contents.of_read ((valid_prefix valid fits).mono filled.shape) rfl
        (fun _ bound => filled.read bound bound), ?_,
        (heap.shapeExtends_alloc _ _).trans filled.shape, ?_⟩
      · intro other same
        cases Option.some.inj same
        exact valid.mono filled.shape
      · intro kind other contents separated observed
        exact fill_frame filled other contents separated (observed.alloc _ 0)

/-- The cache transition uses the fixed geometric capacity, not an author-supplied bound. -/
theorem Run.capacity {values : Array Nat} {cache nextCache : Cache}
    {heap finish : Heap} {view : Buffer .nat}
    (run : Run values cache heap nextCache view finish) :
    capacity nextCache = Complexity.GeometricCapacity.next (capacity cache) values.size := by
  cases run with
  | reuse valid fits filled =>
      simp only [Complexity.Language.Buffer.PrepareReuse.capacity,
        Complexity.GeometricCapacity.next, if_pos fits]
  | grow needed called filled =>
      obtain ⟨rfl, _⟩ := allocated_eq called
      rfl

/-- A preparation returns exactly one current request view, without exposing spare cells. -/
theorem Run.length {values : Array Nat} {cache nextCache : Cache}
    {heap finish : Heap} {view : Buffer .nat}
    (run : Run values cache heap nextCache view finish) : view.length = values.size := by
  cases run <;> rfl

/-- Every valid protocol cache can prepare a current request, independently of
machine capacity or a proposed running-time bound. -/
theorem exists_run (values : Array Nat) (cache : Cache) (heap : Heap)
    (valid : Valid cache heap) :
    ∃ nextCache view finish, Run values cache heap nextCache view finish := by
  by_cases needed : NeedsGrowth cache values.size
  · let length := Complexity.GeometricCapacity.next (capacity cache) values.size
    have fits : values.size ≤ length := by
      dsimp [length, Complexity.GeometricCapacity.next]
      split <;> omega
    let allocated := heap.alloc (τ := .nat) length 0
    obtain ⟨finish, filled⟩ := Prepare.Fill.exists_run values (requestView allocated.1 values.size)
      values.size (Nat.le_refl _) allocated.2
      (valid_prefix (heap.alloc_valid length 0) fits) rfl
    refine ⟨some allocated.1, requestView allocated.1 values.size, finish,
      .grow needed ?_ filled⟩
    rw [Replicate.replicateNat_observe]
    exact Replicate.replicateNat_eval _ _ _
  · cases cache with
    | none => exact (needed (Or.inl rfl)).elim
    | some buffer =>
        have fits : values.size ≤ buffer.length := by
          have : ¬buffer.length < values.size := fun h => needed (Or.inr h)
          omega
        obtain ⟨finish, filled⟩ := Prepare.Fill.exists_run values (requestView buffer values.size)
          values.size (Nat.le_refl _) heap (valid_prefix (valid buffer rfl) fits) rfl
        exact ⟨some buffer, requestView buffer values.size, finish,
          .reuse (valid buffer rfl) fits filled⟩

/-- A fixed single-buffer request adapter with explicitly threaded protocol cache. -/
def prepare (cache : Cache) (values : Array Nat) (heap : Heap)
    (args : Env [.buffer .nat]) (finish : Heap) (nextCache : Cache) : Prop :=
  Run values cache heap nextCache args.head finish

end Complexity.Language.Buffer.PrepareReuse
