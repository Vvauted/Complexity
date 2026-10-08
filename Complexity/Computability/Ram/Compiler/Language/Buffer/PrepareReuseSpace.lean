/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareReuse
import Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareSpace

/-!
# Actual physical footprints of reusable request preparation

Only actual allocator and scalar-writer invocations contribute addresses.
Successive preparations carry the previous footprint forward, and union counts
reused input cells and call frames once. The driver-owned cache remains an
explicit state threaded with the same retained RAM memory.

The observation does not reclaim candidate objects, discard earlier accesses,
or treat external mathematical request arrays as preinstalled source storage.
-/

namespace Ram.LanguageCompiler.Buffer.PrepareReuse

open Complexity.Language
open Complexity.Language.Buffer
open Complexity.Language.Buffer.PrepareReuse

variable {w heapLimit : Nat}

/-- The same reuse/growth calls, with every actually accessed address retained. -/
inductive SpaceRun (values : Array Nat) : Cache → Session.State w heapLimit →
    Cache → Buffer .nat → Session.State w heapLimit → Nat →
      Finset (Word w) → Finset (Word w) → Prop
  | reuse {buffer current finish count seed footprint}
      (valid : buffer.Valid current.heap) (fits : values.size ≤ buffer.length)
      (filled : Prepare.SpaceFill values (requestView buffer values.size) values.size
        current finish count seed footprint) :
      SpaceRun values (some buffer) current (some buffer) (requestView buffer values.size)
        finish count seed footprint
  | grow {cache current}
      (needed : NeedsGrowth cache values.size)
      (allocated : FunctionArenaExecution Replicate.program Replicate.replicateNatId 0 heapLimit
        current.placement
        (Replicate.replicateNat_args
          (Complexity.GeometricCapacity.next (capacity cache) values.size) 0)
        current.heap current.entry)
      {finish count seed footprint}
      (filled : Prepare.SpaceFill values (requestView allocated.value values.size) values.size
        (Session.State.ofExecution allocated) finish count
        (seed ∪ allocated.heapAccesses) footprint) :
      SpaceRun values cache current (some allocated.value) (requestView allocated.value values.size)
        finish (allocated.result.steps + count) seed footprint

/-- Erase only the address observation, not the cache or actual execution. -/
theorem SpaceRun.erase {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun values cache current nextCache view finish count seed footprint) :
    Run values cache current nextCache view finish count := by
  cases run with
  | reuse valid fits filled => exact .reuse valid fits filled.erase
  | grow needed allocated filled => exact .grow needed allocated filled.erase

/-- The observed source loader is the one executed by these actual RAM calls. -/
theorem SpaceRun.source {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun values cache current nextCache view finish count seed footprint) :
    Complexity.Language.Buffer.PrepareReuse.Run values cache current.heap nextCache view
      finish.heap := run.erase.source

/-- Reuse and growth both retain all previously resident/accessed words. -/
theorem SpaceRun.seed_subset {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun values cache current nextCache view finish count seed footprint) :
    seed ⊆ footprint := by
  cases run with
  | reuse valid fits filled => exact filled.seed_subset
  | grow needed allocated filled => exact Finset.subset_union_left.trans filled.seed_subset

/-- Attach the uniquely determined address union to the given counted execution. -/
theorem Run.withSpace {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat} {count : Nat}
    (run : Run values cache current nextCache view finish count) (seed : Finset (Word w)) :
    ∃ footprint, SpaceRun values cache current nextCache view finish count seed footprint := by
  cases run with
  | reuse valid fits filled =>
      obtain ⟨footprint, observed⟩ := filled.withSpace seed
      exact ⟨footprint, .reuse valid fits observed⟩
  | grow needed allocated filled =>
      obtain ⟨footprint, observed⟩ := filled.withSpace (seed ∪ allocated.heapAccesses)
      exact ⟨footprint, .grow needed allocated observed⟩

/-- Conservative finiteness bound for the exact footprint. Tighter reuse bounds
use address regions, rather than accumulating this per-request estimate. -/
theorem SpaceRun.card_le {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {view : Buffer .nat}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun values cache current nextCache view finish count seed footprint) :
    footprint.card ≤ seed.card + count := by
  cases run with
  | reuse valid fits filled => exact filled.card_le
  | grow needed allocated filled =>
      have accessed : allocated.heapAccesses.card ≤ allocated.result.steps :=
        Ram.heapAccesses_card_le _ _ _
      exact filled.card_le.trans
        ((Nat.add_le_add_right ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left accessed seed.card)) _).trans_eq (Nat.add_assoc _ _ _))

/-- The reusable loader's complete physical-space adapter for a stateful session. -/
def prepareSpace (cache : Cache) (values : Array Nat) (current : Session.State w heapLimit)
    (args : Env [.buffer .nat]) (finish : Session.State w heapLimit)
    (nextCache : Cache) (count : Nat) (seed footprint : Finset (Word w)) : Prop :=
  SpaceRun values cache current nextCache args.head finish count seed footprint

theorem prepareSpace_erase {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {args : Env [.buffer .nat]}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace cache values current args finish nextCache count seed footprint) :
    prepare cache values current args finish nextCache count := run.erase

theorem prepareSpace_source {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {args : Env [.buffer .nat]}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace cache values current args finish nextCache count seed footprint) :
    Complexity.Language.Buffer.PrepareReuse.prepare cache values current.heap args finish.heap
      nextCache := run.source

theorem prepareSpace_seed_subset {values : Array Nat} {cache nextCache : Cache}
    {current finish : Session.State w heapLimit} {args : Env [.buffer .nat]}
    {count : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace cache values current args finish nextCache count seed footprint) :
    seed ⊆ footprint := run.seed_subset

end Ram.LanguageCompiler.Buffer.PrepareReuse
