/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Locals.Verification
import Complexity.Data.Array.MapIdx
import Std.Tactic.Do

/-!
# A borrowed-buffer traversal with a helper call and branch

Each iteration reads the current cell, calls the source increment function,
selects the bounded value and writes it to the same shared buffer. The source
uses ordinary mutable locals and a while loop. Its intended mathematical result
is the native array map by `fun x => min (x + 1) limit`; no host array operation
executes in place of the declared traversal.
-/

namespace Complexity.Language.Examples.Traversal

open scoped Part.TotalCorrectness

source_program Implementation where
  def increment (x : Nat) : Nat := do
    return x + 1

  def boundedMap (xs : Buffer Nat) (limit : Nat) : Unit := do
    let mut i := 0
    while i < xs.length do
      let x ← xs.get i
      let y ← increment x
      if y ≤ limit then
        xs.set i y
      else
        xs.set i limit
      i := i + 1
    return

/-- The actual helper returns the mathematical increment and preserves every
initial heap. This statement does not impose a machine word width or budget. -/
theorem increment_eval (x : Nat) :
    Implementation.increment x =
      (pure (x + 1) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [Implementation.increment_eq]

/-- At the traversal boundary, the processed prefix uses the mathematical
update while the unread suffix still has its original values. -/
private def invariant (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    (i : Nat) (heap : Heap) : Prop :=
  i ≤ contents.size ∧ xs.Contents heap
    (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x)

/-- Before the first iteration, the mapped prefix is empty. -/
private theorem invariant_zero (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {heap : Heap} (observed : xs.Contents heap contents) :
    invariant xs limit contents 0 heap := by
  refine ⟨Nat.zero_le _, ?_⟩
  have values :
      (contents.mapIdx fun j x => if j < 0 then min (x + 1) limit else x) = contents := by
    apply Array.ext (by simp)
    intro j leftBound rightBound
    simp only [Array.getElem_mapIdx, Nat.not_lt_zero, if_false]
  exact values.symm ▸ observed

/-- Finishing the prefix gives the ordinary native array map specification. -/
private theorem invariant_done (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (finished : contents.size ≤ i) :
    xs.Contents heap (contents.map fun x => min (x + 1) limit) := by
  have same : i = contents.size := Nat.le_antisymm current.1 finished
  subst i
  have values :
      (contents.mapIdx fun j x => if j < contents.size then min (x + 1) limit else x) =
        contents.map (fun x => min (x + 1) limit) := by
    apply Array.ext (by simp)
    intro j leftBound rightBound
    simp only [Array.getElem_mapIdx, Array.getElem_map]
    exact if_pos (by simpa only [Array.size_map] using rightBound)
  exact values ▸ current.2

/-- The next cell still contains its original mathematical value. -/
private theorem invariant_read (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    heap.read xs i = .ok contents[i] := by
  have available : i <
      (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x).size := by
    simpa only [Array.size_mapIdx] using bound
  simpa only [Array.getElem_mapIdx, Nat.lt_irrefl, if_false] using current.2.read available

/-- Updating the next cell advances the processed prefix by one position. -/
private theorem invariant_write (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    ∃ finish, heap.write xs i (min (contents[i] + 1) limit) = .ok finish ∧
      invariant xs limit contents (i + 1) finish := by
  have available : i <
      (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x).size := by
    simpa only [Array.size_mapIdx] using bound
  obtain ⟨finish, written, updated⟩ :=
    current.2.write_exists available (min (contents[i] + 1) limit)
  refine ⟨finish, written, Nat.succ_le_of_lt bound, ?_⟩
  simpa only [Array.set_mapIdx_ite_lt (fun x => min (x + 1) limit) bound] using updated

end Complexity.Language.Examples.Traversal
