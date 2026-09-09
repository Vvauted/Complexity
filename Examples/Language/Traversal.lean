/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Locals.Verification
import Complexity.Data.Array.MapIdx
import Complexity.Control.Part.StateT
import Std.Tactic.Do

/-!
# A borrowed-buffer traversal with a helper call and branch

Each iteration reads the current cell, calls the source increment function,
selects the bounded value and writes it to the same shared buffer. The source
uses ordinary mutable locals and a while loop. The complete source proof shows
termination and the native array map result by `fun x => min (x + 1) limit`;
no host array operation executes in place of the declared traversal.
`Examples.Language.TraversalCompiled` connects this same source proof to its
compiled invocation and an independent linear execution-cost bound.
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
def invariant (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    (i : Nat) (heap : Heap) : Prop :=
  i ≤ contents.size ∧ xs.Contents heap
    (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x)

/-- Before the first iteration, the mapped prefix is empty. -/
theorem invariant_zero (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
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
theorem invariant_read (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    heap.read xs i = .ok contents[i] := by
  have available : i <
      (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x).size := by
    simpa only [Array.size_mapIdx] using bound
  simpa only [Array.getElem_mapIdx, Nat.lt_irrefl, if_false] using current.2.read available

/-- The actual guard tests the current index and preserves all its inputs. -/
theorem guard_eval (xs : Buffer .nat) (limit i : Nat) :
    Implementation.boundedMap_loop1.guard i xs limit =
      (pure (.returned (decide (i < xs.length)), i, xs, limit, ()) :
        StateT Heap Part (Control .bool × Implementation.boundedMap_loop1.Locals)) :=
  Implementation.boundedMap_loop1.guard_eq i xs limit

/-- The guard's native contract exposes its mathematical decision and unchanged
index and heap, for reuse by correctness and separate resource proofs. -/
theorem guard_spec (xs : Buffer .nat) (limit i : Nat) (heap : Heap) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.boundedMap_loop1.guard i xs limit)
      (fun entry => ⟨entry = heap⟩)
      (fun outcome finish =>
        ⟨outcome.1 = .returned (decide (i < xs.length)) ∧ outcome.2.1 = i ∧ finish = heap⟩,
        ⟨⟩) := by
  rw [guard_eval]
  apply Std.Do.Triple.pure
  intro finish same
  exact ⟨rfl, rfl, same⟩

/-- A native contract for the actual loop body. Shared read/write rules and
the named helper advance the mathematical prefix, retaining the actual heap. -/
theorem body_spec (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.boundedMap_loop1.body i xs limit)
      (fun entry => ⟨entry = heap⟩)
      (fun outcome finish => ⟨outcome = (.normal, i + 1, xs, limit, ()) ∧
        invariant xs limit contents (i + 1) finish⟩, ⟨⟩) := by
  rw [Implementation.boundedMap_loop1.body_eq]
  simp only [increment_eval]
  mvcgen
  rename_i entry same
  subst entry
  let values := contents.mapIdx fun j x => if j < i then min (x + 1) limit else x
  have available : i < values.size := by simpa only [values, Array.size_mapIdx] using bound
  refine ⟨values, available, current.2, ?_⟩
  have next : values[i] = contents[i] := by simp only [values, Array.getElem_mapIdx,
    Nat.lt_irrefl, if_false]
  simp only [next]
  mvcgen
  · rename_i small
    have small : contents[i] + 1 ≤ limit := by
      simpa only [decide_eq_true_eq] using small
    refine ⟨values, available, current.2, ?_⟩
    intro finish _ updated
    mvcgen
    have advanced : invariant xs limit contents (i + 1) finish := by
      refine ⟨by omega, ?_⟩
      rw [← Nat.min_eq_left small] at updated
      simpa only [values,
        Array.set_mapIdx_ite_lt (fun x => min (x + 1) limit) bound] using updated
    simpa using advanced
  · rename_i large
    have large : limit ≤ contents[i] + 1 := by
      have : ¬contents[i] + 1 ≤ limit := by
        simpa only [decide_eq_true_eq] using large
      omega
    refine ⟨values, available, current.2, ?_⟩
    intro finish _ updated
    mvcgen
    have advanced : invariant xs limit contents (i + 1) finish := by
      refine ⟨by omega, ?_⟩
      rw [← Nat.min_eq_right large] at updated
      simpa only [values,
        Array.set_mapIdx_ite_lt (fun x => min (x + 1) limit) bound] using updated
    simpa using advanced

/-- One real iteration advances the mathematical prefix. The named helper and
the shared read/write contracts provide the actual finite outcome. -/
theorem body_step (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    ∃ finish, Implementation.boundedMap_loop1.body i xs limit heap =
        Part.some ((.normal, i + 1, xs, limit, ()), finish) ∧
      invariant xs limit contents (i + 1) finish := by
  obtain ⟨outcome, finish, executed, same, updated⟩ :=
    (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
      (body_spec xs limit contents current bound) heap rfl
  exact ⟨finish, same ▸ executed, updated⟩

/-- One source round exposes the invariant and mathematical decision at the
actual guard result, then the index progress and invariant at the actual body
result. The body starts from the guard's real locals and heap. No machine
representation, instruction bound or duplicate traversal proof is involved. -/
theorem round_spec (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Stmt.observe Implementation.boundedMap_loop1.View Implementation.boundedMap_loop1.Guard
        Implementation.program (i, xs, limit, ()))
      (fun entry => ⟨entry = heap⟩)
      (fun guardOutcome guardHeap => ⟨match guardOutcome.1 with
        | .returned again =>
            (invariant xs limit contents guardOutcome.2.1 guardHeap ∧
              (again = true ↔ guardOutcome.2.1 < contents.size)) ∧
            if again then
              Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
                (Stmt.observe Implementation.boundedMap_loop1.View
                  Implementation.boundedMap_loop1.Body Implementation.program guardOutcome.2)
                (fun entry => ⟨entry = guardHeap⟩)
                (fun bodyOutcome bodyHeap => ⟨match bodyOutcome.1 with
                  | .normal => bodyOutcome.2.1 = i + 1 ∧
                      invariant xs limit contents bodyOutcome.2.1 bodyHeap
                  | .returned _ => False
                  | .fault _ => False⟩, ⟨⟩)
            else True
        | .normal => False
        | .fault _ => False⟩, ⟨⟩) := by
  rw [Implementation.boundedMap_loop1.guard_observe, guard_eval]
  apply Std.Do.Triple.pure
  intro entry same
  subst entry
  have size : contents.size = xs.length := by
    simpa only [Array.size_mapIdx] using current.2.size_eq
  refine ⟨⟨current, ?_⟩, ?_⟩
  · simp only [size, decide_eq_true_eq]
  · by_cases fits : i < contents.size
    · have active : i < xs.length := by simpa only [size] using fits
      simp only [decide_eq_true_eq, if_pos active]
      apply Std.Do.SPred.entails.trans (body_spec xs limit contents current fits)
      apply (Std.Do.WP.wp _).mono
      constructor
      · rintro outcome finish ⟨rfl, updated⟩
        exact ⟨rfl, updated⟩
      · trivial
    · have inactive : ¬i < xs.length := by simpa only [size] using fits
      simp only [decide_eq_true_eq, if_neg inactive]

/-- The generated loop rule needs an invariant only for the changing index.
Readonly captures are handled by the frontend's proved frame. -/
theorem loop_spec (xs : Buffer .nat) (limit : Nat) (contents : Array Nat) (i : Nat) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.boundedMap_loop1 i xs limit)
      (fun heap => ⟨invariant xs limit contents i heap⟩)
      (fun outcome heap => ⟨match outcome.1 with
        | .normal => xs.Contents heap (contents.map fun x => min (x + 1) limit)
        | .returned _ => False
        | .fault _ => False⟩, ⟨⟩) := by
  refine Implementation.boundedMap_loop1.variant_spec xs limit
    (invariant xs limit contents) (fun j _ => contents.size - j)
    (fun _ heap => xs.Contents heap (contents.map fun x => min (x + 1) limit))
    (fun _ _ _ => False) ?_ i
  intro j entry current
  have round := round_spec xs limit contents current
  -- Align the actual native body entry with the generated fixed-capture interface.
  rw [Implementation.boundedMap_loop1.guard_observe, guard_eval] at round
  rw [guard_eval]
  apply Std.Do.Triple.pure
  intro heap same
  subst heap
  have guardPost := Part.TotalCorrectness.stateT_post_of_eq round
    (entry := entry) (finish := entry)
    (value := (Control.returned (result := .bool) (decide (j < xs.length)), j, xs, limit, ()))
    rfl rfl
  rcases guardPost with ⟨⟨guardInvariant, guardTest⟩, body⟩
  simp only [decide_eq_true_eq] at guardTest
  by_cases fits : j < xs.length
  · simp only [decide_eq_true_eq, if_pos fits] at body ⊢
    have available : j < contents.size := guardTest.mp fits
    apply Std.Do.SPred.entails.trans body
    apply (Std.Do.WP.wp _).mono
    constructor
    · rintro ⟨control, locals⟩ finish property
      cases control with
      | normal =>
          rcases property with ⟨next, updated⟩
          exact ⟨updated, by
            change contents.size - locals.1 < contents.size - j
            rw [next]
            omega⟩
      | returned value => exact property
      | fault error => exact property
    · trivial
  · simp only [decide_eq_true_eq, if_neg fits]
    have finished : ¬j < contents.size := fun bound => fits (guardTest.mpr bound)
    exact invariant_done xs limit contents guardInvariant (by
      change contents.size ≤ j
      omega)

/-- The declared traversal terminates and updates the actual buffer to the
ordinary native array map. This is the same source program, not a host map used
as its implementation, and correctness imposes no proposed runtime budget. -/
theorem boundedMap_eval (xs : Buffer .nat) (limit : Nat) {contents : Array Nat} {heap : Heap}
    (observed : xs.Contents heap contents) :
    ∃ finish, Implementation.boundedMap xs limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (contents.map fun x => min (x + 1) limit) := by
  have specification : Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (Implementation.boundedMap xs limit)
      (fun heap => ⟨invariant xs limit contents 0 heap⟩)
      (fun _ heap => ⟨xs.Contents heap (contents.map fun x => min (x + 1) limit)⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)) := by
    rw [Implementation.boundedMap_eq]
    mvcgen [loop_spec]
    rw [Std.Do.WP.lift_ExceptT, Std.Do.WP.monadLift_ExceptT]
    mvcgen [loop_spec]
    all_goals simp_all
  obtain ⟨value, finish, executed, updated⟩ :=
    (triple_iff_eval _ _ _).mp specification heap (invariant_zero xs limit contents observed)
  exact ⟨finish, executed, updated⟩

/-- The ordinary array specification transfers to the source function contract
through its generated argument interface, with no register or environment proof. -/
theorem boundedMap_total (contents : Array Nat) :
    FunctionTotal Implementation.program Implementation.boundedMapId
      (fun args heap => args.head.Contents heap contents)
      (fun args _ _ finish =>
        args.head.Contents finish (contents.map fun x => min (x + 1) args.tail.head)) := by
  apply (Implementation.boundedMap_total_iff
    (fun xs _ heap => xs.Contents heap contents)
    (fun xs limit _ _ finish =>
      xs.Contents finish (contents.map fun x => min (x + 1) limit))).mpr
  intro xs limit heap observed
  obtain ⟨finish, executed, updated⟩ := boundedMap_eval xs limit observed
  exact ⟨(), finish, executed, updated⟩

end Complexity.Language.Examples.Traversal
