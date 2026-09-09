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
uses ordinary mutable locals and a while loop. The complete source proof shows
termination and the native array map result by `fun x => min (x + 1) limit`;
no host array operation executes in place of the declared traversal. A separate
compiled invocation and execution-cost proof are not supplied in this module.
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

/-- The actual guard tests the current index and preserves all its inputs. -/
private theorem guard_eval (xs : Buffer .nat) (limit i : Nat) :
    Implementation.boundedMap_loop1.guard i xs limit =
      (pure (.returned (decide (i < xs.length)), i, xs, limit, ()) :
        StateT Heap Part (Control .bool × Implementation.boundedMap_loop1.Locals)) :=
  Implementation.boundedMap_loop1.guard_eq i xs limit

/-- One real iteration advances the mathematical prefix. The named helper and
the shared read/write contracts provide the actual finite outcome. -/
private theorem body_step (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    {i : Nat} {heap : Heap} (current : invariant xs limit contents i heap)
    (bound : i < contents.size) :
    ∃ finish, Implementation.boundedMap_loop1.body i xs limit heap =
        Part.some ((.normal, i + 1, xs, limit, ()), finish) ∧
      invariant xs limit contents (i + 1) finish := by
  obtain ⟨finish, written, updated⟩ := invariant_write xs limit contents current bound
  refine ⟨finish, ?_, updated⟩
  rw [Implementation.boundedMap_loop1.body_eq]
  simp only [increment_eval, ExceptT.run, ExceptT.mk, Bind.bind, StateT.bind,
    Pure.pure, ExceptT.pure, StateT.pure,
    Buffer.readM_eq_ok (invariant_read xs limit contents current bound), Part.bind_some]
  by_cases small : contents[i] + 1 ≤ limit
  · simp only [Nat.min_eq_left small] at written
    simp [small, Buffer.writeM_eq_ok written, Part.bind_some,
      Bind.bind, Pure.pure, StateT.bind, StateT.pure]
  · simp only [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))] at written
    simp [small, Buffer.writeM_eq_ok written, Part.bind_some,
      Bind.bind, Pure.pure, StateT.bind, StateT.pure]

/-- The generated loop rule needs an invariant only for the changing index.
Readonly captures are handled by the frontend's proved frame. -/
private theorem loop_spec (xs : Buffer .nat) (limit : Nat) (contents : Array Nat) (i : Nat) :
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
  rw [guard_eval]
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro heap same
  subst heap
  refine ⟨((.returned (decide (j < xs.length)), j, xs, limit, ()), entry),
    Part.eq_some_iff.mp rfl, ?_⟩
  have length : contents.size = xs.length := by
    simpa only [Array.size_mapIdx] using current.2.size_eq
  by_cases fits : j < xs.length
  · simp only [decide_eq_true_eq, if_pos fits]
    intro heap same
    subst heap
    obtain ⟨finish, executed, updated⟩ :=
      body_step xs limit contents current (by omega)
    exact ⟨((.normal, j + 1, xs, limit, ()), finish),
      Part.eq_some_iff.mp executed, updated, by
        change contents.size - (j + 1) < contents.size - j
        omega⟩
  · simp only [decide_eq_true_eq, if_neg fits]
    exact invariant_done xs limit contents current (by omega)

/-- The declared traversal terminates and updates the actual buffer to the
ordinary native array map. This is the same source program, not a host map used
as its implementation, and correctness imposes no proposed runtime budget. -/
theorem boundedMap_eval (xs : Buffer .nat) (limit : Nat) {contents : Array Nat} {heap : Heap}
    (observed : xs.Contents heap contents) :
    ∃ finish, Implementation.boundedMap xs limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (contents.map fun x => min (x + 1) limit) := by
  have specification := loop_spec xs limit contents 0
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp] at specification
  obtain ⟨⟨⟨control, locals⟩, finish⟩, member, property⟩ :=
    specification heap (invariant_zero xs limit contents observed)
  cases control with
  | normal =>
      refine ⟨finish, ?_, property⟩
      have loopResult := Part.eq_some_iff.mpr member
      rw [Implementation.boundedMap_eq]
      simp only [ExceptT.lift, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        Functor.map, StateT.map, Bind.bind, StateT.bind,
        Pure.pure, ExceptT.pure, StateT.pure, loopResult, Part.bind_some]
  | returned value => exact False.elim property
  | fault error => exact False.elim property

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
