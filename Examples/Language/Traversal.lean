/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.RepresentedFunction
import Complexity.Language.Eval.Locals.Verification
import Complexity.Data.Array.MapIdx
import Complexity.Control.Part.StateT
import Complexity.Control.Triple
import Std.Tactic.Do

/-!
# A borrowed-buffer traversal with a helper call and branch

Each iteration reads the current cell, calls the source increment function,
selects the bounded value and writes it to the same shared buffer. The source
uses an ordinary range loop with an immutable iteration index. The complete source proof shows
termination and the native array map result by `fun x => min (x + 1) limit`;
no host array operation executes in place of the declared traversal.
`Examples.Language.TraversalCompiled` connects this same source proof to its
compiled invocation and an independent linear execution-cost bound.
-/

namespace Complexity.Language.Examples.Traversal

open scoped Std.Do Part.TotalCorrectness

source_program Implementation where
  def increment (x : Nat) : Nat := do
    return x + 1

  def boundedMap (xs : Buffer Nat) (limit : Nat) : Unit := do
    for i in [:xs.length] do
      let x ← xs.get i
      let y ← increment x
      if y ≤ limit then
        xs.set i y
      else
        xs.set i limit
    return

  def boundedMapPair (xs : Buffer Nat) (ys : Buffer Nat) (limit : Nat) : Unit := do
    boundedMap xs limit
    boundedMap ys limit
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

/-- The guard returns its ordinary mathematical decision and preserves the
index and heap. Fixed captures stay inside the generated block interface. -/
theorem guard_contract (xs : Buffer .nat) (limit : Nat) (contents : Array Nat) :
    Implementation.boundedMap_loop1.guard_contract xs limit
      (invariant xs limit contents) (fun _ _ _ _ => False)
      (fun i heap again j finish => j = i ∧ finish = heap ∧
        invariant xs limit contents j finish ∧ (again = true ↔ j < contents.size)) := by
  rw [Implementation.boundedMap_loop1.guard_contract_iff]
  intro i heap current
  rw [Implementation.boundedMap_loop1.guard_eq]
  apply Std.Do.Triple.pure
  intro finish same
  subst finish
  have size : contents.size = xs.length := by
    simpa only [Array.size_mapIdx] using current.2.size_eq
  exact ⟨rfl, rfl, current, by simp only [decide_eq_true_eq, size]⟩

/-- One native body proof advances the mathematical prefix and retains every
outside-buffer observation at the same actual final heap. -/
theorem body_contract (xs : Buffer .nat) (limit : Nat) (contents : Array Nat) :
    Implementation.boundedMap_loop1.body_contract xs limit
      (fun i heap => invariant xs limit contents i heap ∧ i < contents.size)
      (fun i heap j finish => j = i + 1 ∧ invariant xs limit contents j finish ∧
        xs.PreservesOutside heap finish)
      (fun _ _ _ _ _ => False) := by
  rw [Implementation.boundedMap_loop1.body_contract_iff]
  rintro i heap ⟨current, bound⟩
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
    intro finish written updated
    mvcgen
    have advanced : invariant xs limit contents (i + 1) finish := by
      refine ⟨by omega, ?_⟩
      rw [← Nat.min_eq_left small] at updated
      simpa only [values,
        Array.set_mapIdx_ite_lt (fun x => min (x + 1) limit) bound] using updated
    simpa using And.intro advanced
      (fun {kind : CellTy} => Buffer.PreservesOutside.write written (σ := kind))
  · rename_i large
    have large : limit ≤ contents[i] + 1 := by
      have : ¬contents[i] + 1 ≤ limit := by
        simpa only [decide_eq_true_eq] using large
      omega
    refine ⟨values, available, current.2, ?_⟩
    intro finish written updated
    mvcgen
    have advanced : invariant xs limit contents (i + 1) finish := by
      refine ⟨by omega, ?_⟩
      rw [← Nat.min_eq_right large] at updated
      simpa only [values,
        Array.set_mapIdx_ite_lt (fun x => min (x + 1) limit) bound] using updated
    simpa using And.intro advanced
      (fun {kind : CellTy} => Buffer.PreservesOutside.write written (σ := kind))

/-- The prefix invariant and outside-buffer frame compose across the actual
iterations. Descent is ordinary subtraction on the number of unread cells;
the guard and body are specified independently, with their real endpoint heaps. -/
theorem loop_contract (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    (initial : Heap) :
    Implementation.boundedMap_loop1.contract xs limit
      (fun i heap => invariant xs limit contents i heap ∧ xs.PreservesOutside initial heap)
      (fun _ _ _ heap => xs.Contents heap (contents.map fun x => min (x + 1) limit) ∧
        xs.PreservesOutside initial heap)
      (fun _ _ _ _ _ => False) := by
  refine Implementation.boundedMap_loop1.variant_contract xs limit
    (fun i heap => invariant xs limit contents i heap ∧ xs.PreservesOutside initial heap)
    (fun i _ => contents.size - i)
    (fun i heap j finish => j = i ∧ finish = heap ∧ j < contents.size)
    (fun _ heap => xs.Contents heap (contents.map fun x => min (x + 1) limit) ∧
      xs.PreservesOutside initial heap) (fun _ _ _ => False) ?_ ?_
  · apply Stmt.BlockSpec.mono (guard_contract xs limit contents)
    · intro _ _ current; exact current.1
    · intro _ _ _ _ _ impossible; exact impossible
    · intro start heap again finish finalHeap current tested
      rcases tested with ⟨sameIndex, rfl, prefixState, available⟩
      by_cases active : again = true
      · simp only [if_pos active]
        exact ⟨sameIndex, trivial, available.mp active⟩
      · simp only [if_neg active]
        exact ⟨invariant_done xs limit contents prefixState
          (Nat.le_of_not_gt (fun bound => active (available.mpr bound))), current.2⟩
  · intro i heap current
    apply Stmt.BlockSpec.mono (body_contract xs limit contents)
    · rintro start afterGuard ⟨sameIndex, rfl, active⟩
      exact ⟨by simpa only [sameIndex] using current.1, active⟩
    · rintro start afterGuard finish finalHeap ⟨sameIndex, rfl, available⟩
        ⟨next, updated, preserved⟩
      exact ⟨⟨updated, Buffer.PreservesOutside.trans current.2 preserved⟩, by
        dsimp only
        omega⟩
    · intro _ _ _ _ _ _ impossible; exact impossible

/-- The traversal's ordinary array result and its outside-buffer frame hold at
the same actual final heap. This includes disjoint slices of the same object. -/
theorem boundedMap_eval_frame (xs : Buffer .nat) (limit : Nat)
    {contents : Array Nat} {heap : Heap} (observed : xs.Contents heap contents) :
    ∃ finish, Implementation.boundedMap xs limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (contents.map fun x => min (x + 1) limit) ∧
      xs.PreservesOutside heap finish := by
  have specification :
      ⦃fun current => ⌜invariant xs limit contents 0 current ∧
        xs.PreservesOutside heap current⌝⦄ Implementation.boundedMap xs limit
      ⦃⇓ _ finish => ⌜xs.Contents finish (contents.map fun x => min (x + 1) limit) ∧
        xs.PreservesOutside heap finish⌝⦄ := by
    have loopSpec := Implementation.boundedMap_loop1.spec xs limit
      (loop_contract xs limit contents heap)
    rw [Implementation.boundedMap_eq]
    mvcgen [loopSpec]
    all_goals simp_all
  obtain ⟨value, finish, executed, updated, preserved⟩ :=
    (triple_iff_eval _ _ _).mp specification heap
      ⟨invariant_zero xs limit contents observed, Buffer.PreservesOutside.refl xs heap⟩
  exact ⟨finish, executed, updated, preserved⟩

/-- The declared traversal terminates and updates the actual buffer to the
ordinary native array map. This is the same source program, not a host map used
as its implementation, and correctness imposes no proposed runtime budget. -/
theorem boundedMap_eval (xs : Buffer .nat) (limit : Nat) {contents : Array Nat} {heap : Heap}
    (observed : xs.Contents heap contents) :
    ∃ finish, Implementation.boundedMap xs limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (contents.map fun x => min (x + 1) limit) := by
  obtain ⟨finish, executed, updated, _⟩ := boundedMap_eval_frame xs limit observed
  exact ⟨finish, executed, updated⟩

/-- The ordinary array specification transfers to the source function contract
through its generated argument interface, with no register or environment proof. -/
theorem boundedMap_total (contents : Array Nat) :
    Implementation.boundedMap_contract
      (fun xs _ heap => xs.Contents heap contents)
      (fun xs limit _ _ finish =>
        xs.Contents finish (contents.map fun x => min (x + 1) limit)) := by
  apply (Implementation.boundedMap_total_iff _ _).mpr
  intro xs limit heap observed
  obtain ⟨finish, executed, updated⟩ := boundedMap_eval xs limit observed
  exact ⟨(), finish, executed, updated⟩

/-- Callers receive the same array-map specification together with preservation
of every disjoint borrowed view, relative to their actual calling heap. -/
theorem boundedMap_total_frame (contents : Array Nat) :
    Implementation.boundedMap_contract
      (fun xs _ heap => xs.Contents heap contents)
      (fun xs limit heap _ finish =>
        xs.Contents finish (contents.map fun x => min (x + 1) limit) ∧
        xs.PreservesOutside heap finish) := by
  apply (Implementation.boundedMap_total_iff _ _).mpr
  intro xs limit heap observed
  obtain ⟨finish, executed, updated, preserved⟩ := boundedMap_eval_frame xs limit observed
  exact ⟨(), finish, executed, updated, preserved⟩

/-- Observe ordinary array input and output without changing the in-place
implementation or its `Unit` return. The output is read at the final heap. -/
def boundedMapRepresentation :
    FunctionRepresentation (Array Nat × Nat) (fun _ => Array Nat)
      Implementation.signatures[Implementation.boundedMapId] :=
  FunctionRepresentation.ofArgument
    (ArgumentRepresentation.cons (Representation.array .nat)
      (ArgumentRepresentation.single Representation.nat)) .here
    (fun _ => Representation.array .nat)

/-- The existing implementation proof supplies the shared mathematical
correspondence; it is not another implementation or loop induction. -/
theorem boundedMap_refines :
    RepresentedFunction.Refines Implementation.program Implementation.boundedMapId
      boundedMapRepresentation (fun _ => True)
      (fun input => input.1.map fun x => min (x + 1) input.2) := by
  rintro ⟨contents, limit⟩ _
  apply (boundedMap_total contents).consequence
  · intro args heap represented
    exact represented.1
  · intro args initial value finish represented result
    have limit_eq : limit = args.tail.head := represented.2
    simpa only [boundedMapRepresentation, FunctionRepresentation.ofArgument,
      Representation.array, limit_eq] using result

/-- An ordinary array theorem composes with implementation correspondence.
This proves a property of the same source execution without reopening its loop. -/
theorem boundedMap_preserves_length :
    RepresentedFunction.Total Implementation.program Implementation.boundedMapId
      boundedMapRepresentation (fun _ => True)
      (fun input output => output.size = input.1.size) :=
  boundedMap_refines.of_math (by intros; simp)

end Complexity.Language.Examples.Traversal
