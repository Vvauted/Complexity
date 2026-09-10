/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Heap.Restriction
import Complexity.Control.Part.StateT
import Complexity.Control.Triple
import Std.Tactic.Do

/-!
# Reusing nested temporary storage across source calls

`Implementation.make` allocates one result cell outside the temporary scopes.
Each call to `Implementation.work` allocates two nested temporary arrays, reads
the outer temporary array after the inner scope has released its storage, and
writes the result cell. A return from inside the outer scope also releases its
temporary storage. The returned result is longer-lived than either scratch
array; no copied host implementation or algorithm-specific lowering is used.

The mathematical result depends on whether an iteration and a nonempty read
occur, while the required temporary capacity is independent of the iteration
count. Source correctness and termination do not require a RAM capacity or
instruction budget.
-/

namespace Complexity.Language.Examples.Scope

open scoped Part.TotalCorrectness

source_program Implementation where
  def work (out : Buffer Nat) (n : Nat) (value : Nat) : Unit := do
    with_scratch do
      let temp ← Buffer.alloc n value
      with_scratch do
        let trash ← Buffer.alloc n 0
      if 0 < n then
        let x ← temp.get 0
        out.set 0 x
        return
      else
        return

  def make (count : Nat) (n : Nat) (value : Nat) : Buffer Nat := do
    let out ← Buffer.alloc 1 0
    let mut remaining := count
    while 0 < remaining do
      work out n value
      remaining := remaining - 1
    return out

/-- The ordinary mathematical contents expected after all calls. -/
def resultContents (count n value : Nat) : Array Nat :=
  #[if 0 < count ∧ 0 < n then value else 0]

/-- A single call either writes the value read from its initialized scratch
array or leaves the result cell unchanged when that array is empty. -/
def workContents (n value previous : Nat) : Array Nat :=
  #[if 0 < n then value else previous]

/-- One permanent result cell and two simultaneously allocated scratch arrays
suffice independently of how many calls the loop performs. -/
def heapLimit (entryCursor n : Nat) : Nat := entryCursor + 1 + 2 * n

/-- The inner body allocates its actual scratch array and then falls through.
Its surrounding lexical bindings retain their original ordinary values. -/
theorem inner_body_eval (temp out : Buffer .nat) (n value : Nat) (heap : Heap) :
    Implementation.work_scope2.body temp out n value heap =
      Part.some ((.normal, temp, out, n, value, ()), (heap.alloc (τ := .nat) n 0).2) := by
  rw [Implementation.work_scope2.body_eq]
  simp only [Buffer.allocM, ExceptT.run, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, Part.bind_some]

/-- A nested allocation-only scope releases its entire fresh suffix. Both
borrowed handles were live on entry, so neither is an escaping temporary. -/
theorem inner_eval (temp out : Buffer .nat) (n value : Nat) (heap : Heap)
    (tempRooted : temp.Rooted heap) (outRooted : out.Rooted heap) :
    Implementation.work_scope2 temp out n value heap =
      Part.some ((.normal, temp, out, n, value, ()), heap) := by
  have safe : ScopeSafe heap
      ⟨Implementation.work_scope2.View.symm (temp, out, n, value, ()),
        (heap.alloc (τ := .nat) n 0).2⟩ (.normal : Control .unit) := by
    simp only [ScopeSafe, Implementation.work_scope2.view_symm_apply,
      Env.Rooted.cons_iff, Env.Rooted.empty, ValueRooted, Control.Rooted,
      tempRooted, outRooted, and_self]
  rw [Implementation.work_scope2.eq]
  dsimp only
  rw [inner_body_eval]
  simp only [Part.map_some, scopeExit_of_safe safe, Heap.take_alloc_self,
    Equiv.apply_symm_apply]

/-- The checked inner scope is reusable in native verification, with no
allocation or reclamation detail imposed on its continuation. -/
theorem inner_spec (temp out : Buffer .nat) (n value : Nat)
    (post : Std.Do.PostCond
      (Control .unit × Implementation.work_scope2.Locals) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.work_scope2 temp out n value)
      (fun heap => ⟨temp.Rooted heap ∧ out.Rooted heap ∧
        (post.1 (.normal, temp, out, n, value, ()) heap).down⟩) post := by
  apply (Part.TotalCorrectness.stateT_triple_iff _ _ _).mpr
  intro heap ⟨tempRooted, outRooted, property⟩
  exact ⟨(.normal, temp, out, n, value, ()), heap,
    inner_eval temp out n value heap tempRooted outRooted, property⟩

/-- The actual outer body reads its still-live temporary after inner cleanup.
The ordinary contents contract describes the write to the surviving output. -/
theorem outer_body_spec (out : Buffer .nat) (n value previous : Nat)
    (heap : Heap) (observed : out.Contents heap #[previous]) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.work_scope1.body out n value)
      (fun entry => ⟨entry = heap⟩)
      (fun outcome finish => ⟨outcome = (.returned (), out, n, value, ()) ∧
        out.Contents finish (workContents n value previous)⟩, ⟨⟩) := by
  rw [Implementation.work_scope1.body_eq]
  mvcgen [inner_spec]
  rename_i entry same
  subst entry
  intro temp middle allocated initialized growth fresh
  have retained : out.Contents middle #[previous] := by
    have preserved := observed.alloc (τ := .nat) n value
    rw [allocated] at preserved
    exact preserved
  mvcgen [inner_spec]
  refine ⟨initialized.valid.rooted, observed.valid.rooted.mono growth, ?_⟩
  mvcgen
  · rename_i nonempty
    have active : 0 < n := by simpa only [decide_eq_true_eq] using nonempty
    have available : 0 < (Array.replicate n value : Array Nat).size := by
      simpa only [Array.size_replicate] using active
    refine ⟨Array.replicate n value, available, initialized, ?_⟩
    simp only [Array.getElem_replicate]
    mvcgen
    refine ⟨#[previous], by simp, retained, ?_⟩
    intro finish written updated
    mvcgen
    simpa [workContents, active] using updated
  · rename_i empty
    have inactive : ¬ 0 < n := by simpa only [decide_eq_true_eq] using empty
    simpa only [workContents, if_neg inactive, true_and] using retained

/-- Returning from the outer scope preserves the output's updated contents
while releasing the temporary object from the actual final heap. -/
theorem outer_eval (out : Buffer .nat) (n value previous : Nat)
    (heap : Heap) (observed : out.Contents heap #[previous]) :
    ∃ finish,
      Implementation.work_scope1 out n value heap =
        Part.some ((.returned (), out, n, value, ()), finish) ∧
      out.Contents finish (workContents n value previous) := by
  obtain ⟨outcome, finish, executed, same, updated⟩ :=
    (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
      (outer_body_spec out n value previous heap observed) heap rfl
  subst outcome
  have safe : ScopeSafe heap
      ⟨Implementation.work_scope1.View.symm (out, n, value, ()), finish⟩
      (.returned () : Control .unit) := by
    simp only [ScopeSafe, Implementation.work_scope1.view_symm_apply,
      Env.Rooted.cons_iff, Env.Rooted.empty, ValueRooted, Control.Rooted,
      observed.valid.rooted, and_self]
  refine ⟨finish.take heap.objects.size, ?_, updated.take observed.valid.rooted⟩
  rw [Implementation.work_scope1.eq]
  dsimp only
  rw [executed]
  simp only [Part.map_some, scopeExit_of_safe safe, Equiv.apply_symm_apply]

/-- The declared worker terminates and updates the ordinary contents of its
borrowed output. No word width, memory capacity or time budget is assumed. -/
theorem work_eval (out : Buffer .nat) (n value previous : Nat)
    (heap : Heap) (observed : out.Contents heap #[previous]) :
    ∃ finish, Implementation.work out n value heap = Part.some (.ok (), finish) ∧
      out.Contents finish (workContents n value previous) := by
  obtain ⟨finish, executed, updated⟩ := outer_eval out n value previous heap observed
  refine ⟨finish, ?_, updated⟩
  rw [Implementation.work_eq]
  simp only [ExceptT.lift, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
    Bind.bind, Pure.pure, Functor.map, StateT.bind, StateT.pure, StateT.map,
    executed, Part.bind_some]

/-- A source call reuses the worker's mathematical contents contract at its
actual entry and final heaps, through the generated ordinary-argument bridge. -/
theorem work_total (previous : Nat) :
    FunctionTotal Implementation.program Implementation.workId
      (fun args heap => args.head.Contents heap #[previous])
      (fun args _ _ finish =>
        args.head.Contents finish (workContents args.tail.head args.tail.tail.head previous)) := by
  apply (Implementation.work_total_iff
    (fun out _ _ heap => out.Contents heap #[previous])
    (fun out n value _ _ finish => out.Contents finish (workContents n value previous))).mpr
  intro out n value heap observed
  obtain ⟨finish, executed, updated⟩ := work_eval out n value previous heap observed
  exact ⟨(), finish, executed, updated⟩

/-- Only the remaining call count changes in the loop. The first completed
nonempty call sets the result; all later calls preserve that same value. -/
def invariant (out : Buffer .nat) (count n value remaining : Nat) (heap : Heap) : Prop :=
  remaining ≤ count ∧
    out.Contents heap #[if remaining < count ∧ 0 < n then value else 0]

/-- The newly initialized output satisfies the loop invariant before any call. -/
theorem invariant_initial (out : Buffer .nat) (count n value : Nat)
    {heap : Heap} (observed : out.Contents heap #[0]) :
    invariant out count n value count heap := by
  exact ⟨Nat.le_refl _, by simpa only [Nat.lt_irrefl, false_and, if_false] using observed⟩

/-- A real call's contents contract advances the loop invariant. Termination
uses the ordinary decrease of `remaining`, separately from machine cost. -/
theorem invariant_step (out : Buffer .nat) (count n value : Nat)
    {remaining : Nat} {heap finish : Heap}
    (current : invariant out count n value remaining heap) (active : 0 < remaining)
    (updated : out.Contents finish
      (workContents n value (if remaining < count ∧ 0 < n then value else 0))) :
    invariant out count n value (remaining - 1) finish := by
  have remainingBound := current.1
  have advanced : remaining - 1 < count := by omega
  refine ⟨by omega, ?_⟩
  by_cases nonempty : 0 < n
  · simpa only [workContents, nonempty, advanced, and_self, if_true] using updated
  · simpa only [workContents, nonempty, and_false, if_false] using updated

/-- At loop exit the result has the ordinary mathematical array contents. -/
theorem invariant_done (out : Buffer .nat) (count n value : Nat)
    {remaining : Nat} {heap : Heap}
    (current : invariant out count n value remaining heap) (finished : ¬ 0 < remaining) :
    out.Contents heap (resultContents count n value) := by
  have zero : remaining = 0 := Nat.eq_zero_of_not_pos finished
  simpa only [zero, resultContents] using current.2

/-- The loop's actual guard preserves its full lexical state and decides the
ordinary positivity test used by the termination argument. -/
theorem guard_eval (remaining : Nat) (out : Buffer .nat) (count n value : Nat) :
    Implementation.make_loop1.guard remaining out count n value =
      (pure (.returned (decide (0 < remaining)), remaining, out, count, n, value, ()) :
        StateT Heap Part (Control .bool × Implementation.make_loop1.Locals)) :=
  Implementation.make_loop1.guard_eq remaining out count n value

/-- A real loop body calls the scoped worker and decreases only the remaining
count. Its contents contract and complete local update also serve the separate
resource proof; neither needs to re-prove the worker's behavior. -/
theorem body_spec (out : Buffer .nat) (count n value : Nat)
    {remaining : Nat} {heap : Heap}
    (current : invariant out count n value remaining heap) (active : 0 < remaining) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.make_loop1.body remaining out count n value)
      (fun entry => ⟨entry = heap⟩)
      (fun outcome finish =>
        ⟨outcome = (.normal, remaining - 1, out, count, n, value, ()) ∧
          invariant out count n value (remaining - 1) finish⟩, ⟨⟩) := by
  have workerSpec := Implementation.work_spec
    (work_total (if remaining < count ∧ 0 < n then value else 0))
  rw [Implementation.make_loop1.body_eq]
  mvcgen [workerSpec]
  rename_i entry same
  subst entry
  refine ⟨current.2, ?_⟩
  intro returned finish updated
  cases returned
  mvcgen
  simpa using invariant_step out count n value current active updated

/-- Lean's existing well-founded measure proves termination of the actual
source loop. The relation concerns mathematical progress, not a machine budget;
its body contract carries the current heap through every real call. -/
theorem loop_spec (out : Buffer .nat) (count n value remaining : Nat) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (Implementation.make_loop1 remaining out count n value)
      (fun heap => ⟨invariant out count n value remaining heap⟩)
      (fun outcome finish => ⟨match outcome.1 with
        | .normal => out.Contents finish (resultContents count n value)
        | .returned _ => False
        | .fault _ => False⟩, ⟨⟩) := by
  refine Implementation.make_loop1.wellFounded_spec out count n value
    (invariant out count n value)
    (measure fun state : Implementation.make_loop1.Mutable × Heap => state.1.1).rel
    (measure fun state : Implementation.make_loop1.Mutable × Heap => state.1.1).wf
    (fun _ finish => out.Contents finish (resultContents count n value))
    (fun _ _ _ => False) ?_ remaining
  intro left heap current
  rw [guard_eval]
  apply Std.Do.Triple.pure
  intro entry same
  subst entry
  by_cases active : 0 < left
  · simp only [decide_eq_true_eq, if_pos active]
    refine (body_spec out count n value current active).mono (fun _ same => same) ?_
    constructor
    · rintro outcome finish ⟨rfl, updated⟩
      exact ⟨updated, by change left - 1 < left; omega⟩
    · trivial
  · simp only [decide_eq_true_eq, if_neg active]
    exact invariant_done out count n value current active

/-- One source declaration allocates the surviving result and repeatedly uses
the same nested scratch scopes. Its successful result has the ordinary array
contents, for every count and every initial heap, including both empty cases. -/
theorem make_spec (count n value : Nat) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (Implementation.make count n value)
      (fun _ => ⟨True⟩)
      (fun out finish => ⟨out.Contents finish (resultContents count n value)⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)) := by
  have loopSpec := fun (out : Buffer .nat) (remaining : Nat) =>
    loop_spec out count n value remaining
  rw [Implementation.make_eq]
  mvcgen [loopSpec]
  intro out finish allocated initialized growth fresh
  mvcgen [loopSpec]
  rw [Std.Do.WP.lift_ExceptT, Std.Do.WP.monadLift_ExceptT]
  mvcgen [loopSpec]
  all_goals
    simp_all only [invariant, Nat.le_refl, Nat.lt_irrefl, false_and,
      if_false, true_and, Array.replicate_one]

/-- The mathematical contract supplies actual finite source evaluation and
the retained output contents without a separate termination or budget proof. -/
theorem make_eval (count n value : Nat) (heap : Heap) :
    ∃ out finish, Implementation.make count n value heap = Part.some (.ok out, finish) ∧
      out.Contents finish (resultContents count n value) :=
  (triple_iff_eval _ _ _).mp (make_spec count n value) heap trivial

/-- The same named declaration's source contract is ready for the separate
range, capacity, instruction-count and physical-space proofs. -/
theorem make_total :
    FunctionTotal Implementation.program Implementation.makeId (fun _ _ => True)
      (fun args _ out finish =>
        out.Contents finish (resultContents args.head args.tail.head args.tail.tail.head)) := by
  apply (Implementation.make_total_iff (fun _ _ _ _ => True)
    (fun count n value _ out finish => out.Contents finish (resultContents count n value))).mpr
  intro count n value heap _
  exact make_eval count n value heap

end Complexity.Language.Examples.Scope
