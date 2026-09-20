/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Simp
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

source_program (native) Implementation where
  def work (out : Buffer Nat) (n : Nat) (value : Nat) : Unit := do
    let result : Unit ← do
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
    return result

  def make (count : Nat) (n : Nat) (value : Nat) : Buffer Nat := do
    let result : Buffer Nat ← do
      let out ← Buffer.alloc 1 0
      let mut remaining := count
      while 0 < remaining do
        work out n value
        remaining := remaining - 1
        if remaining == 0 then
          return out
      return out
    return result

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
Its contract mentions only the original source variables and actual heap. -/
theorem inner_body_eval (temp out : Buffer .nat) (n value : Nat) :
    Implementation.Source.work_scope2.body_completion_contract
      (fun locals _ => locals = (temp, out, n, value, ()))
      (fun _ heap locals finish => locals = (temp, out, n, value, ()) ∧
        finish = (heap.alloc (τ := .nat) n 0).2)
      (fun _ _ _ _ _ => False) := by
  rintro _ heap rfl
  dsimp only
  rw [Implementation.Source.work_scope2.body_eq]
  mvcgen
  rename_i entry same
  subst entry
  intro trash finish allocated initialized growth fresh
  mvcgen
  exact ⟨trivial, (congrArg Prod.snd allocated).symm⟩

/-- A nested allocation-only scope releases its entire fresh suffix. Both
borrowed handles were live on entry, so neither is an escaping temporary. -/
theorem inner_eval (temp out : Buffer .nat) (n value : Nat) :
    Implementation.Source.work_scope2.completion_contract
      (fun locals heap => locals = (temp, out, n, value, ()) ∧
        temp.Rooted heap ∧ out.Rooted heap)
      (fun _ heap locals finish => locals = (temp, out, n, value, ()) ∧ finish = heap)
      (fun _ _ _ _ _ => False) := by
  refine Implementation.Source.work_scope2.completion_contract_of_body_spec
    (inner_body_eval temp out n value) (fun _ _ current => current.1) ?_ ?_
  · rintro _ heap _ _ ⟨rfl, tempRooted, outRooted⟩ ⟨rfl, rfl⟩
    refine ⟨?_, rfl, Heap.take_alloc_self (τ := .nat) _ n 0⟩
    simp only [Implementation.Source.work_scope2.VisibleRooted, ValueRooted,
      tempRooted, outRooted, and_self]
  · intro _ _ _ _ _ _ impossible
    exact False.elim impossible

/-- The actual outer body reads its still-live temporary after inner cleanup.
The ordinary contents contract describes the write to the surviving output. -/
theorem outer_body_spec (out : Buffer .nat) (n value previous : Nat) :
    Implementation.Source.work_scope1.body_completion_contract
      (fun locals heap => locals = (out, n, value, ()) ∧ out.Contents heap #[previous])
      (fun _ _ _ _ => False)
      (fun _ _ _ locals finish => locals = (out, n, value, ()) ∧
        out.Contents finish (workContents n value previous)) := by
  rintro _ heap ⟨rfl, observed⟩
  have innerSpec := fun temp => Implementation.Source.work_scope2.completion_spec
    (inner_eval temp out n value) temp out n value
  dsimp only
  rw [Implementation.Source.work_scope1.body_eq]
  mvcgen [innerSpec]
  rename_i entry same
  subst entry
  intro temp middle allocated initialized growth fresh
  have retained : out.Contents middle #[previous] := by
    simpa only [allocated] using observed.alloc (τ := .nat) n value
  mvcgen [innerSpec]
  refine ⟨⟨trivial, initialized.valid.rooted, retained.valid.rooted⟩, ?_, ?_⟩
  swap
  · intro _ _ _ impossible
    exact False.elim impossible
  rintro _ _ rfl rfl
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
theorem outer_eval (out : Buffer .nat) (n value previous : Nat) :
    Implementation.Source.work_scope1.completion_contract
      (fun locals heap => locals = (out, n, value, ()) ∧ out.Contents heap #[previous])
      (fun _ _ _ _ => False)
      (fun _ _ _ locals finish => locals = (out, n, value, ()) ∧
        out.Contents finish (workContents n value previous)) := by
  refine Implementation.Source.work_scope1.completion_contract_of_body_spec
    (outer_body_spec out n value previous) (fun _ _ current => current) ?_ ?_
  · intro _ _ _ _ _ impossible
    exact False.elim impossible
  · rintro _ heap _ _ finish ⟨rfl, observed⟩ ⟨rfl, updated⟩
    refine ⟨?_, trivial, rfl, updated.take observed.valid.rooted⟩
    simp only [Implementation.Source.work_scope1.VisibleRooted, ValueRooted,
      observed.valid.rooted, and_self]

/-- The declared worker terminates and updates the ordinary contents of its
borrowed output. No word width, memory capacity or time budget is assumed. -/
theorem work_eval (out : Buffer .nat) (n value previous : Nat)
    (heap : Heap) (observed : out.Contents heap #[previous]) :
    ∃ finish, Implementation.Source.work out n value heap = Part.some (.ok (), finish) ∧
      out.Contents finish (workContents n value previous) := by
  have outerSpec := Implementation.Source.work_scope1.completion_spec
    (outer_eval out n value previous) out n value
  have specification :
      Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
        (ps := .except Fault (.arg Heap .pure))
        (Implementation.Source.work out n value)
        (fun entry => ⟨entry = heap⟩)
        (fun _ finish => ⟨out.Contents finish (workContents n value previous)⟩,
          (fun _ _ => ⟨False⟩, ⟨⟩)) := by
    rw [Implementation.Source.work_eq]
    mvcgen [outerSpec]
    rename_i entry same
    subst entry
    refine ⟨⟨trivial, observed⟩, ?_, ?_⟩
    · intro _ _ impossible
      exact False.elim impossible
    · rintro _ _ finish rfl updated
      mvcgen
  obtain ⟨result, finish, executed, updated⟩ :=
    (triple_iff_eval _ _ _).mp specification heap rfl
  cases result
  exact ⟨finish, executed, updated⟩

/-- A source call reuses the worker's mathematical contents contract at its
actual entry and final heaps, through the generated ordinary-argument bridge. -/
theorem work_total (previous : Nat) :
    FunctionTotal Implementation.Source.program Implementation.Source.workId
      (fun args heap => args.head.Contents heap #[previous])
      (fun args _ _ finish =>
        args.head.Contents finish (workContents args.tail.head args.tail.tail.head previous)) := by
  apply (Implementation.Source.work_total_iff
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

/-- The loop's source variables, selected by name. The buffer field records its
handle; the invariant separately describes its contents at the current heap. -/
def loopModel (out : Buffer .nat) (count n value remaining : Nat) :
    Implementation.Source.make_loop1.Model :=
  Implementation.Source.make_loop1.mkModel
    (remaining := remaining) (out := out) (count := count) (n := n) (value := value)

open Implementation.Source.make_loop1 in
/-- The actual guard decides positivity without changing the mathematical
locals or heap. Its contract accepts any additional entry-heap condition. -/
theorem guard_model_spec (out : Buffer .nat) (count n value remaining : Nat)
    (pre : Heap → Prop) :
    guard_model_contract (loopModel out count n value) remaining pre
      (fun heap again next finish =>
        again = decide (0 < remaining) ∧ next = remaining ∧ finish = heap) := by
  rw [guard_model_contract_iff]
  intro heap _
  simp only [guard_model_action, loopModel]
  rw [guard_eq]
  mvcgen
  simp_all [visible, modelEquiv, mkModel]

open Implementation.Source.make_loop1 in
/-- The worker's actual contents contract proves one mathematical loop round.
Continuing rounds update the invariant; a local return supplies the final result. -/
theorem body_model_spec (out : Buffer .nat) (count n value : Nat)
    {remaining : Nat} {heap : Heap}
    (current : invariant out count n value remaining heap) (active : 0 < remaining) :
    body_model_contract (loopModel out count n value) remaining (fun entry => entry = heap)
      (fun _ next finish => next = remaining - 1 ∧ invariant out count n value next finish)
      (fun _ returned next finish => returned = out ∧ next = 0 ∧
        out.Contents finish (resultContents count n value)) := by
  rw [body_model_contract_iff]
  rintro _ rfl
  have workerSpec := Implementation.Source.work_spec
    (work_total (if remaining < count ∧ 0 < n then value else 0))
  simp only [body_model_action, loopModel]
  rw [body_eq]
  mvcgen [workerSpec]
  rename_i entry same
  subst entry
  refine ⟨current.2, ?_⟩
  intro returned finish updated
  cases returned
  mvcgen
  all_goals
    have advanced := invariant_step out count n value current active updated
  · rename_i finished
    have zero : remaining - 1 = 0 := by simpa using finished
    simpa [loopModel, visible, modelEquiv, mkModel, zero] using
      invariant_done out count n value advanced (by omega)
  · simpa [loopModel, visible, modelEquiv, mkModel] using advanced

open Implementation.Source.make_loop1 in
/-- The loop's actual guard preserves its full lexical state and decides the
ordinary positivity test used by the termination argument. -/
theorem guard_eval (remaining : Nat) (out : Buffer .nat) (count n value : Nat) :
    Implementation.Source.make_loop1.guard_completion_contract
      (fun locals _ => locals = (remaining, out, count, n, value, ()))
      (fun _ heap again locals finish => again = decide (0 < remaining) ∧
        locals = (remaining, out, count, n, value, ()) ∧ finish = heap) := by
  simpa [guard_model_contract, loopModel, and_assoc, and_left_comm, and_comm] using
    guard_model_spec out count n value remaining (fun _ => True)

open Implementation.Source.make_loop1 in
/-- A real loop body calls the scoped worker and decreases only the remaining
count. Its contents contract and complete local update also serve the separate
resource proof; neither needs to re-prove the worker's behavior. -/
theorem body_spec (out : Buffer .nat) (count n value : Nat)
    {remaining : Nat} {heap : Heap}
    (current : invariant out count n value remaining heap) (active : 0 < remaining) :
    Implementation.Source.make_loop1.body_completion_contract
      (fun locals entry => locals = (remaining, out, count, n, value, ()) ∧ entry = heap)
      (fun _ _ locals finish => locals = (remaining - 1, out, count, n, value, ()) ∧
        invariant out count n value (remaining - 1) finish)
      (fun _ _ returned locals finish => returned = out ∧
        locals = (0, out, count, n, value, ()) ∧
          out.Contents finish (resultContents count n value)) := by
  simpa [body_model_contract, loopModel, and_assoc, and_left_comm, and_comm] using
    body_model_spec out count n value current active

open Implementation.Source.make_loop1 in
/-- Lean's existing well-founded measure proves termination of the actual
source loop. The relation concerns mathematical progress, not a machine budget;
its body contract carries the current heap through every real call. -/
theorem loop_spec (out : Buffer .nat) (count n value remaining : Nat) :
    Implementation.Source.make_loop1.completion_contract
      (fun locals heap => locals = (remaining, out, count, n, value, ()) ∧
        invariant out count n value remaining heap)
      (fun _ _ locals finish => ∃ left,
        locals = (left, out, count, n, value, ()) ∧
          out.Contents finish (resultContents count n value))
      (fun _ _ returned locals finish => returned = out ∧
        locals = (0, out, count, n, value, ()) ∧
          out.Contents finish (resultContents count n value)) := by
  have specification := model_completion_contract
    (loopModel out count n value) (fun left => decide (0 < left))
    (invariant out count n value) (fun left next => next = left - 1) (measure id).wf
    (fun _ finish => out.Contents finish (resultContents count n value))
    (fun returned left finish => returned = out ∧ left = 0 ∧
      out.Contents finish (resultContents count n value))
    (fun left heap _ => guard_model_spec out count n value left (fun entry => entry = heap))
    (fun _ _ current active => body_model_spec out count n value current
      (of_decide_eq_true active))
    (by
      rintro left next heap _ active rfl
      have positive : 0 < left := of_decide_eq_true active
      change left - 1 < left
      omega)
    (by
      intro left heap current stopped
      exact invariant_done out count n value current (of_decide_eq_false stopped)) remaining
  simpa [loopModel, and_assoc, and_left_comm, and_comm] using specification

/-- One source declaration allocates the surviving result and repeatedly uses
the same nested scratch scopes. Its successful result has the ordinary array
contents, for every count and every initial heap, including both empty cases. -/
theorem make_spec (count n value : Nat) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (Implementation.Source.make count n value)
      (fun _ => ⟨True⟩)
      (fun out finish => ⟨out.Contents finish (resultContents count n value)⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)) := by
  have loopSpec := fun (out : Buffer .nat) (remaining : Nat) =>
    Implementation.Source.make_loop1.completion_spec
      (loop_spec out count n value remaining) remaining out count n value
  rw [Implementation.Source.make_eq]
  mvcgen [loopSpec]
  intro out finish allocated initialized growth fresh
  mvcgen [loopSpec]
  refine ⟨⟨trivial, invariant_initial out count n value (by
    simpa only [Array.replicate_one] using initialized)⟩, ?_, ?_⟩
  · rintro locals heap ⟨left, same, observed⟩
    subst locals
    mvcgen
  · rintro returned locals heap sameReturned sameLocals observed
    subst returned
    subst locals
    mvcgen

/-- The mathematical contract supplies actual finite source evaluation and
the retained output contents without a separate termination or budget proof. -/
theorem make_eval (count n value : Nat) (heap : Heap) :
    ∃ out finish, Implementation.Source.make count n value heap = Part.some (.ok out, finish) ∧
      out.Contents finish (resultContents count n value) :=
  (triple_iff_eval _ _ _).mp (make_spec count n value) heap trivial

/-- The same named declaration's source contract is ready for the separate
range, capacity, instruction-count and physical-space proofs. -/
theorem make_total :
    FunctionTotal Implementation.Source.program Implementation.Source.makeId (fun _ _ => True)
      (fun args _ out finish =>
        out.Contents finish (resultContents args.head args.tail.head args.tail.tail.head)) := by
  apply (Implementation.Source.make_total_iff (fun _ _ _ _ => True)
    (fun count n value _ out finish => out.Contents finish (resultContents count n value))).mpr
  intro count n value heap _
  exact make_eval count n value heap

end Complexity.Language.Examples.Scope
