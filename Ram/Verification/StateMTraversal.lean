/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.StateM
import Init.Data.List.Control

/-!
# Native list traversal implemented by a fixed RAM loop

`Refines.stateM_forM` connects ordinary `List.forM` to one fixed source while
loop. The representation tracks a logical remaining list and an ordinary
model state. Each actual body execution implements the native action for the
next represented element and consumes that element in the representation.

The list is ghost data, not a free RAM iterator: the actual guard must agree
with whether it is empty, and the body refinement proves all runtime loads,
updates and safety conditions. Neither the body nor the while syntax depends
on the list. Native list recursion supplies termination and the returned
value/final-state pair; clients need no separate pure loop evaluator or result
recurrence. Mathematical postconditions can be attached using the existing
native `StateM` specification bridge and then passed to further native binds.
-/

namespace Ram.Source.Refines

universe u v

variable {α : Type u} {σ : Type v} {program : Program} {heapLimit depth : Nat}
variable {condition : Expr} {body : Stmt} {rep : List α → σ → State w → Prop}

/-- A single fixed RAM loop implements a native stateful list traversal.
The representation retains the abstract final state at the empty suffix;
registers, heap bounds, frames and mathematical invariants can remain in it.
No instruction budget or input-dependent source unrolling is introduced. -/
theorem stateM_forM (action : α → StateM σ PUnit)
    (reads : ∀ xs state s, rep xs state s →
      condition.ReadsBelow heapLimit s.regs s.mem)
    (guard : ∀ xs state s, rep xs state s → (s.eval condition ≠ 0 ↔ xs ≠ []))
    (iteration : ∀ x xs, Refines program heapLimit depth body
      (rep (x :: xs)) (fun result => rep xs result.2) (action x).run)
    (xs : List α) :
    Refines program heapLimit depth (.while condition body)
      (rep xs) (fun result => rep [] result.2) (List.forM xs action).run := by
  induction xs with
  | nil =>
      intro state s represented
      have stopped : s.eval condition = 0 := by
        by_contra nonzero
        exact ((guard [] state s represented).mp nonzero) rfl
      refine ⟨s, .whileFalse (reads [] state s represented) stopped, ?_⟩
      simpa only [List.forM_eq_forM, List.forM_nil, StateT.run_pure] using represented
  | cons x xs ih =>
      intro state s represented
      have continuing : s.eval condition ≠ 0 :=
        (guard (x :: xs) state s represented).mpr (by simp)
      obtain ⟨middle, first, next⟩ := iteration x xs state s represented
      obtain ⟨finish, rest, post⟩ := ih ((action x).run state).2 middle next
      refine ⟨finish, .whileTrue (reads (x :: xs) state s represented)
        continuing first rest, ?_⟩
      simpa only [List.forM_eq_forM, List.forM_cons, StateT.run_bind] using post

end Ram.Source.Refines
