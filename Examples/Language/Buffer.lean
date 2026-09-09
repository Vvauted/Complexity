/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Std.Tactic.Do

/-!
# Reading, calling, writing and returning a borrowed buffer

The source program reads the current first cell, calls a real branching helper,
writes its returned value, takes a full slice and returns that actual view.
Its specification uses ordinary native array contents and `Array.set`. A slice
does not copy storage: the returned handle is the original view, now observing
the shared write. All other cells of the view retain their original values.

The proof uses generated function equations and the shared heap contracts,
without exposing object storage, typed environment construction or registers.
This file establishes source behavior; machine realization and cost are separate.
-/

namespace Complexity.Language.Examples.BorrowedBuffer

open scoped Part.TotalCorrectness

source_program Implementation where
  def clamp (x : Nat) (limit : Nat) : Nat := do
    if x ≤ limit then
      return x
    else
      return limit

  def clipHead (xs : Buffer Nat) (limit : Nat) : Buffer Nat := do
    let head ← xs.get 0
    let updated ← clamp head limit
    xs.set 0 updated
    let ys ← xs.slice 0 xs.length
    return ys

/-- The branching helper computes the ordinary mathematical minimum and
preserves any current heap, without assuming that heap is empty. -/
theorem clamp_eval (x limit : Nat) :
    Implementation.clamp x limit =
      (pure (min x limit) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [Implementation.clamp_eq]
  by_cases small : x ≤ limit
  · simp only [decide_eq_true_eq, if_pos small, Nat.min_eq_left small]
  · simp only [decide_eq_true_eq, if_neg small,
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))]

/-- Generated contract conversion reuses the ordinary helper proof directly. -/
theorem clamp_total :
    FunctionTotal Implementation.program Implementation.clampId (fun _ _ => True)
      (fun args heap value finish =>
        value = min args.head args.tail.head ∧ finish = heap) := by
  apply (Implementation.clamp_total_iff (fun _ _ _ => True)
    (fun x limit heap value finish => value = min x limit ∧ finish = heap)).mpr
  intro x limit heap _
  exact ⟨min x limit, heap, congrFun (clamp_eval x limit) heap, rfl, rfl⟩

/-- Native verification composes the public read, write and slice specifications.
The remaining conditions concern only ordinary array contents and the returned view. -/
theorem clipHead_spec (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    (nonempty : 0 < contents.size) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (Implementation.clipHead xs limit)
      (fun heap => ⟨xs.Contents heap contents⟩)
      (fun view finish => ⟨view = xs ∧
        view.Contents finish (contents.set 0 (min contents[0] limit) nonempty)⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)) := by
  rw [Implementation.clipHead_eq]
  simp only [clamp_eval, pure_bind]
  mvcgen
  rename_i heap observed
  refine ⟨contents, nonempty, observed, ?_⟩
  mvcgen
  refine ⟨contents, nonempty, observed, ?_⟩
  intro finish _ updated
  mvcgen
  constructor
  · omega
  · mvcgen

/-- The same native triple establishes actual finite source evaluation and its
final-heap contents, rather than only a partial-correctness implication. -/
theorem clipHead_eval (xs : Buffer .nat) (limit : Nat) {heap : Heap} {contents : Array Nat}
    (observed : xs.Contents heap contents) (nonempty : 0 < contents.size) :
    ∃ finish, Implementation.clipHead xs limit heap = Part.some (.ok xs, finish) ∧
      xs.Contents finish (contents.set 0 (min contents[0] limit) nonempty) := by
  obtain ⟨view, finish, returned, same, updated⟩ :=
    (triple_iff_eval _ _ _).mp (clipHead_spec xs limit contents nonempty) heap observed
  subst view
  exact ⟨finish, returned, updated⟩

/-- An ordinary array specification of the same declaration, obtained through
its generated curried contract equivalence rather than source constructor proofs. -/
theorem clipHead_total (contents : Array Nat) (nonempty : 0 < contents.size) :
    FunctionTotal Implementation.program Implementation.clipHeadId
      (fun args heap => args.head.Contents heap contents)
      (fun args _ value finish => value = args.head ∧
        value.Contents finish (contents.set 0 (min contents[0] args.tail.head) nonempty)) := by
  apply (Implementation.clipHead_total_iff
    (fun xs _ heap => xs.Contents heap contents)
    (fun xs limit _ value finish => value = xs ∧
      value.Contents finish (contents.set 0 (min contents[0] limit) nonempty))).mpr
  intro xs limit heap observed
  obtain ⟨finish, execution, updated⟩ := clipHead_eval xs limit observed nonempty
  exact ⟨xs, finish, execution, rfl, updated⟩

end Complexity.Language.Examples.BorrowedBuffer
