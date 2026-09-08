/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.List.MapIdx
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Sums along fold prefixes

Split a sum whose summand observes the accumulator before each list element.
The prefix is the ordinary `List.take` and its state is the ordinary `List.foldl`.
-/

namespace List

/-- Splitting the head also advances the accumulator used by every later
summand. This is the usual list sum, not a separate cost semantics. -/
theorem sum_mapIdx_foldl_take_cons {α σ β : Type*} [AddMonoid β]
    (step : σ → α → σ) (value : σ → α → β) (a : σ) (x : α) (xs : List α) :
    ((x :: xs).mapIdx
      (fun i y => value (((x :: xs).take i).foldl step a) y)).sum =
      value a x +
        (xs.mapIdx (fun i y => value ((xs.take i).foldl step (step a x)) y)).sum := by
  simp only [mapIdx_cons, take_zero, foldl_nil, take_succ_cons, foldl_cons, sum_cons]

end List
