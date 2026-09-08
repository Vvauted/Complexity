/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Control.State
import Init.Data.List.Control

/-!
# List traversal with a state accumulator

A `List.forM` traversal which modifies an accumulator has the same final state
as `List.foldl`. This equation is about ordinary Lean computations, independently
of a machine model, word representation or execution cost.
-/

namespace List

universe u v

/-- Repeated state updates along a list compute the ordinary left fold. -/
theorem forM_modify_run {α : Type u} {σ : Type v} (step : σ → α → σ)
    (xs : List α) (initial : σ) :
    ((List.forM xs (fun x => _root_.modify (fun s => step s x)) :
      StateM σ PUnit).run initial).2 = xs.foldl step initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      change ((List.forM xs (fun x => _root_.modify (fun s => step s x)) :
        StateM σ PUnit).run (step initial x)).2 = xs.foldl step (step initial x)
      exact ih _

end List
