/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.List.Attach
import Init.Data.Range.Lemmas

/-!
# Termination facts for mathematical range models

Lean's well-founded preprocessing can expose facts about callback arguments
without changing the function's ordinary equation. The frontend's finite ranges
retain their usual `List.foldl` or `forIn` views; during termination checking,
each index additionally carries the range's strict upper bound.

The preprocessing equalities reuse Lean's attached-list and membership-aware
iteration laws. They change neither source lowering nor its control, heap
effects or instruction costs.
-/

namespace List

private theorem lt_stop_of_mem_range' {start stop stride index : Nat}
    (inside : index ∈ range' start ((stop - start + stride - 1) / stride) stride) :
    index < stop := by
  by_cases zero : stride = 0
  · subst stride
    simp at inside
  · exact (Std.Legacy.Range.mem_of_mem_range'
      (r := ⟨start, stop, stride, Nat.pos_of_ne_zero zero⟩) inside).upper

/-- Expose a finite range index's strict upper bound to well-founded recursion.
The bound is a proof-only callback binder; erasing it gives the original fold. -/
@[wf_preprocess] theorem foldl_range'_wf {α : Type u} (start stop stride : Nat)
    (step : α → Nat → α) (initial : α) :
    (range' start ((stop - start + stride - 1) / stride) stride).foldl step initial =
      ((range' start ((stop - start + stride - 1) / stride) stride).attachWith
        (fun index => index < stop) (fun _ inside => lt_stop_of_mem_range' inside)).foldl
        (fun state ⟨index, inside⟩ =>
          binderNameHint state step <| binderNameHint index (step state) <|
            binderNameHint inside () <| step state (wfParam index)) initial := by
  simp only [binderNameHint, wfParam, foldl_attachWith]
  exact foldl_attach.symm

end List

namespace Std.Legacy.Range

/-- Expose the upper bound of a range membership proof before checking descent
in its callback. The ordinary `forIn` equation and completion behavior are unchanged. -/
@[wf_preprocess high] theorem forIn_wf {m : Type u → Type v} [Monad m]
    {α : Type u} (range : Std.Legacy.Range) (initial : α)
    (step : Nat → α → m (ForInStep α)) :
    forIn (m := m) range initial step =
      forIn' (m := m) range initial
        (fun (index : Nat) (membership : index ∈ range) =>
          match membership with
          | ⟨_, upper, _⟩ =>
            binderNameHint index step <| binderNameHint upper () <| step index) := by
  symm
  apply forIn'_eq_forIn
  intro index membership state
  rcases membership with ⟨lower, upper, aligned⟩
  rfl

end Std.Legacy.Range
