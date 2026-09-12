/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Composition
import Complexity.Language.Eval.Locals.Range

/-!
# Native finite ranges with local loop exits

`RangeControl.loop` is ordinary source syntax: a private Boolean masks the
original guard and the increment. A lowered `break` clears this Boolean; a
lowered `continue` leaves it set and skips only the remaining user body. Both
finish the lowered body normally. A function return remains `Control.returned`.
Consequently, continue performs the increment exactly once, whereas break and
function return do not execute it. A broken loop does not reevaluate its original
guard either. These are structural branches of the actual source statement,
not an identification of computations that happen to return the same value.

`observe_rangeControl_eq_forIn_range_step` connects this same statement to
Lean's native `ForInStep`. Normal completion and continue meet at `yield none`;
`done none` breaks and `done (some value)` returns from the function. The complete
view retains the private Boolean, actual cursor, mutable locals and captures.
Any additional private continuation flags belong to these retained locals.

The premises classify the actual body and increment, preserving any initial
heap. In particular, the increment premise is required only after `yield`;
there is no premise about an increment after break or return. The theorem is
budget-free and introduces neither a cost model nor an overflow assumption.
The ordinary source `Exec` and `ExecutionCost` rules still apply to every
inserted branch, flag assignment, guard evaluation and executed increment.
-/

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {Mutable Captured Locals : Type}

namespace RangeControl

/-- Test the private loop flag before running the original guard. -/
def guard (live : Atom Γ .bool) (test : Stmt signatures Γ .bool) :
    Stmt signatures Γ .bool :=
  .ite live test (.ret (.bool false))

/-- A lowered continue still reaches this increment; break clears `live`, and
a function return bypasses the second statement through ordinary sequencing. -/
def body (live : Atom Γ .bool) (iteration increment : Stmt signatures Γ result) :
    Stmt signatures Γ result :=
  .seq iteration (.ite live increment .skip)

/-- The exit-aware loop uses only the existing source statement constructors. -/
def loop (live : Atom Γ .bool) (test : Stmt signatures Γ .bool)
    (iteration increment : Stmt signatures Γ result) : Stmt signatures Γ result :=
  .while (guard live test) (body live iteration increment)

/-- A native function return exits the range; it is never a yielding step. -/
@[simp] def Valid {α β : Type} : ForInStep (Option α × β) → Prop
  | .yield (returned, _) => returned = none
  | .done _ => True

/-- Preserve the actual loop flag and cursor alongside the native result.
Only a yielding iteration advances the cursor. -/
def advance {α : Type} (stride : Nat)
    (step : Nat → Mutable → ForInStep (Option α × Mutable))
    (index : Nat) (state : Option α × (Bool × Nat × Mutable)) :
    Id (ForInStep (Option α × (Bool × Nat × Mutable))) :=
  match step index state.2.2.2 with
  | .yield (returned, next) => pure (.yield (returned, (true, index + stride, next)))
  | .done (none, next) => pure (.done (none, (false, index, next)))
  | .done (some value, next) => pure (.done (some value, (true, index, next)))

/-- A cleared flag returns false without evaluating the original guard. This
equation has no premise about that guard's effects or termination. -/
theorem observe_guard_false (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (test : Stmt signatures Γ .bool) (locals : Locals)
    (stopped : live.eval (view.symm locals) = false) :
    observe view (guard live test) program locals = pure (.returned false, locals) := by
  rw [guard, observe_ite, stopped]
  simp only [Bool.false_eq_true, if_false, observe_ret, Atom.eval]

/-- A set flag runs exactly the original guard, retaining its actual effects. -/
theorem observe_guard_true (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (test : Stmt signatures Γ .bool) (locals : Locals)
    (running : live.eval (view.symm locals) = true) :
    observe view (guard live test) program locals = observe view test program locals := by
  rw [guard, observe_ite, running, if_pos rfl]

/-- The increment after a break is not executed. In particular this rule needs
no increment correspondence, termination, range or overflow premise. -/
theorem observe_body_break (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (iteration increment : Stmt signatures Γ result)
    (initial finish : Locals)
    (iterationEq : observe view iteration program initial = pure (.normal, finish))
    (stopped : live.eval (view.symm finish) = false) :
    observe view (body live iteration increment) program initial =
      pure (.normal, finish) := by
  rw [body, observe_seq, iterationEq]
  simp only [pure_bind]
  rw [observe_ite, stopped]
  simp only [Bool.false_eq_true, if_false, observe_skip]

/-- A function return also bypasses the increment, independently of the flag. -/
theorem observe_body_return (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (iteration increment : Stmt signatures Γ result)
    (initial finish : Locals) (value : Value result)
    (iterationEq : observe view iteration program initial = pure (.returned value, finish)) :
    observe view (body live iteration increment) program initial =
      pure (.returned value, finish) := by
  rw [body, observe_seq, iterationEq]
  simp only [pure_bind]

/-- Normal completion and lowered continue both run the one actual increment
from their final mutable locals and shared heap. -/
theorem observe_body_yield (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (iteration increment : Stmt signatures Γ result)
    (initial finish : Locals)
    (iterationEq : observe view iteration program initial = pure (.normal, finish))
    (running : live.eval (view.symm finish) = true) :
    observe view (body live iteration increment) program initial =
      observe view increment program finish := by
  rw [body, observe_seq, iterationEq]
  simp only [pure_bind]
  rw [observe_ite, running, if_pos rfl]

end RangeControl

/-- An exit-aware positive-stride source loop is its native finite range.
The body premise describes the iteration before the conditional increment;
the increment premise is needed only for an actual yielding iteration.
Normal completion and continue share that yield case, whereas break and
function return preserve their actual cursor and do not evaluate the increment.
All equations retain the complete locals and the arbitrary initial heap. -/
theorem observe_rangeControl_eq_forIn_range_step
    (view : Env Γ ≃ (Bool × Nat × Mutable) × Captured)
    (program : Program signatures) (live : Atom Γ .bool)
    (guard : Stmt signatures Γ .bool) (body increment : Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat) (positive : 0 < stride)
    (step : Nat → Mutable → ForInStep (Option (Value result) × Mutable))
    (liveEq : ∀ running index mutable,
      live.eval (view.symm ((running, index, mutable), captures)) = running)
    (valid : ∀ index mutable, index < stop → RangeControl.Valid (step index mutable))
    (guardEq : ∀ index mutable,
      observe view guard program ((true, index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((true, index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      observe view body program ((true, index, mutable), captures) =
        pure (match step index mutable with
          | .yield (_, next) => (.normal, ((true, index, next), captures))
          | .done (none, next) => (.normal, ((false, index, next), captures))
          | .done (some value, next) => (.returned value, ((true, index, next), captures))))
    (incrementEq : ∀ index mutable next, index < stop →
      step index mutable = .yield (none, next) →
      observe view increment program ((true, index, next), captures) =
        pure (.normal, ((true, index + stride, next), captures)))
    (start : Nat) (mutable : Mutable) :
    observe view (RangeControl.loop live guard body increment) program
        ((true, start, mutable), captures) =
      (let outcome := Id.run (forIn (m := Id)
          ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
          ((none, (true, start, mutable)) : Option (Value result) × (Bool × Nat × Mutable))
          (RangeControl.advance stride step))
       pure (outcome.1.elim Control.normal Control.returned, (outcome.2, captures))) := by
  let decode (outcome : Option (Value result) × (Bool × Nat × Mutable)) :
      Control result × ((Bool × Nat × Mutable) × Captured) :=
    (outcome.1.elim .normal .returned, (outcome.2, captures))
  have activeGuard (index : Nat) (mutable : Mutable) :
      observe view (RangeControl.guard live guard) program ((true, index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((true, index, mutable), captures)) := by
    rw [RangeControl.observe_guard_true view program live guard _ (liveEq true index mutable)]
    exact guardEq index mutable
  have stopped (index : Nat) (mutable : Mutable) :
      observe view (RangeControl.loop live guard body increment) program
          ((false, index, mutable), captures) =
        pure (.normal, ((false, index, mutable), captures)) := by
    rw [RangeControl.loop, observe_while,
      RangeControl.observe_guard_false view program live guard _ (liveEq false index mutable)]
    simp only [pure_bind]
  have activeBody (index : Nat) (mutable : Mutable) (inside : index < stop) :
      observe view (RangeControl.body live body increment) program
          ((true, index, mutable), captures) =
        pure (match step index mutable with
          | .yield (_, next) => (.normal, ((true, index + stride, next), captures))
          | .done (none, next) => (.normal, ((false, index, next), captures))
          | .done (some value, next) => (.returned value, ((true, index, next), captures))) := by
    cases stepEq : step index mutable with
    | yield values =>
        rcases values with ⟨returned, next⟩
        have noReturn := valid index mutable inside
        simp only [stepEq, RangeControl.Valid] at noReturn
        subst returned
        rw [RangeControl.observe_body_yield view program live body increment _ _
          (by simpa only [stepEq] using bodyEq index mutable inside)
          (liveEq true index next)]
        exact incrementEq index mutable next inside stepEq
    | done values =>
        rcases values with ⟨returned, next⟩
        cases returned with
        | none =>
            exact RangeControl.observe_body_break view program live body increment _ _
              (by simpa only [stepEq] using bodyEq index mutable inside)
              (liveEq false index next)
        | some value =>
            exact RangeControl.observe_body_return view program live body increment _ _ value
              (by simpa only [stepEq] using bodyEq index mutable inside)
  have sizeSucc (index : Nat) (inside : index < stop) :
      (stop - index + stride - 1) / stride =
        (stop - (index + stride) + stride - 1) / stride + 1 := by
    exact Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside
  have finite : ∀ count start mutable, (stop - start + stride - 1) / stride = count →
      observe view (RangeControl.loop live guard body increment) program
          ((true, start, mutable), captures) =
        pure (decode (Id.run (forIn (m := Id) (List.range' start count stride)
          (none, (true, start, mutable)) (RangeControl.advance stride step)))) := by
    intro count
    induction count with
    | zero =>
        intro start mutable remaining
        have outside : ¬ start < stop := by
          have := (Nat.div_eq_zero_iff_lt positive).mp remaining
          omega
        rw [RangeControl.loop, observe_while, activeGuard]
        simp only [outside, decide_false, pure_bind, List.range'_zero, List.forIn_nil,
          Id.run, Id.instMonad, decode, Option.elim_none]
    | succ count ih =>
        intro start mutable remaining
        have inside : start < stop := by
          by_contra outside
          have empty : (stop - start + stride - 1) / stride = 0 :=
            Nat.div_eq_of_lt (by omega)
          omega
        rw [RangeControl.loop, observe_while, activeGuard]
        simp only [inside, decide_true, pure_bind]
        rw [activeBody start mutable inside]
        cases stepEq : step start mutable with
        | yield values =>
            rcases values with ⟨returned, next⟩
            have noReturn := valid start mutable inside
            simp only [stepEq, RangeControl.Valid] at noReturn
            subst returned
            simpa only [stepEq, pure_bind, List.range'_succ, List.forIn_cons,
              RangeControl.advance, Id.run, Id.instMonad] using
              ih (start + stride) next (by have := sizeSucc start inside; omega)
        | done values =>
            rcases values with ⟨returned, next⟩
            cases returned with
            | none =>
                simpa only [stepEq, pure_bind, List.range'_succ, List.forIn_cons,
                  RangeControl.advance, Id.run, Id.instMonad, decode, Option.elim_none] using
                  stopped start next
            | some value =>
                simp only [stepEq, pure_bind, List.range'_succ, List.forIn_cons,
                  RangeControl.advance, Id.run, Id.instMonad, decode, Option.elim_some]
  change observe view (RangeControl.loop live guard body increment) program
      ((true, start, mutable), captures) =
    pure (decode (Id.run (forIn (m := Id)
      ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      (none, (true, start, mutable)) (RangeControl.advance stride step))))
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact finite ((stop - start + stride - 1) / stride) start mutable rfl

end Complexity.Language.Stmt
