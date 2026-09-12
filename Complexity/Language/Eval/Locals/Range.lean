/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals
import Init.Data.Range.Lemmas

/-!
# Native finite ranges and the same source loop

`Stmt.observe_while_eq_forIn_range_step` connects an actual source `while` to Lean's
native finite `forIn`. Its premises identify the guard and one iteration of the
same source body; a native callback is not installed as source syntax. The
generated body's ordinary values may include mutable locals and structured
results. Callee correspondence, including recursive hypotheses, can be used in
the one-iteration premise.

The view retains the hidden cursor, mutable values and fixed lexical captures.
Normal iterations advance it by the positive stride; early returns retain their
actual cursor, result and final locals. Both cases preserve an arbitrary initial
heap because the supplied body correspondence is pure. The native range itself
provides finite iteration, including empty ranges, nonzero starts and non-unit
strides. No separate author-supplied termination argument, machine premise or
cost model is used.

For a native iteration that always continues, `Stmt.forIn_range_step_yield_eq_foldl`
removes the return flag and cursor bookkeeping. Ordinary list-fold mathematics
then describes the mutable result; there is no source control or heap adapter
for an algorithm author to prove. `Stmt.foldl_fst_unit` removes the final empty
lexical tuple when a loop has one mutable value, using Lean's existing fold
homomorphism theorem.
-/

namespace Std.Legacy.Range

/-- Advancing a nonempty range by its positive step removes exactly one round. -/
theorem size_eq_succ_of_start_lt (r : Range) (inside : r.start < r.stop) :
    r.size = ({ r with start := r.start + r.step } : Range).size + 1 := by
  rcases r with ⟨start, stop, stride, positive⟩
  change start < stop at inside
  change (stop - start + stride - 1) / stride =
    (stop - (start + stride) + stride - 1) / stride + 1
  by_cases before : start + stride ≤ stop
  · rw [show stop - start + stride - 1 =
        (stop - (start + stride) + stride - 1) + stride by omega,
      Nat.add_div_right _ positive]
  · have tail : (stop - (start + stride) + stride - 1) / stride = 0 :=
      Nat.div_eq_of_lt (by omega)
    rw [tail, Nat.zero_add, Nat.div_eq_iff positive]
    omega

end Std.Legacy.Range

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {Mutable Captured : Type}

/-- Remove the empty lexical tail of a single mutable value. Every step still
uses its actual value; only the unique `Unit` coordinate is discarded. -/
@[simp] theorem foldl_fst_unit {α β : Type} (step : α × Unit → β → α × Unit)
    (initial : α × Unit) (values : List β) :
    (values.foldl step initial).1 =
      values.foldl (fun value index => (step (value, ()) index).1) initial.1 := by
  symm
  apply List.foldl_hom Prod.fst
  rintro ⟨value, empty⟩ index
  cases empty
  rfl

/-- Change a pure list loop's accumulator by a commuting map. Both early
termination and continuation retain their actual mapped next state. -/
theorem forIn_list_hom {α State Mapped : Type}
    (mapState : State → Mapped)
    (step : α → State → Id (ForInStep State))
    (mappedStep : α → Mapped → Id (ForInStep Mapped))
    (stepEq : ∀ value state, mappedStep value (mapState state) =
      match step value state with
      | .done next => .done (mapState next)
      | .yield next => .yield (mapState next))
    (values : List α) (initial : State) :
    forIn (m := Id) values (mapState initial) mappedStep =
      mapState (forIn (m := Id) values initial step) := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      cases outcome : step value initial with
      | done next =>
          simp only [List.forIn_cons, stepEq, outcome, Id.instMonad]
      | yield next =>
          simpa only [List.forIn_cons, stepEq, outcome, Id.instMonad] using ih next

/-- The accumulator homomorphism for Lean's actual finite range iteration,
including early termination; no separate range evaluator is introduced. -/
theorem forIn_range_hom {State Mapped : Type}
    (mapState : State → Mapped)
    (step : Nat → State → Id (ForInStep State))
    (mappedStep : Nat → Mapped → Id (ForInStep Mapped))
    (stepEq : ∀ index state, mappedStep index (mapState state) =
      match step index state with
      | .done next => .done (mapState next)
      | .yield next => .yield (mapState next))
    (range : Std.Legacy.Range) (initial : State) :
    forIn (m := Id) range (mapState initial) mappedStep =
      mapState (forIn (m := Id) range initial step) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list_hom mapState step mappedStep stepEq
    (List.range' range.start range.size range.step) initial

/-- Encode only a finite range's optional early return. The native mutable
state is unchanged, normal steps advance the cursor, and early returns retain
their actual cursor and final mutable state. The encoding need not be invertible. -/
theorem forIn_range_step_map_return {α β : Type}
    (encode : α → β) (step : Nat → Mutable → Option α × Mutable)
    (start stop stride : Nat) (positive : 0 < stride) (initial : Mutable) :
    forIn (m := Id)
      ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      ((none, (start, initial)) : Option β × (Nat × Mutable))
      (fun index state =>
        let outcome := step index state.2.2
        (outcome.1.map encode).elim
          (pure (ForInStep.yield (none, (index + stride, outcome.2))))
          (fun value => pure (ForInStep.done (some value, (index, outcome.2))))) =
      Prod.map (Option.map encode) id
        (forIn (m := Id)
          ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
          ((none, (start, initial)) : Option α × (Nat × Mutable))
          (fun index state =>
            let outcome := step index state.2.2
            outcome.1.elim
              (pure (ForInStep.yield (none, (index + stride, outcome.2))))
              (fun value => pure (ForInStep.done (some value, (index, outcome.2)))))) := by
  apply forIn_range_hom (Prod.map (Option.map encode) id)
    (initial := ((none, (start, initial)) : Option α × (Nat × Mutable)))
  intro index state
  cases outcome : step index state.2.2 with
  | mk returned next =>
      cases returned <;> simp [outcome, Prod.map, Id.instMonad]

/-- An always-continuing native range has no early result and performs the
ordinary left fold on its mutable value. The final cursor also covers empty
ranges and a final stride beyond the stop; no execution function is defined by
this theorem. -/
@[simp] theorem forIn_range_step_yield_eq_foldl {α : Type}
    (next : Nat → Mutable → Mutable) (start stop stride : Nat)
    (positive : 0 < stride) (initial : Mutable) :
    forIn (m := Id)
      ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      ((none, (start, initial)) : Option α × (Nat × Mutable))
      (fun index state => pure (ForInStep.yield
        (none, (index + stride, next index state.2.2)))) =
      (let count := (stop - start + stride - 1) / stride
       (none, (start + count * stride,
        (List.range' start count stride).foldl (fun state index => next index state) initial))) := by
  have fold : ∀ count start initial,
      (List.range' start count stride).foldl
        (fun (state : Option α × (Nat × Mutable)) index =>
          (none, (index + stride, next index state.2.2))) (none, (start, initial)) =
        (none, (start + count * stride,
          (List.range' start count stride).foldl (fun state index => next index state) initial)) := by
    intro count
    induction count with
    | zero =>
        intro start initial
        simp only [List.range'_zero, List.foldl_nil, Nat.zero_mul, Nat.add_zero]
    | succ count ih =>
        intro start initial
        simpa only [List.range'_succ, List.foldl_cons, Nat.succ_mul, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ih (start + stride) (next start initial)
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  exact fold ((stop - start + stride - 1) / stride) start initial

/-- An always-continuing native unit-step range is the ordinary left fold on
its mutable value. This specializes the positive-stride rule. -/
@[simp] theorem forIn_range_yield_eq_foldl {α : Type}
    (next : Nat → Mutable → Mutable) (start stop : Nat) (initial : Mutable) :
    forIn (m := Id)
      ({ start := start, stop := stop, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
      ((none, (start, initial)) : Option α × (Nat × Mutable))
      (fun index state => pure (ForInStep.yield
        (none, (index + 1, next index state.2.2)))) =
      (none, (start + (stop - start),
        (List.range' start (stop - start)).foldl (fun state index => next index state) initial)) := by
  simpa only [Nat.add_sub_cancel, Nat.div_one, Nat.mul_one] using
    forIn_range_step_yield_eq_foldl (α := α) next start stop 1 Nat.zero_lt_one initial

/-- A positive-stride source loop is the corresponding native finite range, provided
its guard and body have the stated actual behavior. `none` means normal body
completion, not a default result; `some value` returns immediately. The native
accumulator retains mutable values and the cursor on early return; the actual
body equation establishes that the fixed captures survive both kinds of exit. -/
theorem observe_while_eq_forIn_range_step (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Program signatures) (guard : Stmt signatures Γ .bool)
    (body : Stmt signatures Γ result) (captures : Captured) (stop stride : Nat)
    (positive : 0 < stride)
    (step : Nat → Mutable → Option (Value result) × Mutable)
    (guardEq : ∀ index mutable, observe view guard program ((index, mutable), captures) =
      pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned value, ((index, next), captures))))
    (start : Nat) (mutable : Mutable) :
    observe view (.while guard body) program ((start, mutable), captures) =
      (let outcome := Id.run (forIn (m := Id)
          ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
          ((none, (start, mutable)) : Option (Value result) × (Nat × Mutable))
          (fun index state =>
            let iteration := step index state.2.2
            iteration.1.elim
              (pure (ForInStep.yield (none, (index + stride, iteration.2))))
              (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
       pure (outcome.1.elim Control.normal Control.returned, (outcome.2, captures))) := by
  let advance (index : Nat) (state : Option (Value result) × (Nat × Mutable)) :
      Id (ForInStep (Option (Value result) × (Nat × Mutable))) :=
    let iteration := step index state.2.2
    iteration.1.elim
      (pure (.yield (none, (index + stride, iteration.2))))
      (fun value => pure (.done (some value, (index, iteration.2))))
  let decode (outcome : Option (Value result) × (Nat × Mutable)) :
      Control result × ((Nat × Mutable) × Captured) :=
    (outcome.1.elim .normal .returned, (outcome.2, captures))
  have sizeSucc (index : Nat) (inside : index < stop) :
      (stop - index + stride - 1) / stride =
        (stop - (index + stride) + stride - 1) / stride + 1 := by
    exact Std.Legacy.Range.size_eq_succ_of_start_lt
      { start := index, stop := stop, step := stride, step_pos := positive } inside
  have finite : ∀ count start mutable, (stop - start + stride - 1) / stride = count →
      observe view (.while guard body) program ((start, mutable), captures) =
        pure (decode (Id.run (forIn (m := Id) (List.range' start count stride)
          (none, (start, mutable)) advance))) := by
    intro count
    induction count with
    | zero =>
        intro start mutable remaining
        have outside : ¬ start < stop := by
          have := (Nat.div_eq_zero_iff_lt positive).mp remaining
          omega
        rw [observe_while, guardEq]
        simp only [outside, decide_false, pure_bind, List.range'_zero, List.forIn_nil,
          Id.run, Id.instMonad, decode, Option.elim_none]
    | succ count ih =>
        intro start mutable remaining
        have inside : start < stop := by
          by_contra outside
          have empty : (stop - start + stride - 1) / stride = 0 :=
            Nat.div_eq_of_lt (by omega)
          omega
        rw [observe_while, guardEq]
        simp only [inside, decide_true, pure_bind]
        rw [bodyEq start mutable inside]
        cases stepEq : step start mutable with
        | mk returned next =>
            cases returned with
            | none =>
                simpa only [stepEq, pure_bind, List.range'_succ, List.forIn_cons,
                  advance, Id.run, Id.instMonad, Option.elim_none] using
                  ih (start + stride) next (by have := sizeSucc start inside; omega)
            | some value =>
                simp only [stepEq, pure_bind, List.range'_succ, List.forIn_cons,
                  advance, Id.run, Id.instMonad, decode, Option.elim_some]
  change observe view (.while guard body) program ((start, mutable), captures) =
    pure (decode (Id.run (forIn (m := Id)
      ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      (none, (start, mutable)) advance)))
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact finite ((stop - start + stride - 1) / stride) start mutable rfl

/-- Observe the same finite source loop through native local coordinates and
an encoded native return value. Only the returned value is mapped; the actual
cursor, mutable state, fixed captures, and heap retain the original behavior. -/
theorem observe_while_eq_forIn_range_step_encoded {α : Type}
    (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Program signatures) (guard : Stmt signatures Γ .bool)
    (body : Stmt signatures Γ result) (captures : Captured) (stop stride : Nat)
    (positive : 0 < stride) (encode : α → Value result)
    (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable, observe view guard program ((index, mutable), captures) =
      pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (start : Nat) (mutable : Mutable) :
    observe view (.while guard body) program ((start, mutable), captures) =
      (let outcome := Id.run (forIn (m := Id)
          ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
          ((none, (start, mutable)) : Option α × (Nat × Mutable))
          (fun index state =>
            let iteration := step index state.2.2
            iteration.1.elim
              (pure (ForInStep.yield (none, (index + stride, iteration.2))))
              (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
       pure (outcome.1.elim Control.normal (fun value => Control.returned (encode value)),
         (outcome.2, captures))) := by
  have actual := observe_while_eq_forIn_range_step view program guard body captures
    stop stride positive
    (fun index mutable =>
      let outcome := step index mutable
      (outcome.1.map encode, outcome.2))
    guardEq
    (by
      intro index mutable inside
      rw [bodyEq index mutable inside]
      cases stepEq : step index mutable with
      | mk returned next =>
          cases returned <;> simp only [stepEq, Option.map_none, Option.map_some])
    start mutable
  rw [forIn_range_step_map_return encode step start stop stride positive mutable] at actual
  have mapControl (returned : Option α) :
      (returned.map encode).elim (Control.normal (result := result)) Control.returned =
        returned.elim Control.normal (fun value => Control.returned (encode value)) := by
    cases returned <;> rfl
  simpa only [Id.run, Prod.map_fst, Prod.map_snd, id_eq, mapControl] using actual

/-- A unit-step source loop is the corresponding native finite range. This
specialization retains the actual cursor and mutable values on an early return. -/
theorem observe_while_eq_forIn_range (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Program signatures) (guard : Stmt signatures Γ .bool)
    (body : Stmt signatures Γ result) (captures : Captured) (stop : Nat)
    (step : Nat → Mutable → Option (Value result) × Mutable)
    (guardEq : ∀ index mutable, observe view guard program ((index, mutable), captures) =
      pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + 1, next), captures))
          | (some value, next) => (.returned value, ((index, next), captures))))
    (start : Nat) (mutable : Mutable) :
    observe view (.while guard body) program ((start, mutable), captures) =
      (let outcome := Id.run (forIn (m := Id)
          ({ start := start, stop := stop, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
          ((none, (start, mutable)) : Option (Value result) × (Nat × Mutable))
          (fun index state =>
            let iteration := step index state.2.2
            iteration.1.elim
              (pure (ForInStep.yield (none, (index + 1, iteration.2))))
              (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
       pure (outcome.1.elim Control.normal Control.returned, (outcome.2, captures))) :=
  observe_while_eq_forIn_range_step view program guard body captures stop 1
    Nat.zero_lt_one step guardEq bodyEq start mutable

end Complexity.Language.Stmt
