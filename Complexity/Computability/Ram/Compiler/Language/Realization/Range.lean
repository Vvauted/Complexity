/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop
import Complexity.Language.Eval.Locals.Range

/-!
# Realizing pure native finite ranges

Native guard and body observations expose the actual cursor, mutable values,
fixed captures and heap. A high-level invariant supplies the word-range and
callee-realization conditions of the same source blocks. Only normal body
completion must preserve that invariant, after the actual cursor increment;
an early return neither increments the cursor nor starts another round.

`RealizationWP.while_range_encoded_of_total` retains an existing source total
specification and its postconditions. `RealizationWP.while_range_encoded_invariant`
obtains finite source execution directly from the existing native range
observation theorem and retains the invariant on normal exit. Its weaker
`RealizationWP.while_range_encoded` corollary forgets that exit property. No rule
introduces a second termination argument, block contract, execution semantics
or instruction budget.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace RealizationWP

private theorem while_normal_invariant_of_exec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    {entry finish : Complexity.Language.State Γ}
    (execution : Complexity.Language.Exec program (.while guard body) entry finish .normal)
    (exit : ∀ current finish, invariant current →
      Complexity.Language.Exec program guard current finish (.returned false) → invariant finish)
    (preserve : ∀ current afterGuard afterBody, invariant current →
      Complexity.Language.Exec program guard current afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal → invariant afterBody)
    (initial : invariant entry) : invariant finish := by
  have lift : ∀ {Δ : List Ty} {σ : Ty}
      {statement : Complexity.Language.Stmt signatures Δ σ}
      {start stop : Complexity.Language.State Δ} {outcome : Control σ},
      Complexity.Language.Exec program statement start stop outcome →
      ∀ (nextGuard : Complexity.Language.Stmt signatures Δ .bool)
        (nextBody : Complexity.Language.Stmt signatures Δ σ)
        (nextInvariant : Complexity.Language.State Δ → Prop),
        statement = .while nextGuard nextBody → outcome = .normal →
        (∀ current finish, nextInvariant current →
          Complexity.Language.Exec program nextGuard current finish (.returned false) →
            nextInvariant finish) →
        (∀ current afterGuard afterBody, nextInvariant current →
          Complexity.Language.Exec program nextGuard current afterGuard (.returned true) →
          Complexity.Language.Exec program nextBody afterGuard afterBody .normal →
            nextInvariant afterBody) →
        nextInvariant start → nextInvariant stop := by
    intro Δ σ statement start stop outcome actual
    induction actual <;>
      intro nextGuard nextBody nextInvariant same normal exit preserve initial <;> cases same
    case whileFalse test ih => exact exit _ _ initial test
    case whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact ihRest _ _ _ rfl normal exit preserve (preserve _ _ _ initial test iteration)
    case whileReturn => cases normal
    case whileFault => cases normal
    case whileGuardFault => cases normal
    case whileGuardMissingReturn => cases normal
  exact lift execution guard body invariant rfl rfl exit preserve initial

private theorem range_total_encoded
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured α : Type} (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat) (positive : 0 < stride)
    (encode : α → Value result) (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable,
      Complexity.Language.Stmt.observe view guard program ((index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      Complexity.Language.Stmt.observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (start : Nat) (mutable : Mutable) (heap : Heap) :
    Complexity.Language.TotalWP program (.while guard body)
      (fun _ => True) (fun _ _ => True) ⟨view.symm ((start, mutable), captures), heap⟩ := by
  let outcome := Id.run (forIn (m := Id)
    (⟨start, stop, stride, positive⟩ : Std.Legacy.Range)
    ((none, (start, mutable)) : Option α × (Nat × Mutable))
    (fun index state =>
      let iteration := step index state.2.2
      iteration.1.elim
        (pure (ForInStep.yield (none, (index + stride, iteration.2))))
        (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
  have observed : Complexity.Language.Stmt.observe view (.while guard body) program
      ((start, mutable), captures) heap =
      Part.some ((outcome.1.elim Control.normal (fun value => Control.returned (encode value)),
        (outcome.2, captures)), heap) :=
    congrFun (Complexity.Language.Stmt.observe_while_eq_forIn_range_step_encoded
      view program guard body captures stop stride positive encode step guardEq bodyEq
      start mutable) heap
  refine ⟨⟨view.symm (outcome.2, captures), heap⟩, _,
    Complexity.Language.Stmt.observe_eq_some_iff.mp observed, ?_⟩
  cases outcome.1 <;> trivial

/-- Realize an already total source range while retaining its postconditions.
The only preservation obligation concerns the native next value of a normal
body step. Guard and body realization still check their actual operations,
including the cursor increment on a normal path and encoded early returns. -/
theorem while_range_encoded_of_total
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured α : Type} {w depth : Nat}
    (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat)
    (encode : α → Value result) (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable,
      Complexity.Language.Stmt.observe view guard program ((index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      Complexity.Language.Stmt.observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (invariant : Nat → Mutable → Heap → Prop)
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {start : Nat} {mutable : Mutable} {heap : Heap}
    (total : Complexity.Language.TotalWP program (.while guard body) normal returned
      ⟨view.symm ((start, mutable), captures), heap⟩)
    (guardRealizable : ∀ index state heap, invariant index state heap →
      RealizationWP program w depth guard (fun _ => False) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (bodyRealizable : ∀ index state heap, invariant index state heap → index < stop →
      RealizationWP program w depth body (fun _ => True) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (preserve : ∀ index state next heap, invariant index state heap → index < stop →
      step index state = (none, next) → invariant (index + stride) next heap)
    (initial : invariant start mutable heap) :
    RealizationWP program w depth (.while guard body) normal returned
      ⟨view.symm ((start, mutable), captures), heap⟩ := by
  have guardTrue {index : Nat} {state : Mutable} {entry finish : Heap}
      {after : (Nat × Mutable) × Captured}
      (tested : Complexity.Language.Stmt.observe view guard program
        ((index, state), captures) entry = Part.some ((.returned true, after), finish)) :
      index < stop ∧ after = ((index, state), captures) ∧ finish = entry := by
    rw [guardEq index state] at tested
    have same := Part.some_injective tested
    have controlEq := congrArg (fun outcome => outcome.1.1) same
    have inside : index < stop := by
      simpa only [Control.returned.injEq, decide_eq_true_eq] using controlEq
    exact ⟨inside, (congrArg (fun outcome => outcome.1.2) same).symm,
      (congrArg Prod.snd same).symm⟩
  have bodyNormal {index : Nat} {state : Mutable} {entry finish : Heap}
      {after : (Nat × Mutable) × Captured} (inside : index < stop)
      (iterated : Complexity.Language.Stmt.observe view body program
        ((index, state), captures) entry = Part.some ((.normal, after), finish)) :
      ∃ next, step index state = (none, next) ∧
        after = ((index + stride, next), captures) ∧ finish = entry := by
    rw [bodyEq index state inside] at iterated
    cases outcome : step index state with
    | mk returned next =>
        cases returned with
        | none =>
            simp only [outcome] at iterated
            have same := Part.some_injective iterated
            exact ⟨next, rfl, (congrArg (fun output => output.1.2) same).symm,
              (congrArg Prod.snd same).symm⟩
        | some value =>
            simp only [outcome] at iterated
            have impossible : (Control.returned (encode value) : Control result) = .normal :=
              congrArg (fun output => output.1.1) (Part.some_injective iterated)
            cases impossible
  apply while_observe_of_total view
    (invariant := fun locals heap =>
      locals.2 = captures ∧ invariant locals.1.1 locals.1.2 heap) total
  · rintro ⟨⟨index, state⟩, fixed⟩ entry ⟨same, current⟩
    change fixed = captures at same
    subst fixed
    exact guardRealizable index state entry current
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after finish ⟨same, current⟩ tested
    change fixed = captures at same
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    exact bodyRealizable index state _ current inside
  · rintro ⟨⟨index, state⟩, fixed⟩ entry after afterHeap finish finishHeap
      ⟨same, current⟩ tested iterated
    change fixed = captures at same
    subst fixed
    obtain ⟨inside, rfl, rfl⟩ := guardTrue tested
    obtain ⟨next, nextEq, rfl, rfl⟩ := bodyNormal inside iterated
    exact ⟨rfl, preserve index state next _ current inside nextEq⟩
  · exact ⟨rfl, initial⟩

/-- Realize a pure positive-step source range and retain its invariant and
fixed captures on normal exit. Invariant preservation follows the already
finite source execution; it requires no second termination proof. An early
function return does not have to preserve the normal-round invariant. -/
theorem while_range_encoded_invariant
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured α : Type} {w depth : Nat}
    (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat) (positive : 0 < stride)
    (encode : α → Value result) (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable,
      Complexity.Language.Stmt.observe view guard program ((index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      Complexity.Language.Stmt.observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (invariant : Nat → Mutable → Heap → Prop)
    (guardRealizable : ∀ index state heap, invariant index state heap →
      RealizationWP program w depth guard (fun _ => False) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (bodyRealizable : ∀ index state heap, invariant index state heap → index < stop →
      RealizationWP program w depth body (fun _ => True) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (preserve : ∀ index state next heap, invariant index state heap → index < stop →
      step index state = (none, next) → invariant (index + stride) next heap)
    (start : Nat) (mutable : Mutable) (heap : Heap)
    (initial : invariant start mutable heap) :
    RealizationWP program w depth (.while guard body)
      (fun finish => (view finish.locals).2 = captures ∧
        invariant (view finish.locals).1.1 (view finish.locals).1.2 finish.heap)
      (fun _ _ => True)
      ⟨view.symm ((start, mutable), captures), heap⟩ := by
  have total := range_total_encoded view program guard body captures stop stride positive
    encode step guardEq bodyEq start mutable heap
  have realized := while_range_encoded_of_total view program guard body captures stop stride
    encode step guardEq bodyEq invariant total guardRealizable bodyRealizable preserve initial
  have observation {τ : Ty} {statement : Complexity.Language.Stmt signatures Γ τ}
      {entry finish : Complexity.Language.State Γ} {control : Control τ}
      (execution : Complexity.Language.Exec program statement entry finish control) :
      Complexity.Language.Stmt.observe view statement program (view entry.locals) entry.heap =
        Part.some ((control, view finish.locals), finish.heap) := by
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    simpa only [Equiv.symm_apply_apply] using execution
  have repack (current : Complexity.Language.State Γ)
      (fixed : (view current.locals).2 = captures) :
      view current.locals =
        (((view current.locals).1.1, (view current.locals).1.2), captures) := by
    apply Prod.ext
    · rfl
    · exact fixed
  obtain ⟨finish, control, execution, post⟩ := realized
  refine ⟨finish, control, execution, ?_⟩
  cases control with
  | normal =>
      change (view finish.locals).2 = captures ∧
        invariant (view finish.locals).1.1 (view finish.locals).1.2 finish.heap
      apply while_normal_invariant_of_exec
        (invariant := fun current => (view current.locals).2 = captures ∧
          invariant (view current.locals).1.1 (view current.locals).1.2 current.heap)
        execution.erase
      · intro current finish currentInvariant tested
        have observed := observation tested
        rw [repack current currentInvariant.1, guardEq] at observed
        have same := Part.some_injective observed
        have finishLocals : view finish.locals =
            (((view current.locals).1.1, (view current.locals).1.2), captures) :=
          (congrArg (fun outcome => outcome.1.2) same).symm
        have finishHeap : finish.heap = current.heap := (congrArg Prod.snd same).symm
        rw [finishLocals, finishHeap]
        exact ⟨rfl, currentInvariant.2⟩
      · intro current afterGuard afterBody currentInvariant tested iterated
        have observedGuard := observation tested
        rw [repack current currentInvariant.1, guardEq] at observedGuard
        have sameGuard := Part.some_injective observedGuard
        have inside : (view current.locals).1.1 < stop := by
          simpa only [Control.returned.injEq, decide_eq_true_eq] using
            congrArg (fun outcome => outcome.1.1) sameGuard
        have guardLocals : view afterGuard.locals =
            (((view current.locals).1.1, (view current.locals).1.2), captures) :=
          (congrArg (fun outcome => outcome.1.2) sameGuard).symm
        have guardHeap : afterGuard.heap = current.heap :=
          (congrArg Prod.snd sameGuard).symm
        have observedBody := observation iterated
        rw [guardLocals, guardHeap, bodyEq _ _ inside] at observedBody
        cases outcome : step (view current.locals).1.1 (view current.locals).1.2 with
        | mk returned next =>
            cases returned with
            | none =>
                simp only [outcome] at observedBody
                have sameBody := Part.some_injective observedBody
                have bodyLocals : view afterBody.locals =
                    (((view current.locals).1.1 + stride, next), captures) :=
                  (congrArg (fun result => result.1.2) sameBody).symm
                have bodyHeap : afterBody.heap = current.heap :=
                  (congrArg Prod.snd sameBody).symm
                rw [bodyLocals, bodyHeap]
                exact ⟨rfl, preserve _ _ next _ currentInvariant.2 inside outcome⟩
            | some value =>
                simp only [outcome] at observedBody
                have impossible :
                    (Control.returned (encode value) : Control result) = .normal :=
                  congrArg (fun result => result.1.1) (Part.some_injective observedBody)
                cases impossible
      · simpa only [Equiv.apply_symm_apply] using
          (show captures = captures ∧ invariant start mutable heap from ⟨rfl, initial⟩)
  | returned value => trivial
  | fault error => exact post

/-- Forget the normal-exit invariant after realizing the same pure finite
range. Normal and early-return outcomes both remain possible. -/
theorem while_range_encoded
    {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Mutable Captured α : Type} {w depth : Nat}
    (view : Env Γ ≃ (Nat × Mutable) × Captured)
    (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (captures : Captured) (stop stride : Nat) (positive : 0 < stride)
    (encode : α → Value result) (step : Nat → Mutable → Option α × Mutable)
    (guardEq : ∀ index mutable,
      Complexity.Language.Stmt.observe view guard program ((index, mutable), captures) =
        pure (.returned (decide (index < stop)), ((index, mutable), captures)))
    (bodyEq : ∀ index mutable, index < stop →
      Complexity.Language.Stmt.observe view body program ((index, mutable), captures) =
        pure (match step index mutable with
          | (none, next) => (.normal, ((index + stride, next), captures))
          | (some value, next) => (.returned (encode value), ((index, next), captures))))
    (invariant : Nat → Mutable → Heap → Prop)
    (guardRealizable : ∀ index state heap, invariant index state heap →
      RealizationWP program w depth guard (fun _ => False) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (bodyRealizable : ∀ index state heap, invariant index state heap → index < stop →
      RealizationWP program w depth body (fun _ => True) (fun _ _ => True)
        ⟨view.symm ((index, state), captures), heap⟩)
    (preserve : ∀ index state next heap, invariant index state heap → index < stop →
      step index state = (none, next) → invariant (index + stride) next heap)
    (start : Nat) (mutable : Mutable) (heap : Heap)
    (initial : invariant start mutable heap) :
    RealizationWP program w depth (.while guard body) (fun _ => True) (fun _ _ => True)
      ⟨view.symm ((start, mutable), captures), heap⟩ :=
  (while_range_encoded_invariant view program guard body captures stop stride positive
    encode step guardEq bodyEq invariant guardRealizable bodyRealizable preserve
    start mutable heap initial).mono_post (fun _ _ => True.intro) (fun _ _ _ => True.intro)

end RealizationWP

end Ram.LanguageCompiler
