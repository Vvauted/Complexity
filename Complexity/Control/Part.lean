/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Part
import Std.Do.WP.Monad

/-!
# Total-correctness weakest preconditions for partial values

The interpretation of `p : Part α` requires an actual returned value satisfying
the postcondition. In particular, `Part.none` has false weakest precondition:
nontermination cannot establish a specification vacuously.

The adapter reuses mathlib's `Monad Part` and `LawfulMonad Part`. Its
`Std.Do.WPMonad` instance is scoped under `Part.TotalCorrectness`; activate it
with `open scoped Part.TotalCorrectness`. This makes the choice of total
correctness explicit instead of globally selecting it over other possible
interpretations of partial computations.

No evaluator, transformer, state model or machine semantics is introduced here.
-/

namespace Part.TotalCorrectness

open Std.Do

universe u

variable {α β : Type u}

/-- Strict weakest preconditions require a returned value. Conjunctivity follows
from the uniqueness of the value of a partial computation. -/
def wp (p : Part α) : PredTrans .pure α where
  apply Q := ⟨∃ value ∈ p, (Q.1 value).down⟩
  conjunctive := by
    intro Q R
    change (∃ value ∈ p, (Q.1 value).down ∧ (R.1 value).down) ↔
      (∃ value ∈ p, (Q.1 value).down) ∧ (∃ value ∈ p, (R.1 value).down)
    constructor
    · rintro ⟨value, member, left, right⟩
      exact ⟨⟨value, member, left⟩, ⟨value, member, right⟩⟩
    · rintro ⟨⟨a, ha, left⟩, ⟨b, hb, right⟩⟩
      have same := Part.mem_unique ha hb
      subst b
      exact ⟨a, ha, left, right⟩

/-- Applying the interpretation means that the computation actually returns a
value satisfying the given native `Std.Do` postcondition. -/
@[simp] theorem wp_apply_iff (p : Part α) (Q : PostCond α .pure) :
    ((wp p).apply Q).down ↔ ∃ value ∈ p, (Q.1 value).down := Iff.rfl

/-- Returning a value uses the existing pure predicate transformer. -/
@[simp] theorem wp_some (value : α) : wp (Part.some value) = PredTrans.pure value := by
  apply PredTrans.ext
  funext Q
  apply SPred.ext_nil
  change (∃ a ∈ Part.some value, (Q.1 a).down) ↔ (Q.1 value).down
  simp only [Part.mem_some_iff, exists_eq_left]

/-- The strict interpretation preserves the existing `Part.bind`: both the
first computation and its actual continuation must return. -/
theorem wp_bind (p : Part α) (f : α → Part β) :
    wp (p.bind f) = (wp p >>= fun value => wp (f value)) := by
  apply PredTrans.ext
  funext Q
  apply SPred.ext_nil
  change (∃ b ∈ p.bind f, (Q.1 b).down) ↔
    ∃ a ∈ p, ∃ b ∈ f a, (Q.1 b).down
  constructor
  · rintro ⟨b, member, property⟩
    obtain ⟨a, ha, hb⟩ := Part.mem_bind_iff.mp member
    exact ⟨a, ha, b, hb, property⟩
  · rintro ⟨a, ha, b, hb, property⟩
    exact ⟨b, Part.mem_bind ha hb, property⟩

/-- A computation without a returned value cannot establish total correctness. -/
@[simp] theorem wp_none :
    wp (Part.none : Part α) = PredTrans.const (ps := .pure) ⟨False⟩ := by
  apply PredTrans.ext
  funext Q
  apply SPred.ext_nil
  change (∃ value ∈ (Part.none : Part α), (Q.1 value).down) ↔ False
  simp only [Part.notMem_none, false_and, exists_false]

/-- Opt into total-correctness reasoning for mathlib's existing partial-value
monad. The same interpretation extends through the standard transformer instances. -/
scoped instance instWPMonad : Std.Do.WPMonad Part .pure where
  toLawfulMonad := inferInstance
  toWP := ⟨wp⟩
  wp_pure value := wp_some value
  wp_bind p f := Part.TotalCorrectness.wp_bind p f

/-- The scoped standard interface has the same strict existential meaning. -/
@[simp] theorem std_wp_apply_iff (p : Part α) (Q : PostCond α .pure) :
    ((Std.Do.WP.wp p).apply Q).down ↔ ∃ value ∈ p, (Q.1 value).down := Iff.rfl

/-- Adequacy separates genuine termination from the postcondition on every
actual returned value. Neither direction assumes a decidable domain. -/
theorem wp_iff_dom_and_post (p : Part α) (Q : PostCond α .pure) :
    ((wp p).apply Q).down ↔ p.Dom ∧ ∀ value ∈ p, (Q.1 value).down := by
  constructor
  · rintro ⟨value, member, property⟩
    refine ⟨Part.dom_iff_mem.mpr ⟨value, member⟩, ?_⟩
    intro other otherMember
    have same := Part.mem_unique member otherMember
    exact same ▸ property
  · rintro ⟨defined, property⟩
    exact ⟨p.get defined, Part.get_mem defined, property _ (Part.get_mem defined)⟩

end Part.TotalCorrectness
