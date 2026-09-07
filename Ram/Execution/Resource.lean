/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Nat.Basic
import Ram.Execution

/-!
# Resource observations along actual execution prefixes

`PrefixBound observe code n start bound` bounds the observation at every
state reached by a real prefix of length `k ≤ n`. The initial state is included
at `k = 0`; when an `n`-step execution exists, its final state is included too.
`HasPeak` additionally requires that some such prefix attains the bound.

These predicates observe the existing `Ram.Exec` relation. They neither add
instructions nor assign execution costs. An observation is not automatically
a live-space measure: that interpretation requires a separate representation
and correctness argument. In particular, no heap-capacity or active-stack
interpretation is attached to these generic results.

The existence theorem assumes an actual finite execution. The peak is only
an existential witness in `Prop`, not a value extracted from an execution
proof. Sequential time lengths add, whereas sequential peaks combine by `max`.
-/

namespace Ram

/-- Every actually reachable prefix state, including the initial and final
states, satisfies the proposed observation bound. -/
def PrefixBound (observe : State w → Nat) (code : Code) (n : Nat)
    (start : State w) (bound : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ state, Exec code k start state → observe state ≤ bound

/-- A bound attained by an actual execution prefix. Pair this with an
`Exec code n start finish` proof when certifying a complete execution. -/
structure HasPeak (observe : State w → Nat) (code : Code) (n : Nat)
    (start : State w) (peak : Nat) : Prop where
  bound : PrefixBound observe code n start peak
  attained : ∃ k, k ≤ n ∧ ∃ state, Exec code k start state ∧ observe state = peak

namespace PrefixBound

variable {observe other : State w → Nat} {code : Code}
variable {n m a b : Nat} {start middle finish : State w}

@[simp] theorem zero_iff : PrefixBound observe code 0 start b ↔ observe start ≤ b := by
  constructor
  · intro h
    exact h 0 (Nat.le_refl _) start (.refl start)
  · intro h k hk state he
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    have hs := Exec.zero_iff.mp he
    simpa only [← hs] using h

theorem initial (h : PrefixBound observe code n start b) : observe start ≤ b :=
  h 0 (Nat.zero_le _) start (.refl start)

theorem final (h : PrefixBound observe code n start b)
    (he : Exec code n start finish) : observe finish ≤ b :=
  h n (Nat.le_refl _) finish he

/-- Enlarge the observation bound without changing the run. -/
theorem mono (h : PrefixBound observe code n start a) (hab : a ≤ b) :
    PrefixBound observe code n start b :=
  fun k hk state he => (h k hk state he).trans hab

/-- A bound on a longer interval also bounds each shorter prefix interval. -/
theorem restrict_time (h : PrefixBound observe code n start b) (hmn : m ≤ n) :
    PrefixBound observe code m start b :=
  fun k hk state he => h k (hk.trans hmn) state he

/-- Pointwise domination of state observations transports a prefix bound. -/
theorem observe_mono (h : PrefixBound observe code n start b)
    (hle : ∀ state, other state ≤ observe state) :
    PrefixBound other code n start b :=
  fun k hk state he => (hle state).trans (h k hk state he)

/-- Monotone postprocessing, for example conversion from words to bits at a
fixed width, transports the bound without changing the observed execution. -/
theorem map (h : PrefixBound observe code n start b) {f : Nat → Nat}
    (hf : Monotone f) : PrefixBound (fun state => f (observe state)) code n start (f b) :=
  fun k hk state he => hf (h k hk state he)

/-- A real first transition separates the initial observation from the
remaining prefixes. The transition itself is still `Ram.step`. -/
theorem cons_iff (hs : step code start = some middle) :
    PrefixBound observe code (n + 1) start b ↔
      observe start ≤ b ∧ PrefixBound observe code n middle b := by
  constructor
  · intro h
    refine ⟨h.initial, ?_⟩
    intro k hk state he
    exact h (k + 1) (Nat.add_le_add_right hk 1) state (.cons hs he)
  · rintro ⟨hstart, hrest⟩ k hk state he
    cases k with
    | zero =>
        have heq := Exec.zero_iff.mp he
        simpa only [← heq] using hstart
    | succ k =>
        obtain ⟨next, hstep, htail⟩ := Exec.succ_iff.mp he
        have hnext : next = middle := step_deterministic hstep hs
        subst next
        exact hrest k (by omega) state htail

/-- Exact decomposition at a fixed, actually executed cut point. -/
theorem add_iff (first : Exec code n start middle) :
    PrefixBound observe code (n + m) start b ↔
      PrefixBound observe code n start b ∧ PrefixBound observe code m middle b := by
  constructor
  · intro h
    refine ⟨h.restrict_time (Nat.le_add_right _ _), ?_⟩
    intro k hk state he
    exact h (n + k) (Nat.add_le_add_left hk n) state (first.trans he)
  · rintro ⟨left, right⟩ k hk state he
    by_cases hkn : k ≤ n
    · exact left k hkn state he
    · have hk_eq : n + (k - n) = k := by omega
      have hsplit : Exec code (n + (k - n)) start state := by
        rwa [hk_eq]
      obtain ⟨cut, hfirst, hrest⟩ := hsplit.split
      have hcut : cut = middle := hfirst.deterministic first
      subst cut
      exact right (k - n) (by omega) state hrest

/-- Concatenating executed segments adds their lengths and takes the maximum
of their observation bounds, not their sum. -/
theorem trans (first : Exec code n start middle)
    (left : PrefixBound observe code n start a)
    (right : PrefixBound observe code m middle b) :
    PrefixBound observe code (n + m) start (max a b) :=
  (add_iff first).mpr ⟨left.mono (Nat.le_max_left _ _), right.mono (Nat.le_max_right _ _)⟩

end PrefixBound

namespace HasPeak

variable {observe : State w → Nat} {code : Code}
variable {n m p q : Nat} {start middle finish : State w}

/-- The zero-transition interval contains exactly its initial state. -/
theorem zero (observe : State w → Nat) (code : Code) (start : State w) :
    HasPeak observe code 0 start (observe start) :=
  ⟨PrefixBound.zero_iff.mpr (Nat.le_refl _),
    ⟨0, Nat.le_refl _, start, .refl start, rfl⟩⟩

/-- An attained peak is below every bound on the same prefix interval. -/
theorem le_bound (h : HasPeak observe code n start p)
    (hb : PrefixBound observe code n start q) : p ≤ q := by
  obtain ⟨k, hk, state, he, hvalue⟩ := h.attained
  simpa only [hvalue] using hb k hk state he

theorem unique (left : HasPeak observe code n start p)
    (right : HasPeak observe code n start q) : p = q :=
  Nat.le_antisymm (left.le_bound right.bound) (right.le_bound left.bound)

/-- Increasing the observed execution interval cannot decrease its peak. -/
theorem le_of_prefix (left : HasPeak observe code n start p)
    (right : HasPeak observe code m start q) (hnm : n ≤ m) : p ≤ q :=
  left.le_bound (right.bound.restrict_time hnm)

/-- Monotone postprocessing preserves both the bound and its attainment. -/
theorem map (h : HasPeak observe code n start p) {f : Nat → Nat} (hf : Monotone f) :
    HasPeak (fun state => f (observe state)) code n start (f p) := by
  refine ⟨h.bound.map hf, ?_⟩
  obtain ⟨k, hk, state, he, hvalue⟩ := h.attained
  exact ⟨k, hk, state, he, congrArg f hvalue⟩

/-- Exact peaks compose by maximum at an actual execution cut point. -/
theorem add (first : Exec code n start middle)
    (left : HasPeak observe code n start p) (right : HasPeak observe code m middle q) :
    HasPeak observe code (n + m) start (max p q) := by
  refine ⟨PrefixBound.trans first left.bound right.bound, ?_⟩
  by_cases hpq : p ≤ q
  · obtain ⟨k, hk, state, he, hvalue⟩ := right.attained
    exact ⟨n + k, Nat.add_le_add_left hk n, state, first.trans he,
      hvalue.trans (Nat.max_eq_right hpq).symm⟩
  · obtain ⟨k, hk, state, he, hvalue⟩ := left.attained
    exact ⟨k, hk.trans (Nat.le_add_right _ _), state, he,
      hvalue.trans (Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hpq))).symm⟩

/-- Every actual finite execution has an attained peak. This existential
statement stays in `Prop`; no data is extracted from a proof of `Exec`. -/
theorem exists_of_exec (he : Exec code n start finish) :
    ∃ p, HasPeak observe code n start p := by
  induction he with
  | refl state => exact ⟨observe state, zero observe code state⟩
  | @cons n start middle finish hs _ ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨max (observe start) p, ?_⟩
      refine ⟨(PrefixBound.cons_iff hs).mpr
        ⟨Nat.le_max_left _ _, hp.bound.mono (Nat.le_max_right _ _)⟩, ?_⟩
      by_cases hsp : observe start ≤ p
      · obtain ⟨k, hk, state, he, hvalue⟩ := hp.attained
        exact ⟨k + 1, Nat.add_le_add_right hk 1, state, .cons hs he,
          hvalue.trans (Nat.max_eq_right hsp).symm⟩
      · exact ⟨0, Nat.zero_le _, start, .refl start,
          (Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hsp))).symm⟩

end HasPeak

end Ram
