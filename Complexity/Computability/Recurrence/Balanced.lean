/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Recurrence.Basic

/-!
# Balanced two-branch budget recurrences

The two subproblem sizes are `n / 2` and `n - n / 2`, not two copies of the
floor half. The upper bound therefore covers odd sizes as well as powers of
two. Mathlib's ceiling logarithm accounts for the height of the larger branch.

The hypothesis `T n ≤ T (n / 2) + T (n - n / 2) + toll * n` must be justified
by the real program's verified execution budgets. Its linear toll must cover
all remaining work, including calls, argument evaluation, frame management,
allocation and copying when present. It is not a user-selected cost table.

These are arithmetic comparison theorems, not a merge-sort implementation or
a machine complexity certificate. They supply concrete budgets for later
contracts; functional correctness, termination and word/stack conditions must
still be proved for the actual compiled program.
-/

namespace Recurrence

/-- The larger, ceiling-rounded half consumes exactly one logarithm level.
This is mathlib's ceiling-log recurrence specialized to a balanced split. -/
theorem clog_ceil_half_add_one {n : Nat} (hn : 2 ≤ n) :
    Nat.clog 2 (n - n / 2) + 1 = Nat.clog 2 n := by
  have hhalf : n - n / 2 = (n + 2 - 1) / 2 := by omega
  rw [hhalf]
  exact (Nat.clog_of_two_le (by decide : 1 < 2) hn).symm

/-- All-input budget: one base payment for an empty input, otherwise at most
one base payment per element and one linear toll per logarithmic level. -/
def balancedBudget (initial toll n : Nat) : Nat :=
  initial * max 1 n + toll * n * Nat.clog 2 n

@[simp] theorem balancedBudget_zero (initial toll : Nat) :
    balancedBudget initial toll 0 = initial := by
  simp [balancedBudget]

@[simp] theorem balancedBudget_one (initial toll : Nat) :
    balancedBudget initial toll 1 = initial := by
  simp [balancedBudget]

/-- A fixed outer cost can be absorbed into the base reserve on all sizes,
including zero. This is useful for a counted initial call and final halt. -/
theorem balancedBudget_add_const_le (initial toll extra n : Nat) :
    balancedBudget initial toll n + extra ≤ balancedBudget (initial + extra) toll n := by
  have h : extra ≤ extra * max 1 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left extra (le_max_left 1 n)
  simp only [balancedBudget, Nat.add_mul]
  omega

/-- Pay both unequal child budgets and the whole current linear toll from
the parent budget. No monotonicity assumption on an algorithm's cost is used. -/
theorem balancedBudget_split_le (initial toll : Nat) {n : Nat} (hn : 2 ≤ n) :
    balancedBudget initial toll (n / 2) +
        balancedBudget initial toll (n - n / 2) + toll * n ≤
      balancedBudget initial toll n := by
  have hleft : 1 ≤ n / 2 := by omega
  have hright : 1 ≤ n - n / 2 := by omega
  have hwhole : 1 ≤ n := by omega
  have hsum : n / 2 + (n - n / 2) = n := by omega
  have hlogs : Nat.clog 2 (n / 2) ≤ Nat.clog 2 (n - n / 2) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [balancedBudget, max_eq_right hleft, max_eq_right hright, max_eq_right hwhole]
  calc
    initial * (n / 2) + toll * (n / 2) * Nat.clog 2 (n / 2) +
        (initial * (n - n / 2) + toll * (n - n / 2) * Nat.clog 2 (n - n / 2)) + toll * n
      ≤ initial * (n / 2) + toll * (n / 2) * Nat.clog 2 (n - n / 2) +
        (initial * (n - n / 2) + toll * (n - n / 2) * Nat.clog 2 (n - n / 2)) + toll * n :=
      Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlogs) _) _) _
    _ = initial * (n / 2 + (n - n / 2)) +
        toll * (n / 2 + (n - n / 2)) * Nat.clog 2 (n - n / 2) + toll * n := by ring
    _ = initial * n + toll * n * (Nat.clog 2 (n - n / 2) + 1) := by rw [hsum]; ring
    _ = initial * n + toll * n * Nat.clog 2 n := by rw [clog_ceil_half_add_one hn]

/-- A one-sided balanced recurrence has the concrete upper bound
`initial * max 1 n + toll * n * Nat.clog 2 n` on every natural input.
Both base cases are retained; the recursive hypothesis is needed only at
sizes at least two, where both children are strictly smaller and positive. -/
theorem le_nlogn_of_balanced_le {T : Nat → Nat} {initial toll : Nat}
    (zero : T 0 ≤ initial) (one : T 1 ≤ initial)
    (step : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T (n - n / 2) + toll * n) :
    ∀ n, T n ≤ balancedBudget initial toll n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hzero : n = 0
      · simpa only [hzero, balancedBudget_zero] using zero
      by_cases hone : n = 1
      · simpa only [hone, balancedBudget_one] using one
      have hn : 2 ≤ n := by omega
      exact (step n hn).trans
        ((Nat.add_le_add_right (Nat.add_le_add (ih (n / 2) (by omega))
          (ih (n - n / 2) (by omega))) _).trans (balancedBudget_split_le initial toll hn))

/-- The balanced supersolution itself has an explicit shifted `n log n`
majorant on positive sizes. This applies when a program is proved directly
against the supersolution, without requiring it to satisfy a reverse recurrence. -/
theorem balancedBudget_le_shifted (initial toll : Nat) {n : Nat} (hn : 1 ≤ n) :
    balancedBudget initial toll n ≤
      (initial + toll) * ((n + 1) * Nat.clog 2 (n + 1)) := by
  have hlog : 1 ≤ Nat.clog 2 (n + 1) := Nat.clog_pos (by decide) (by omega)
  have hmax : max 1 n ≤ n + 1 := max_le (by omega) (Nat.le_succ n)
  have hbase : initial * max 1 n ≤ initial * (n + 1) * Nat.clog 2 (n + 1) := by
    have hmul : n + 1 ≤ (n + 1) * Nat.clog 2 (n + 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n + 1) hlog
    have h := Nat.mul_le_mul_left initial (hmax.trans hmul)
    simpa only [Nat.mul_assoc] using h
  have htoll : toll * n * Nat.clog 2 n ≤ toll * (n + 1) * Nat.clog 2 (n + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left toll (Nat.le_succ n))
      (Nat.clog_mono_right 2 (Nat.le_succ n))
  calc
    balancedBudget initial toll n ≤ initial * (n + 1) * Nat.clog 2 (n + 1) +
        toll * (n + 1) * Nat.clog 2 (n + 1) := Nat.add_le_add hbase htoll
    _ = (initial + toll) * ((n + 1) * Nat.clog 2 (n + 1)) := by ring

/-- Mathlib's asymptotic bound for the reusable balanced supersolution. -/
theorem balancedBudget_isBigO (initial toll : Nat) :
    Asymptotics.IsBigO Filter.atTop (fun n => (balancedBudget initial toll n : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((initial + toll : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnat := balancedBudget_le_shifted initial toll hn
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (balancedBudget initial toll n : ℝ) ≤
      (((initial + toll) * ((n + 1) * Nat.clog 2 (n + 1)) : Nat) : ℝ))

/-- Mathlib's `IsBigO` conclusion for the same recurrence, with shifted input
size in the logarithm. The concrete theorem above, unlike an eventual bound,
also retains the possibly nonzero costs at zero and one. -/
theorem isBigO_nlogn_of_balanced_le {T : Nat → Nat} {initial toll : Nat}
    (zero : T 0 ≤ initial) (one : T 1 ≤ initial)
    (step : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T (n - n / 2) + toll * n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (((n + 1) * Nat.clog 2 (n + 1) : Nat) : ℝ)) := by
  refine (Asymptotics.IsBigO.of_norm_le (g := fun n =>
    (balancedBudget initial toll n : ℝ)) ?_).trans (balancedBudget_isBigO initial toll)
  intro n
  simpa only [Real.norm_natCast] using
    (Nat.cast_le.mpr (le_nlogn_of_balanced_le zero one step n) :
      (T n : ℝ) ≤ (balancedBudget initial toll n : ℝ))

end Recurrence
