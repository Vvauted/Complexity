/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Asymptotics.Polynomial
import Complexity.Computability.Ram.Array.Sort.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic complexity of the verified insertion-sort block

The explicit budget retains logarithmic searches and linear shifts. These
lemmas bound that same proved execution budget by a quadratic and expose
mathlib's `IsBigO`. The size is the number of array words; the machine uses
unit-cost word operations, not bit operations. Input loading remains outside
the preloaded-block contract and is not silently included in this claim.
-/

namespace Ram.Source.Array.Sort

/-- A concrete quadratic bound on the source sort budget, valid also at zero. -/
theorem budget_le_quadratic (n : Nat) : budget n ≤ 44 * n ^ 2 + 35 * n + 6 := by
  have hlog : Nat.clog 2 (n + 1) ≤ n :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  calc
    budget n = n * (25 * Nat.clog 2 (n + 1) + 19 * n + 35) + 6 := rfl
    _ ≤ n * (44 * n + 35) + 6 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 6
    _ = 44 * n ^ 2 + 35 * n + 6 := by ring

/-- The compiled block's actual halt contributes exactly one further step. -/
theorem budget_add_halt_le_quadratic (n : Nat) :
    budget n + 1 ≤ 44 * n ^ 2 + 35 * n + 7 := by
  have h := Nat.add_le_add_right (budget_le_quadratic n) 1
  simpa only [Nat.add_assoc] using h

/-- One coefficient handles the constant/linear prefix as well as the quadratic term. -/
theorem budget_add_halt_le_shifted_square (n : Nat) :
    budget n + 1 ≤ 44 * (n + 1) ^ 2 := by
  apply (budget_add_halt_le_quadratic n).trans
  nlinarith

/-- This is mathlib's asymptotic relation applied to the actual block budget,
including halt, with one coefficient independent of word width and contents. -/
theorem budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => (budget n + 1 : ℝ))
      (fun n => (((n + 1) ^ 2 : Nat) : ℝ)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Asymptotics.isBigO_shifted_pow_iff (f := fun n => budget n + 1) (k := 2)).mpr
      ⟨44, budget_add_halt_le_shifted_square⟩

/-- The simpler quadratic budget applies to the same program, precondition,
actual execution and functional postcondition, not just to an isolated function. -/
theorem contract_quadratic {control heapLimit depth : Nat} {functions : Program}
    {base : Word w} {xs : List (Word w)} (hw : 2 ≤ w) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit base xs) (Post heapLimit base xs)
      (fun _ => 44 * xs.length ^ 2 + 35 * xs.length + 6) := by
  intro entry hp
  obtain ⟨steps, finish, hx, hpost, hb⟩ :=
    contract (control := control) (functions := functions) (depth := depth) hw entry hp
  exact ⟨steps, finish, hx, hpost, hb.trans (budget_le_quadratic xs.length)⟩

end Ram.Source.Array.Sort
