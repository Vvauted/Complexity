/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Ram.Complexity.Multivariate
import Ram.Loop.Traversal

/-!
# Complexity of actual traversal occurrences

An input-dependent list records visits, not distinct values: repeated visits
are charged repeatedly. The uniform comparison uses one coefficient and one
eventual condition for all visits in each input. Mathlib supplies list sums,
their monotonicity and `IsBigO`; no execution or summation model is added.

The traversal bridge retains guard and back-edge work even when body costs
vanish. A fixed setup/termination allowance is included explicitly. It applies
to already proved machine runs, and never treats a mathematical visit list as
an uncharged implementation of the requested computation.
-/

namespace Ram.CostSum

open Filter

/-- A uniform bound on every visit controls the sum, including repeated visits
and inputs with an empty visit list. The same eventual condition covers all
currently selected occurrences. -/
theorem isBigO_list_sum_of_uniform
    {α ι : Type*} {l : Filter α} {visits : α → List ι}
    {cost majorant : α → ι → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ a ∈ visits x,
      (cost x a : ℝ) ≤ C * (majorant x a : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => (((visits x).map (cost x)).sum : ℝ))
      (fun x => (((visits x).map (majorant x)).sum : ℝ)) := by
  obtain ⟨C, hC⟩ := uniform
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with x hx
  simp only [Real.norm_natCast]
  simpa only [Nat.cast_list_sum, List.map_map,
    Function.comp_def, List.sum_map_mul_left] using List.sum_le_sum hx

/-- A common per-visit growth bound multiplies the length of the visit list,
not the number of distinct values. No decidable equality on visits is needed. -/
theorem isBigO_list_sum_length_mul_of_uniform
    {α ι : Type*} {l : Filter α} {visits : α → List ι}
    {cost : α → ι → Nat} {growth : α → Nat}
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ a ∈ visits x,
      (cost x a : ℝ) ≤ C * (growth x : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => (((visits x).map (cost x)).sum : ℝ))
      (fun x => (((visits x).length * growth x : Nat) : ℝ)) := by
  simpa only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul] using
    (isBigO_list_sum_of_uniform (majorant := fun x _ => growth x) uniform)

end Ram.CostSum

namespace Ram.Source.Traversal

open Filter

/-- Real traversal control flow costs linear work in the number of visits,
in addition to the sum of body majorants. The final `+ 1` retains the empty
traversal and fixed setup/termination costs. -/
theorem budget_isBigO_of_uniform
    {α ι : Type*} {l : Filter α} {visits : α → List ι}
    {cost majorant : α → ι → Nat} (control : Nat) (condition : Expr) (setup : Nat)
    (uniform : ∃ C : ℝ, ∀ᶠ x in l, ∀ a ∈ visits x,
      (cost x a : ℝ) ≤ C * (majorant x a : ℝ)) :
    Asymptotics.IsBigO l
      (fun x => ((budget control condition (fun a _ => cost x a) (visits x) + setup : Nat) : ℝ))
      (fun x => ((((visits x).map (majorant x)).sum + (visits x).length + 1 : Nat) : ℝ)) := by
  obtain ⟨C, hC, hsum⟩ := (CostSum.isBigO_list_sum_of_uniform uniform).exists_pos
  let guard := Contract.guardCost control condition
  let K : ℝ := C + guard + setup + 1
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hsum.bound] with x hx
  have hbody : (((visits x).map (cost x)).sum : ℝ) ≤
      K * (((visits x).map (majorant x)).sum : ℝ) := by
    have hx' : (((visits x).map (cost x)).sum : ℝ) ≤
        C * (((visits x).map (majorant x)).sum : ℝ) := by
      simpa only [Real.norm_natCast] using hx
    exact hx'.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [(Nat.cast_nonneg guard : (0 : ℝ) ≤ _),
        (Nat.cast_nonneg setup : (0 : ℝ) ≤ _)]) (Nat.cast_nonneg _))
  have hcontrol : ((visits x).length : ℝ) * (guard + 1) + guard + setup ≤
      K * ((visits x).length + 1) := by
    have hsmall : ((visits x).length : ℝ) * (guard + 1) + guard + setup ≤
        ((guard : ℝ) + setup + 1) * ((visits x).length + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg ((visits x).length) : (0 : ℝ) ≤ _)
        (Nat.cast_nonneg setup : (0 : ℝ) ≤ _)]
    exact hsmall.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith)
      (by linarith [(Nat.cast_nonneg ((visits x).length) : (0 : ℝ) ≤ _)]))
  simp only [Real.norm_natCast]
  rw [budget_eq_map_sum]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  change (((visits x).map (cost x)).sum : ℝ) +
      (visits x).length * ((guard : ℝ) + 1) + guard + setup ≤
    K * ((((visits x).map (majorant x)).sum : ℝ) + (visits x).length + 1)
  calc
    _ ≤ K * (((visits x).map (majorant x)).sum : ℝ) +
        K * ((visits x).length + 1) := by linarith
    _ = _ := by ring

end Ram.Source.Traversal

namespace Ram.UniformBigOAt

/-- Export actual complete-machine traversal bounds on every legal input.
The visit list is proof data; the supplied runs still justify all work,
including the chosen fixed setup allowance and the real control flow. -/
theorem of_traversal {Input ι : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {post : ∀ w, Input → State w → Prop} {l : Filter (LegalInput admissible)}
    {visits : LegalInput admissible → List ι}
    {cost majorant : LegalInput admissible → ι → Nat}
    (control : Nat) (condition : Expr) (setup : Nat)
    (runs : ∀ i : LegalInput admissible, ∃ finish,
      TerminatesWithin code
        (Source.Traversal.budget control condition (fun a _ => cost i a) (visits i) + setup)
        (State.initial (encode i.val.1 i.val.2)) finish ∧ post i.val.1 i.val.2 finish)
    (uniform : ∃ C : ℝ, ∀ᶠ i in l, ∀ a ∈ visits i,
      (cost i a : ℝ) ≤ C * (majorant i a : ℝ)) :
    UniformBigOAt code encode admissible post l
      (fun i => ((visits i).map (majorant i)).sum + (visits i).length + 1) :=
  of_terminatesWithin runs
    (Source.Traversal.budget_isBigO_of_uniform control condition setup uniform)

end Ram.UniformBigOAt
