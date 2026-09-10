/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Log
import Mathlib.Data.Tree.Basic

/-!
# Splay-tree potential

Ranks are binary logarithms of leaf counts, equivalently internal-node counts
plus one. The potential sums these ranks over internal nodes. Both quantities
are proof-only observations of mathlib trees: the implementation does not
maintain subtree sizes or compute logarithms.

The local inequalities below count one or two rotations, not RAM instructions.
An implementation's measured execution must separately justify the cost of those
rotations and all surrounding work before using a scaled potential for runtime.
-/

namespace Complexity.Language.Examples.Splay

variable {α : Type*}

/-- A proof-only rank with a well-defined zero value at the empty tree. -/
noncomputable def rank (t : Tree α) : ℝ := Real.logb 2 t.numLeaves

/-- Sum the ranks of the internal nodes. -/
noncomputable def potential : Tree α → ℝ
  | .nil => 0
  | .node x l r => rank (.node x l r) + potential l + potential r

@[simp] theorem rank_nil : rank (.nil : Tree α) = 0 := by
  simp [rank]

/-- Leaf-count rank in terms of the ordinary input-size measure. -/
theorem rank_eq_log_numNodes (t : Tree α) :
    rank t = Real.logb 2 ((t.numNodes + 1 : ℕ) : ℝ) := by
  rw [rank, Tree.numLeaves_eq_numNodes_succ]

theorem rank_nonneg (t : Tree α) : 0 ≤ rank t := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast (show 1 ≤ t.numLeaves from t.numLeaves_pos)

theorem rank_mono {s t : Tree α} (h : s.numLeaves ≤ t.numLeaves) :
    rank s ≤ rank t := by
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast s.numLeaves_pos
  · exact_mod_cast h

theorem rank_left_le (x : α) (l r : Tree α) : rank l ≤ rank (.node x l r) := by
  apply rank_mono
  simp only [Tree.numLeaves]
  omega

theorem rank_right_le (x : α) (l r : Tree α) : rank r ≤ rank (.node x l r) := by
  apply rank_mono
  simp only [Tree.numLeaves]
  omega

/-- The logarithmic slack available for two disjoint subtrees. -/
theorem rank_add_rank_add_two_le (s t u : Tree α)
    (h : s.numLeaves + t.numLeaves ≤ u.numLeaves) :
    rank s + rank t + 2 ≤ 2 * rank u := by
  apply Real.logb_add_logb_add_two_le_of_add_le
  · exact_mod_cast s.numLeaves_pos
  · exact_mod_cast t.numLeaves_pos
  · exact_mod_cast h

@[simp] theorem potential_nil : potential (.nil : Tree α) = 0 := rfl

@[simp] theorem potential_node (x : α) (l r : Tree α) :
    potential (.node x l r) = rank (.node x l r) + potential l + potential r := rfl

theorem potential_nonneg (t : Tree α) : 0 ≤ potential t := by
  induction t with
  | nil => simp
  | node x l r hl hr =>
    exact add_nonneg (add_nonneg (rank_nonneg _) hl) hr

/-- Initial credit is bounded by the number of nodes times the root rank. -/
theorem potential_le_numNodes_mul_rank (t : Tree α) :
    potential t ≤ (t.numNodes : ℝ) * rank t := by
  induction t with
  | nil => simp
  | node x l r hl hr =>
    have hleft := mul_le_mul_of_nonneg_left (rank_left_le x l r)
      (Nat.cast_nonneg l.numNodes : (0 : ℝ) ≤ l.numNodes)
    have hright := mul_le_mul_of_nonneg_left (rank_right_le x l r)
      (Nat.cast_nonneg r.numNodes : (0 : ℝ) ≤ r.numNodes)
    simp only [potential_node, Tree.numNodes, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A uniform bound on the initial potential of any tree of the given size. -/
theorem potential_le_numNodes_mul_log (t : Tree α) :
    potential t ≤ (t.numNodes : ℝ) * Real.logb 2 ((t.numNodes + 1 : ℕ) : ℝ) := by
  simpa only [rank_eq_log_numNodes] using potential_le_numNodes_mul_rank t

/-- A final left-child single rotation has one additive unit of amortized cost. -/
theorem zig_left (x y : α) (a b c : Tree α) :
    1 + potential (.node x a (.node y b c)) - potential (.node y (.node x a b) c) ≤
      3 * (rank (.node y (.node x a b) c) - rank (.node x a b)) + 1 := by
  have hroot : rank (.node x a (.node y b c)) = rank (.node y (.node x a b) c) := by
    simp [rank, Nat.add_assoc]
  have hnew := rank_right_le x a (.node y b c)
  have hold := rank_left_le y (.node x a b) c
  simp only [potential_node]
  linarith

/-- A final right-child single rotation has one additive unit of amortized cost. -/
theorem zig_right (x y : α) (a b c : Tree α) :
    1 + potential (.node x (.node y a b) c) - potential (.node y a (.node x b c)) ≤
      3 * (rank (.node y a (.node x b c)) - rank (.node x b c)) + 1 := by
  have hroot : rank (.node x (.node y a b) c) = rank (.node y a (.node x b c)) := by
    simp [rank, Nat.add_assoc]
  have hnew := rank_left_le x (.node y a b) c
  have hold := rank_right_le y a (.node x b c)
  simp only [potential_node]
  linarith

/-- Two left-child rotations are paid for by three times the accessed rank gain. -/
theorem zig_zig_left (x y z : α) (a b c d : Tree α) :
    2 + potential (.node x a (.node y b (.node z c d))) -
        potential (.node z (.node y (.node x a b) c) d) ≤
      3 * (rank (.node z (.node y (.node x a b) c) d) - rank (.node x a b)) := by
  have hroot : rank (.node x a (.node y b (.node z c d))) =
      rank (.node z (.node y (.node x a b) c) d) := by
    simp [rank, Nat.add_assoc]
  have hpair := rank_add_rank_add_two_le (.node x a b) (.node z c d)
    (.node z (.node y (.node x a b) c) d) (by simp [Nat.add_assoc])
  have hold := rank_left_le y (.node x a b) c
  have hnew := rank_right_le x a (.node y b (.node z c d))
  simp only [potential_node]
  linarith

/-- Two right-child rotations are paid for by three times the accessed rank gain. -/
theorem zig_zig_right (x y z : α) (a b c d : Tree α) :
    2 + potential (.node x (.node y (.node z a b) c) d) -
        potential (.node z a (.node y b (.node x c d))) ≤
      3 * (rank (.node z a (.node y b (.node x c d))) - rank (.node x c d)) := by
  have hroot : rank (.node x (.node y (.node z a b) c) d) =
      rank (.node z a (.node y b (.node x c d))) := by
    simp [rank, Nat.add_assoc]
  have hpair := rank_add_rank_add_two_le (.node z a b) (.node x c d)
    (.node z a (.node y b (.node x c d))) (by simp [Nat.add_assoc])
  have hold := rank_right_le y b (.node x c d)
  have hnew := rank_left_le x (.node y (.node z a b) c) d
  simp only [potential_node]
  linarith

/-- A left-right double rotation satisfies the stronger two-rank-gain bound. -/
theorem zig_zag_left (x y z : α) (a b c d : Tree α) :
    2 + potential (.node x (.node y a b) (.node z c d)) -
        potential (.node z (.node y a (.node x b c)) d) ≤
      2 * (rank (.node z (.node y a (.node x b c)) d) - rank (.node x b c)) := by
  have hroot : rank (.node x (.node y a b) (.node z c d)) =
      rank (.node z (.node y a (.node x b c)) d) := by
    simp [rank, Nat.add_assoc]
  have hpair := rank_add_rank_add_two_le (.node y a b) (.node z c d)
    (.node z (.node y a (.node x b c)) d) (by simp [Nat.add_assoc])
  have hold := rank_right_le y a (.node x b c)
  simp only [potential_node]
  linarith

/-- A right-left double rotation satisfies the stronger two-rank-gain bound. -/
theorem zig_zag_right (x y z : α) (a b c d : Tree α) :
    2 + potential (.node x (.node z a b) (.node y c d)) -
        potential (.node z a (.node y (.node x b c) d)) ≤
      2 * (rank (.node z a (.node y (.node x b c) d)) - rank (.node x b c)) := by
  have hroot : rank (.node x (.node z a b) (.node y c d)) =
      rank (.node z a (.node y (.node x b c) d)) := by
    simp [rank, Nat.add_assoc]
  have hpair := rank_add_rank_add_two_le (.node z a b) (.node y c d)
    (.node z a (.node y (.node x b c) d)) (by simp [Nat.add_assoc])
  have hold := rank_left_le y (.node x b c) d
  simp only [potential_node]
  linarith

end Complexity.Language.Examples.Splay
