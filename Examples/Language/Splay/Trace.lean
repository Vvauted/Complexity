/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Potential
import Complexity.Data.Tree.Basic

/-!
# Declarative certificates for splay rotations

`SplayTrace` records the shape changes made by bottom-up splaying and their
number of rotations. It is a proposition, not a second executable splay
function. A source-program proof must construct this certificate from its
actual execution; the certificate alone assigns no RAM instruction cost.

The focus is the original subtree rooted at the accessed node. A failed search
may instead focus on its last visited node. Empty grandchildren do not introduce
double-rotation cases: their source calls can perform work, but the tree
transformation is a single zig and that work must be charged separately.
-/

namespace Complexity.Language.Examples.Splay

variable {α : Type*}

/-- A bottom-up splay certificate, indexed by its original focus and rotation count. -/
inductive SplayTrace : Tree α → Tree α → Tree α → Nat → Prop
  | refl (tree : Tree α) : SplayTrace tree tree tree 0
  | zigLeft (x y : α) (a b c : Tree α) :
      SplayTrace (.node x a b) (.node y (.node x a b) c)
        (.node x a (.node y b c)) 1
  | zigRight (x y : α) (a b c : Tree α) :
      SplayTrace (.node x b c) (.node y a (.node x b c))
        (.node x (.node y a b) c) 1
  | zigZigLeft {focus inner : Tree α} {x y z : α} {a b c d : Tree α} {n : Nat}
      (rec : SplayTrace focus inner (.node x a b) n) :
      SplayTrace focus (.node z (.node y inner c) d)
        (.node x a (.node y b (.node z c d))) (n + 2)
  | zigZigRight {focus inner : Tree α} {x y z : α} {a b c d : Tree α} {n : Nat}
      (rec : SplayTrace focus inner (.node x c d) n) :
      SplayTrace focus (.node z a (.node y b inner))
        (.node x (.node y (.node z a b) c) d) (n + 2)
  | zigZagLeft {focus inner : Tree α} {x y z : α} {a b c d : Tree α} {n : Nat}
      (rec : SplayTrace focus inner (.node x b c) n) :
      SplayTrace focus (.node z (.node y a inner) d)
        (.node x (.node y a b) (.node z c d)) (n + 2)
  | zigZagRight {focus inner : Tree α} {x y z : α} {a b c d : Tree α} {n : Nat}
      (rec : SplayTrace focus inner (.node x b c) n) :
      SplayTrace focus (.node z a (.node y inner d))
        (.node x (.node z a b) (.node y c d)) (n + 2)

namespace SplayTrace

variable {focus initial final : Tree α} {rotations : Nat}

/-- Every label, including duplicates, retains its inorder position. -/
theorem inorder_eq (trace : SplayTrace focus initial final rotations) :
    final.inorder = initial.inorder := by
  induction trace with
  | refl => rfl
  | zigLeft => simp [List.append_assoc]
  | zigRight => simp [List.append_assoc]
  | zigZigLeft rec ih | zigZigRight rec ih | zigZagLeft rec ih | zigZagRight rec ih =>
    simp only [Tree.inorder] at ih ⊢
    rw [← ih]
    simp only [List.append_assoc, List.cons_append]

/-- Splaying neither creates nor removes nodes. -/
theorem numNodes_eq (trace : SplayTrace focus initial final rotations) :
    final.numNodes = initial.numNodes :=
  Tree.numNodes_eq_of_inorder_eq trace.inorder_eq

theorem numLeaves_eq (trace : SplayTrace focus initial final rotations) :
    final.numLeaves = initial.numLeaves := by
  simp only [Tree.numLeaves_eq_numNodes_succ, trace.numNodes_eq]

/-- The original focus label is the final root, without choosing a value for nil. -/
theorem root_eq (trace : SplayTrace focus initial final rotations) :
    final.root? = focus.root? := by
  induction trace <;> simp_all only [Tree.root?]

/-- Empty and nonempty trees are preserved. -/
theorem eq_nil_iff (trace : SplayTrace focus initial final rotations) :
    final = .nil ↔ initial = .nil := by
  have h := trace.numNodes_eq
  cases initial <;> cases final <;> simp_all

/-- A nonempty splay result has a nonempty original focus. -/
theorem focus_eq_nil_iff (trace : SplayTrace focus initial final rotations) :
    focus = .nil ↔ final = .nil := by
  have h := trace.root_eq
  cases focus <;> cases final <;> simp_all

/-- The selected original subtree fits inside the original whole tree. -/
theorem focus_numLeaves_le (trace : SplayTrace focus initial final rotations) :
    focus.numLeaves ≤ initial.numLeaves := by
  induction trace <;> (try simp_all only [Tree.numLeaves]) <;> omega

private theorem rank_eq_of_numLeaves_eq {s t : Tree α} (h : s.numLeaves = t.numLeaves) :
    rank s = rank t := congrArg (fun n : Nat => Real.logb 2 (n : ℝ)) h

private theorem left_frame (x : α) (r : Tree α) {s t : Tree α}
    (h : s.numLeaves = t.numLeaves) :
    potential (.node x s r) - potential (.node x t r) = potential s - potential t := by
  have hrank := rank_eq_of_numLeaves_eq (congrArg (· + r.numLeaves) h)
    (s := .node x s r) (t := .node x t r)
  simp only [potential_node]
  linarith

private theorem right_frame (x : α) (l : Tree α) {s t : Tree α}
    (h : s.numLeaves = t.numLeaves) :
    potential (.node x l s) - potential (.node x l t) = potential s - potential t := by
  have hrank := rank_eq_of_numLeaves_eq (congrArg (l.numLeaves + ·) h)
    (s := .node x l s) (t := .node x l t)
  simp only [potential_node]
  linarith

private theorem access_double {focus inner next initial middle final : Tree α} {n : Nat}
    (ih : (n : ℝ) + potential next - potential inner ≤
      3 * (rank inner - rank focus) + 1)
    (step : 2 + potential final - potential middle ≤
      3 * (rank initial - rank inner))
    (frame : potential middle - potential initial = potential next - potential inner) :
    ((n + 2 : Nat) : ℝ) + potential final - potential initial ≤
      3 * (rank initial - rank focus) + 1 := by
  push_cast
  linarith

/-- The access lemma for certified rotations. An execution-cost theorem must
separately bound actual program work by these rotations and its constant overhead. -/
theorem access (trace : SplayTrace focus initial final rotations) :
    (rotations : ℝ) + potential final - potential initial ≤
      3 * (rank initial - rank focus) + 1 := by
  induction trace with
  | refl => simp
  | zigLeft x y a b c => simpa using zig_left x y a b c
  | zigRight x y a b c => simpa using zig_right x y a b c
  | @zigZigLeft focus inner x y z a b c d n rec ih =>
    have hs := rec.numLeaves_eq
    have hp := congrArg (· + c.numLeaves) hs
    have ht := congrArg (· + d.numLeaves) hp
    have hr := rank_eq_of_numLeaves_eq hs
    have htop := rank_eq_of_numLeaves_eq ht
      (s := .node z (.node y (.node x a b) c) d) (t := .node z (.node y inner c) d)
    apply access_double (middle := .node z (.node y (.node x a b) c) d) ih
    · simpa only [htop, hr] using zig_zig_left x y z a b c d
    · have h1 := left_frame y c hs
      have h2 := left_frame z d hp
        (s := .node y (.node x a b) c) (t := .node y inner c)
      linarith
  | @zigZigRight focus inner x y z a b c d n rec ih =>
    have hs := rec.numLeaves_eq
    have hp := congrArg (b.numLeaves + ·) hs
    have ht := congrArg (a.numLeaves + ·) hp
    have hr := rank_eq_of_numLeaves_eq hs
    have htop := rank_eq_of_numLeaves_eq ht
      (s := .node z a (.node y b (.node x c d))) (t := .node z a (.node y b inner))
    apply access_double (middle := .node z a (.node y b (.node x c d))) ih
    · simpa only [htop, hr] using zig_zig_right x y z a b c d
    · have h1 := right_frame y b hs
      have h2 := right_frame z a hp
        (s := .node y b (.node x c d)) (t := .node y b inner)
      linarith
  | @zigZagLeft focus inner x y z a b c d n rec ih =>
    have hs := rec.numLeaves_eq
    have hp := congrArg (a.numLeaves + ·) hs
    have ht := congrArg (· + d.numLeaves) hp
    have hr := rank_eq_of_numLeaves_eq hs
    have htop := rank_eq_of_numLeaves_eq ht
      (s := .node z (.node y a (.node x b c)) d) (t := .node z (.node y a inner) d)
    apply access_double (middle := .node z (.node y a (.node x b c)) d) ih
    · have hstep := zig_zag_left x y z a b c d
      rw [htop, hr] at hstep
      have hgain := (rank_right_le y a inner).trans (rank_left_le z (.node y a inner) d)
      linarith
    · have h1 := right_frame y a hs
      have h2 := left_frame z d hp
        (s := .node y a (.node x b c)) (t := .node y a inner)
      linarith
  | @zigZagRight focus inner x y z a b c d n rec ih =>
    have hs := rec.numLeaves_eq
    have hp := congrArg (· + d.numLeaves) hs
    have ht := congrArg (a.numLeaves + ·) hp
    have hr := rank_eq_of_numLeaves_eq hs
    have htop := rank_eq_of_numLeaves_eq ht
      (s := .node z a (.node y (.node x b c) d)) (t := .node z a (.node y inner d))
    apply access_double (middle := .node z a (.node y (.node x b c) d)) ih
    · have hstep := zig_zag_right x y z a b c d
      rw [htop, hr] at hstep
      have hgain := (rank_left_le y inner d).trans (rank_right_le z a (.node y inner d))
      linarith
    · have h1 := left_frame y d hs
      have h2 := right_frame z a hp
        (s := .node y (.node x b c) d) (t := .node y inner d)
      linarith

/-- A root-size-only amortized bound, retaining both initial and final credit. -/
theorem rotations_add_potential_le (trace : SplayTrace focus initial final rotations) :
    (rotations : ℝ) + potential final ≤ potential initial + 3 * rank initial + 1 := by
  have h := trace.access
  have hfocus := rank_nonneg focus
  linarith

end SplayTrace

end Complexity.Language.Examples.Splay
