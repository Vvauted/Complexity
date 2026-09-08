/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Asymptotics.Polynomial
import Complexity.Computability.Ram.Problem.Basic
import Complexity.Computability.Ram.Verification.Loop.Sum
import Complexity.Tactic.Ram.Basic
import Mathlib.Tactic.Linarith

/-!
# A nested countdown loop with a proved quadratic machine budget

The fixed program reads `n`, executes inner loops of lengths `n, n-1, ..., 1`,
and outputs their total. Mathematical finite sums occur only in specifications
and proofs. The executed accumulator is incremented by actual RAM operations.
The inner loop uses the linear rule; the outer loop uses the finite-sum rule
because its body budget depends on the current counter.
-/

namespace Ram.Examples.TriangularLoop

open Source
open scoped BigOperators

def tri (n : Nat) : Nat := ∑ i ∈ Finset.range n, (i + 1)

@[simp] theorem tri_zero : tri 0 = 0 := by simp [tri]

theorem tri_succ (n : Nat) : tri (n + 1) = tri n + n + 1 := by
  simp [tri, Finset.sum_range_succ, Nat.add_assoc]

theorem tri_pred {n : Nat} (hn : 0 < n) : tri n = tri (n - 1) + n := by
  have h := tri_succ (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  omega

theorem tri_le_square (n : Nat) : tri n ≤ n * n := by
  calc
    tri n ≤ ∑ _i ∈ Finset.range n, n := by
      apply Finset.sum_le_sum
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    _ = n * n := by simp

def innerCondition : Expr := .var 1
def outerCondition : Expr := .var 0
def incAcc : Expr := .bin .add (.var 2) (.const 1)
def decInner : Expr := .bin .sub (.var 1) (.const 1)
def decOuter : Expr := .bin .sub (.var 0) (.const 1)

def innerBody : Stmt := .seq (.assign 2 incAcc) (.assign 1 decInner)
def innerLoop : Stmt := .while innerCondition innerBody
def outerBody : Stmt := .seq (.assign 1 (.var 0)) (.seq innerLoop (.assign 0 decOuter))
def outerLoop : Stmt := .while outerCondition outerBody
def main : Stmt := .seq (.read 0)
  (.seq (.assign 2 (.const 0)) (.seq outerLoop (.write (.var 2))))

private theorem word_pos {x : Word w} (hx : x ≠ 0) : 0 < x.toNat := by
  have hn : x.toNat ≠ 0 := fun h => hx ((Word.toNat_eq_zero_iff _).mp h)
  omega

private theorem word_dec (hw : 0 < w) (x : Word w) (hx : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hp := word_pos hx
  change (BinOp.eval .sub x 1).toNat = x.toNat - 1
  rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hone]; omega), hone]

def innerNext (s : Source.State w) : Source.State w :=
  (s.setReg 2 (s.regs 2 + 1)).setReg 1 (s.regs 1 - 1)

@[simp] theorem innerNext_acc (s : Source.State w) :
    (innerNext s).regs 2 = s.regs 2 + 1 := by simp [innerNext, Source.State.setReg]
@[simp] theorem innerNext_count (s : Source.State w) :
    (innerNext s).regs 1 = s.regs 1 - 1 := by simp [innerNext, Source.State.setReg]
@[simp] theorem innerNext_outer (s : Source.State w) :
    (innerNext s).regs 0 = s.regs 0 := by simp [innerNext, Source.State.setReg]

def InnerInv (entry s : Source.State w) : Prop :=
  (s.regs 2).toNat + (s.regs 1).toNat =
    (entry.regs 2).toNat + (entry.regs 1).toNat ∧
  s.regs 0 = entry.regs 0 ∧ s.input = entry.input ∧ s.outputRev = entry.outputRev

def InnerPost (entry s : Source.State w) : Prop :=
  (s.regs 2).toNat = (entry.regs 2).toNat + (entry.regs 1).toNat ∧
  s.regs 0 = entry.regs 0 ∧ s.input = entry.input ∧ s.outputRev = entry.outputRev

theorem inner_body_contract (s : Source.State w) :
    Contract 3 [] 0 0 innerBody (fun t => t = s)
      (fun t => t = innerNext s) (fun _ => 8) := by
  ram_vc t ht [innerBody, incAcc, decInner, innerNext, ht]

theorem inner_next_preserves (hw : 0 < w) (entry s : Source.State w)
    (hfit : (entry.regs 2).toNat + (entry.regs 1).toNat < 2 ^ w)
    (hs : InnerInv entry s) (hz : s.eval innerCondition ≠ 0) :
    InnerInv entry (innerNext s) ∧
      ((innerNext s).regs 1).toNat < (s.regs 1).toNat := by
  have hp := word_pos hz
  change 0 < (s.regs 1).toNat at hp
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have haccfit : (s.regs 2).toNat + (1 : Word w).toNat < 2 ^ w := by
    have hsum := hs.1
    rw [hone]
    omega
  have ha : ((innerNext s).regs 2).toNat = (s.regs 2).toNat + 1 := by
    rw [innerNext_acc, BitVec.toNat_add_of_lt haccfit, hone]
  have hj : ((innerNext s).regs 1).toNat = (s.regs 1).toNat - 1 := by
    rw [innerNext_count, word_dec hw (s.regs 1) hz]
  refine ⟨⟨?_, ?_, hs.2.2.1, hs.2.2.2⟩, ?_⟩
  · rw [ha, hj]
    have hsum := hs.1
    omega
  · simpa using hs.2.1
  · rw [hj]
    omega

/-- The inner loop adds its entry count to the accumulator without wrapping,
and preserves the outer counter and I/O. -/
theorem inner_contract (hw : 0 < w) (entry : Source.State w)
    (hfit : (entry.regs 2).toNat + (entry.regs 1).toNat < 2 ^ w) :
    Contract 3 [] 0 0 innerLoop (fun s => s = entry) (InnerPost entry)
      (fun _ => 11 * (entry.regs 1).toNat + 2) := by
  have hl : Contract 3 [] 0 0 innerLoop (InnerInv entry)
      (fun t => InnerInv entry t ∧ t.eval innerCondition = 0)
      (fun s => (s.regs 1).toNat * 11 + 2) := by
    apply Contract.while_linear (InnerInv entry) (fun s => (s.regs 1).toNat) 8
    · intro s hs
      trivial
    · intro s hs hz
      apply (inner_body_contract s).mono_post
      intro t ht
      subst t
      exact inner_next_preserves hw entry s hfit hs hz
  apply hl.consequence
  · intro s hs
    subst s
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro t ht
    have hz : (t.regs 1).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr ht.2
    exact ⟨by have hsum := ht.1.1; omega, ht.1.2⟩
  · intro s hs
    subst s
    simp [Nat.mul_comm]

def OuterInv (n : Nat) (s : Source.State w) : Prop :=
  (s.regs 2).toNat + tri (s.regs 0).toNat = tri n ∧ s.input = [] ∧ s.outputRev = []

/-- A complete outer iteration has a nonconstant body budget: the current
outer counter is copied to the inner counter and determines the inner work. -/
theorem outer_body_contract (n : Nat) (hw : 0 < w) (htri : tri n < 2 ^ w)
    (s : Source.State w) (hs : OuterInv n s) (hz : s.eval outerCondition ≠ 0) :
    Contract 3 [] 0 0 outerBody (fun t => t = s)
      (fun t => OuterInv n t ∧ (t.regs 0).toNat < (s.regs 0).toNat)
      (fun _ => 11 * (s.regs 0).toNat + 8) := by
  let start := s.setReg 1 (s.regs 0)
  have hp : 0 < (s.regs 0).toNat := word_pos hz
  have hsplit := tri_pred hp
  have htotal : (start.regs 2).toNat + (start.regs 1).toNat < 2 ^ w := by
    change (s.regs 2).toNat + (s.regs 0).toNat < 2 ^ w
    have hsum := hs.1
    omega
  have hi : Contract 3 [] 0 0 (.assign 1 (.var 0)) (fun t => t = s)
      (fun t => t = start) (fun _ => 2) := by
    apply Contract.assign
    · intro t ht
      trivial
    · intro t ht
      subst t
      rfl
  have hinner := inner_contract hw start htotal
  have hd : Contract 3 [] 0 0 (.assign 0 decOuter) (InnerPost start)
      (fun t => OuterInv n t ∧ (t.regs 0).toNat < (s.regs 0).toNat) (fun _ => 4) := by
    apply Contract.assign
    · intro t ht
      exact ⟨trivial, trivial⟩
    · intro t ht
      have hk : t.regs 0 = s.regs 0 := ht.2.1
      have ha : (t.regs 2).toNat = (s.regs 2).toNat + (s.regs 0).toNat := ht.1
      change OuterInv n (t.setReg 0 (t.regs 0 - 1)) ∧
        ((t.setReg 0 (t.regs 0 - 1)).regs 0).toNat < (s.regs 0).toNat
      refine ⟨⟨?_, ht.2.2.1.trans hs.2.1, ht.2.2.2.trans hs.2.2⟩, ?_⟩
      · change (t.regs 2).toNat + tri (t.regs 0 - 1).toNat = tri n
        rw [ha, hk, word_dec hw (s.regs 0) hz]
        have hsum := hs.1
        omega
      · change (t.regs 0 - 1).toNat < (s.regs 0).toNat
        rw [hk, word_dec hw (s.regs 0) hz]
        omega
  have hb := hi.seq_const (hinner.seq_const hd)
  apply hb.mono_budget
  intro t ht
  change 2 + (11 * (s.regs 0).toNat + 2 + 4) ≤ 11 * (s.regs 0).toNat + 8
  omega

theorem outer_budget (k : Nat) :
    Contract.sumBudget 3 outerCondition (fun j => 11 * j + 8) k =
      11 * tri k + 11 * k + 2 := by
  induction k with
  | zero => simp [Contract.sumBudget_zero, Contract.guardCost, outerCondition, Expr.compile]
  | succ k ih =>
      rw [Contract.sumBudget_succ, ih, tri_succ]
      change (11 * tri k + 11 * k + 2) + 2 + (11 * (k + 1) + 8) + 1 =
        11 * (tri k + k + 1) + 11 * (k + 1) + 2
      omega

theorem outer_contract (n : Nat) (hw : 0 < w) (htri : tri n < 2 ^ w) :
    Contract (w := w) 3 [] 0 0 outerLoop (OuterInv n)
      (fun t => OuterInv n t ∧ t.eval outerCondition = 0)
      (fun s => 11 * tri (s.regs 0).toNat + 11 * (s.regs 0).toNat + 2) := by
  have hl : Contract (w := w) 3 [] 0 0 outerLoop (OuterInv n)
      (fun t => OuterInv n t ∧ t.eval outerCondition = 0)
      (fun s => Contract.sumBudget 3 outerCondition (fun j => 11 * j + 8)
        (s.regs 0).toNat) := by
    apply Contract.while_sum (OuterInv n) (fun s => (s.regs 0).toNat) (fun j => 11 * j + 8)
    · intro s hs
      trivial
    · intro s hs hz
      exact outer_body_contract n hw htri s hs hz
  exact hl.mono_budget (fun s _ => by rw [outer_budget])

def InputReady (n : Nat) (s : Source.State w) : Prop :=
  s.input = [BitVec.ofNat w n] ∧ s.outputRev = []
def CountReady (n : Nat) (s : Source.State w) : Prop :=
  (s.regs 0).toNat = n ∧ s.input = [] ∧ s.outputRev = []
def StartInv (n : Nat) (s : Source.State w) : Prop :=
  OuterInv n s ∧ (s.regs 0).toNat = n
def Post (n : Nat) (s : Source.State w) : Prop :=
  s.output = [BitVec.ofNat w (tri n)] ∧ s.input = []

theorem main_contract (n : Nat) (hw : 0 < w)
    (hn : n < 2 ^ w) (htri : tri n < 2 ^ w) :
    Contract (w := w) 3 [] 0 0 main (InputReady n) (Post n)
      (fun _ => 11 * tri n + 11 * n + 7) := by
  have hr : Contract (w := w) 3 [] 0 0 (.read 0) (InputReady n) (CountReady n)
      (fun _ => 1) := by
    apply Contract.read
    intro s hs
    exact ⟨BitVec.ofNat w n, [], hs.1,
      ⟨by simpa using Word.ofNat_toNat_of_lt hn, rfl, hs.2⟩⟩
  have hi : Contract (w := w) 3 [] 0 0 (.assign 2 (.const 0)) (CountReady n)
      (StartInv n) (fun _ => 2) := by
    apply Contract.assign
    · intro s hs
      trivial
    · intro s hs
      refine ⟨⟨?_, hs.2.1, hs.2.2⟩, ?_⟩
      · simp [Source.State.setReg, Source.State.eval, Expr.eval, hs.1]
      · simpa [Source.State.setReg] using hs.1
  have hl : Contract (w := w) 3 [] 0 0 outerLoop (StartInv n)
      (fun t => OuterInv n t ∧ t.eval outerCondition = 0)
      (fun _ => 11 * tri n + 11 * n + 2) := by
    apply (outer_contract n hw htri).consequence (fun s hs => hs.1) (fun _ ht => ht)
    intro s hs
    rw [hs.2]
  have ho : Contract (w := w) 3 [] 0 0 (.write (.var 2))
      (fun t => OuterInv n t ∧ t.eval outerCondition = 0) (Post n) (fun _ => 2) := by
    apply Contract.write
    · intro s hs
      trivial
    · intro s hs
      have hk : (s.regs 0).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hs.2
      have ha : (s.regs 2).toNat = tri n := by
        have hsum := hs.1.1
        simpa [hk] using hsum
      have haWord : s.regs 2 = BitVec.ofNat w (tri n) := by
        rw [← ha, Word.ofNat_toNat_self]
      exact ⟨by simp [Source.State.output, hs.1.2.2, haWord], hs.1.2.1⟩
  have hall := hr.seq_const (hi.seq_const (hl.seq_const ho))
  apply hall.mono_budget
  intro s hs
  omega

def machine : Code := LocalCompiler.rawLink 3 [] main

theorem main_valid : LocalCompiler.Valid 3 [] main := by
  simp [LocalCompiler.Valid, Compiler.Valid, main, outerLoop, outerBody, innerLoop,
    innerBody, outerCondition, innerCondition, incAcc, decInner, decOuter,
    Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]

theorem checked_machine : LocalCompiler.compileChecked 3 [] main = some machine :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨main_valid, rfl⟩

theorem machine_code_size : machine.length = 27 := rfl

/-- The complete checked program outputs the mathematical triangular number.
The explicit affine-in-the-sum bound includes its input, output, prologue, and halt. -/
theorem machine_correct (n : Nat) (hw : 0 < w)
    (hn : n < 2 ^ w) (htri : tri n < 2 ^ w) (hcodefit : machine.length < 2 ^ w) :
    ∃ finish : Ram.State w,
      Ram.TerminatesWithin machine (11 * tri n + 11 * n + 9)
        (Ram.State.initial [0, BitVec.ofNat w n]) finish ∧
      finish.output = [BitVec.ofNat w (tri n)] ∧ finish.input = [] := by
  have hstack : 0 + 0 * ABI.frameSize 3 < 2 ^ w := by
    omega
  obtain ⟨sf, tf, hp, ht, ho, hi⟩ := (main_contract n hw hn htri).compile
    (input := [BitVec.ofNat w n]) checked_machine hcodefit hstack ⟨rfl, rfl⟩
  exact ⟨tf, by simpa [Nat.add_assoc] using ht, ho.trans hp.1, hi.trans hp.2⟩

/-- A polynomial upper bound follows from mathlib's finite-sum comparison;
no closed form with natural-number division is needed for the algorithm proof. -/
theorem machine_quadratic (n : Nat) (hw : 0 < w)
    (hn : n < 2 ^ w) (htri : tri n < 2 ^ w) (hcodefit : machine.length < 2 ^ w) :
    ∃ finish : Ram.State w,
      Ram.TerminatesWithin machine (11 * (n * n) + 11 * n + 9)
        (Ram.State.initial [0, BitVec.ofNat w n]) finish ∧
      finish.output = [BitVec.ofNat w (tri n)] ∧ finish.input = [] := by
  obtain ⟨finish, ht, hp⟩ := machine_correct n hw hn htri hcodefit
  have htriBound := Nat.mul_le_mul_left 11 (tri_le_square n)
  exact ⟨finish, ht.mono (by omega), hp⟩

/-- The published task takes the numeric value `n` as its size, not its binary
encoding length. Its fixed minimum word width and representable mathematical
input/output domain do not refer to any submission or instruction-list size.
The input contains only the zero heap header and `n`, never a precomputed sum. -/
def problem : AsymptoticProblem Nat where
  encode w n := [0, BitVec.ofNat w n]
  admissible w n := 5 ≤ w ∧ n < 2 ^ w ∧ tri n < 2 ^ w
  size n := n
  post _ n finish := finish.output.map BitVec.toNat = [tri n] ∧ finish.input = []
  unbounded := by
    intro n
    refine ⟨5 + n + tri n, n, ?_, Nat.le_refl n⟩
    have hpow : 5 + n + tri n < 2 ^ (5 + n + tri n) := Nat.lt_two_pow_self
    exact ⟨by omega, by omega, by omega⟩

/-- The concrete code's address fit follows from the independently published
minimum width; it is a proof obligation, not part of the problem domain. -/
private theorem machine_fits {w : Nat} (hw : 5 ≤ w) : machine.length < 2 ^ w := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  norm_num at hpow
  rw [machine_code_size]
  omega

/-- One fixed executable solves every legal input under a concrete quadratic
transition budget, retaining its mathematical result and termination. -/
def certificate : Certificate problem.toProblem (fun n => 11 * (n * n) + 11 * n + 9) where
  code := machine
  verified := by
    intro w n ha
    obtain ⟨finish, hrun, hout, hin⟩ :=
      machine_quadratic n (by have h := ha.1; omega) ha.2.1 ha.2.2 (machine_fits ha.1)
    refine ⟨finish, hrun, ?_, hin⟩
    change finish.output.map BitVec.toNat = [tri n]
    simp only [hout, List.map_cons, List.map_nil, Word.ofNat_toNat_of_lt ha.2.2]

/-- Analyze the proved natural machine bound with the main library's mathlib
bridge. The coefficient is uniform over every input and legal word width. -/
theorem budget_isBigO : Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => ((11 * (n * n) + 11 * n + 9 : Nat) : ℝ))
    (fun n : Nat => (((n + 1) ^ 2 : Nat) : ℝ)) := by
  apply Asymptotics.isBigO_shifted_pow_iff.mpr
  refine ⟨11, ?_⟩
  intro n
  nlinarith

/-- A genuine mathlib-backed `O((n+1)^2)` certificate for this same machine
on the unbounded published domain. This is a numeric-size word-RAM claim,
not a bit-complexity or bit-linear claim. -/
def asymptoticCertificate : AsymptoticCertificate problem (fun n => (n + 1) ^ 2) :=
  .ofIsBigO certificate budget_isBigO

@[simp] theorem asymptoticCertificate_code : asymptoticCertificate.code = machine := rfl

end Ram.Examples.TriangularLoop
