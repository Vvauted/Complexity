/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Verification.Loop.Logarithmic
import Complexity.Tactic.Ram.Basic
import Mathlib.Data.List.Pairwise

/-!
# Lower-bound search in a sorted RAM array

This fixed program searches a preloaded array using unsigned comparisons.
Registers 0 and 1 contain the base and key, register 3 initially contains the
length, register 2 receives the insertion index, and register 4 is temporary.
The midpoint is `lo + (hi - lo) / 2`, so no sum of the two endpoints can wrap.

Sortedness is standard `List.Pairwise` on decoded words. The specification
includes duplicates, empty arrays, and keys outside the element range. The
entire source memory and I/O are preserved. No input-loading cost is claimed:
the interface is a preloaded heap block, not a free host-side array loader.
-/

namespace Ram.Source.Array

/-- The insertion index separating elements below the key from all others. -/
structure LowerBoundSpec (xs : List (Word w)) (key : Word w) (p : Nat) : Prop where
  index_le : p ≤ xs.length
  before : ∀ (i : Nat) (hi : i < xs.length), i < p → xs[i].toNat < key.toNat
  after : ∀ (i : Nat) (hi : i < xs.length), p ≤ i → key.toNat ≤ xs[i].toNat

/-- The verified insertion position is standard `List.findIdx`, including
the length sentinel when no array element is at least the key. -/
theorem LowerBoundSpec.eq_findIdx {xs : List (Word w)} {key : Word w} {p : Nat}
    (h : LowerBoundSpec xs key p) :
    p = xs.findIdx (fun x => decide (key.toNat ≤ x.toNat)) := by
  symm
  by_cases hp : p < xs.length
  · apply (List.findIdx_eq hp).mpr
    refine ⟨by simpa using h.after p hp (Nat.le_refl p), ?_⟩
    intro i hip
    simpa using Nat.not_le.mpr (h.before i (Nat.lt_trans hip hp) hip)
  · have heq : p = xs.length := Nat.le_antisymm h.index_le (Nat.le_of_not_gt hp)
    rw [heq]
    apply List.findIdx_eq_length_of_false
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hip : i < p := by simpa only [heq] using hi
    simpa using Nat.not_le.mpr (h.before i hi hip)

/-- The separating-index specification determines one unique result. -/
theorem LowerBoundSpec.unique {xs : List (Word w)} {key : Word w} {p q : Nat}
    (hp : LowerBoundSpec xs key p) (hq : LowerBoundSpec xs key q) : p = q :=
  hp.eq_findIdx.trans hq.eq_findIdx.symm

def lowerBoundCondition : Expr := .bin .ult (.var 2) (.var 3)

def lowerBoundMidpoint : Expr :=
  .bin .add (.var 2) (.bin .udiv (.bin .sub (.var 3) (.var 2)) (.const 2))

def lowerBoundComparison : Expr :=
  .bin .ult (.load (address 0 4)) (.var 1)

def lowerBoundBody : Stmt :=
  .seq (.assign 4 lowerBoundMidpoint)
    (.ite lowerBoundComparison
      (.assign 2 (.bin .add (.var 4) (.const 1)))
      (.assign 3 (.var 4)))

def lowerBoundLoop : Stmt := .while lowerBoundCondition lowerBoundBody

/-- Initialize the left endpoint and run the fixed binary-search loop. -/
def lowerBound : Stmt := .seq (.assign 2 (.const 0)) lowerBoundLoop

theorem lowerBound_wellFormed {locals : Nat} (h : 5 ≤ locals) :
    lowerBound.WellFormed locals := by
  have h0 : 0 < locals := by omega
  have h1 : 1 < locals := by omega
  have h2 : 2 < locals := by omega
  have h3 : 3 < locals := by omega
  have h4 : 4 < locals := by omega
  simp [lowerBound, lowerBoundLoop, lowerBoundBody, lowerBoundCondition,
    lowerBoundMidpoint, lowerBoundComparison, address, Stmt.WellFormed,
    Expr.Bounded, h0, h1, h2, h3, h4]

theorem lowerBound_body_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable lowerBoundBody = 22 := rfl

theorem lowerBound_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable lowerBound = 29 := rfl

private def midpoint (s : State w) : Nat :=
  (s.regs 2).toNat + ((s.regs 3).toNat - (s.regs 2).toNat) / 2

private def midpointWord (s : State w) : Word w :=
  s.regs 2 + (s.regs 3 - s.regs 2) / 2

/-- Exact state effect of the body: one midpoint assignment and one endpoint update. -/
def lowerBoundStep (s : State w) : State w :=
  if (s.mem (s.regs 0 + midpointWord s)).toNat < (s.regs 1).toNat then
    (s.setReg 4 (midpointWord s)).setReg 2 (midpointWord s + 1)
  else
    (s.setReg 4 (midpointWord s)).setReg 3 (midpointWord s)

private theorem midpoint_toNat (hw : 2 ≤ w) (s : State w)
    (horder : (s.regs 2).toNat ≤ (s.regs 3).toNat) :
    (midpointWord s).toNat = midpoint s := by
  have htwoFit : 2 < 2 ^ w := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have htwo : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt htwoFit
  have hdiv : ((s.regs 3 - s.regs 2) / 2).toNat =
      ((s.regs 3).toNat - (s.regs 2).toNat) / 2 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_sub_of_le horder, htwo]
  have hfit : (s.regs 2).toNat + ((s.regs 3 - s.regs 2) / 2).toNat < 2 ^ w := by
    rw [hdiv]
    have hhalf := Nat.div_le_self ((s.regs 3).toNat - (s.regs 2).toNat) 2
    have hhi := Word.toNat_lt (s.regs 3)
    omega
  exact (BitVec.toNat_add_of_lt hfit).trans (congrArg ((s.regs 2).toNat + ·) hdiv)

private theorem midpoint_interval (s : State w)
    (horder : (s.regs 2).toNat < (s.regs 3).toNat) :
    (s.regs 2).toNat ≤ midpoint s ∧ midpoint s < (s.regs 3).toNat := by
  unfold midpoint
  have hhalf := Nat.div_lt_self
    (show 0 < (s.regs 3).toNat - (s.regs 2).toNat by omega) (by decide : 1 < 2)
  omega

/-- The longest branch uses twenty generated instructions; the shorter one
uses seventeen. The full static block also contains the unselected branch. -/
theorem lowerBound_body_contract {control heapLimit depth : Nat} {program : Program}
    (hw : 0 < w) (s : State w)
    (haddress : (s.regs 0 + (s.regs 2 + (s.regs 3 - s.regs 2) / 2)).toNat < heapLimit) :
    Contract control program heapLimit depth lowerBoundBody (fun t => t = s)
      (fun t => t = lowerBoundStep s) (fun _ => 20) := by
  by_cases hcmp : (s.mem (s.regs 0 + (s.regs 2 + (s.regs 3 - s.regs 2) / 2))).toNat <
      (s.regs 1).toNat
  · ram_vc t ht [lowerBoundBody, lowerBoundMidpoint, lowerBoundComparison,
      address, lowerBoundStep, midpointWord, ht, haddress, hcmp, Word.one_ne_zero hw]
    constructor
    · simpa using haddress
    · intro hzero
      exact False.elim ((Nat.ne_of_gt hw) (hzero hcmp))
  · ram_vc t ht [lowerBoundBody, lowerBoundMidpoint, lowerBoundComparison,
      address, lowerBoundStep, midpointWord, ht, haddress, hcmp]
    constructor
    · simpa using haddress
    · intro hlt
      exact False.elim (hcmp hlt)

/-- The array and operands are already available. The length equality implies
that the array length is representable as a word, including the empty case. -/
structure LowerBoundPre (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (s : State w) : Prop where
  array : ArrayAt heapLimit base xs s
  base_reg : s.regs 0 = base
  key_reg : s.regs 1 = key
  length_reg : (s.regs 3).toNat = xs.length

/-- The answer is decoded without modular ambiguity, and search does not
modify the array, any other source memory, or I/O. Only registers 2–4 change. -/
structure LowerBoundPost (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (entry finish : State w) : Prop where
  array : ArrayAt heapLimit base xs finish
  result : LowerBoundSpec xs key (finish.regs 2).toNat
  mem : finish.mem = entry.mem
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  base_reg : finish.regs 0 = base
  key_reg : finish.regs 1 = key
  other : ∀ r, 5 ≤ r → finish.regs r = entry.regs r

private structure SearchInvariant (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (entry s : State w) : Prop where
  array : ArrayAt heapLimit base xs s
  base_reg : s.regs 0 = base
  key_reg : s.regs 1 = key
  lo_le_hi : (s.regs 2).toNat ≤ (s.regs 3).toNat
  hi_le_length : (s.regs 3).toNat ≤ xs.length
  before : ∀ (i : Nat) (hi : i < xs.length), i < (s.regs 2).toNat →
    xs[i].toNat < key.toNat
  after : ∀ (i : Nat) (hi : i < xs.length), (s.regs 3).toNat ≤ i →
    key.toNat ≤ xs[i].toNat
  mem : s.mem = entry.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → s.regs r = entry.regs r

private theorem sorted_lookup_le {xs : List (Word w)}
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    xs[i].toNat ≤ xs[j].toNat := by
  rcases Nat.eq_or_lt_of_le hij with he | hlt
  · subst j
    exact Nat.le_refl _
  · exact List.pairwise_iff_getElem.mp hsorted i j hi hj hlt

private theorem condition_positive {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w}
    (_h : SearchInvariant heapLimit base key xs entry s)
    (hz : s.eval lowerBoundCondition ≠ 0) : (s.regs 2).toNat < (s.regs 3).toNat := by
  by_contra hn
  exact hz (by simp [lowerBoundCondition, State.eval, Expr.eval, BinOp.eval, hn])

private theorem search_address {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 2 ≤ w)
    (h : SearchInvariant heapLimit base key xs entry s)
    (hz : s.eval lowerBoundCondition ≠ 0) :
    (s.regs 0 + midpointWord s).toNat < heapLimit ∧
      ∃ hi : midpoint s < xs.length,
        s.mem (s.regs 0 + midpointWord s) = xs[midpoint s] := by
  have hmid := midpoint_interval s (condition_positive h hz)
  have hi : midpoint s < xs.length := lt_of_lt_of_le hmid.2 h.hi_le_length
  have hword : midpointWord s = BitVec.ofNat w (midpoint s) := by
    rw [← midpoint_toNat hw s h.lo_le_hi, Word.ofNat_toNat_self]
  have haddr : s.regs 0 + midpointWord s = arrayAddr base (midpoint s) := by
    rw [h.base_reg, hword]
    rfl
  exact ⟨by rw [haddr]; exact h.array.addr_lt hi,
    hi, by rw [haddr]; exact h.array.1.lookup _ hi⟩

private theorem search_step_preserves {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (h : SearchInvariant heapLimit base key xs entry s)
    (hz : s.eval lowerBoundCondition ≠ 0) :
    SearchInvariant heapLimit base key xs entry (lowerBoundStep s) ∧
      ((lowerBoundStep s).regs 3).toNat - ((lowerBoundStep s).regs 2).toNat ≤
        ((s.regs 3).toNat - (s.regs 2).toNat) / 2 := by
  have horder := condition_positive h hz
  have hmid := midpoint_interval s horder
  have hmn := midpoint_toNat hw s h.lo_le_hi
  obtain ⟨_, hi, hload⟩ := search_address hw h hz
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one (by omega)
  have hinc : (midpointWord s + 1).toNat = midpoint s + 1 := by
    have hfit : (midpointWord s).toNat + (1 : Word w).toNat < 2 ^ w := by
      rw [hmn, hone]
      have hhi := Word.toNat_lt (s.regs 3)
      omega
    rw [BitVec.toNat_add_of_lt hfit, hmn, hone]
  have hother (r : Reg) (hr : 5 ≤ r) : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 :=
    ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 5) hr),
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 3 < 5) hr),
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 4 < 5) hr)⟩
  unfold lowerBoundStep
  by_cases hc : (s.mem (s.regs 0 + midpointWord s)).toNat < (s.regs 1).toNat
  · have hkey : xs[midpoint s].toNat < key.toNat := by
      simpa only [hload, h.key_reg] using hc
    simp only [if_pos hc]
    constructor
    · refine ⟨h.array, ?_, ?_, ?_, ?_, ?_, ?_, h.mem, h.input, h.output, ?_⟩
      · simpa [State.setReg] using h.base_reg
      · simpa [State.setReg] using h.key_reg
      · change (midpointWord s + 1).toNat ≤ (s.regs 3).toNat
        rw [hinc]
        omega
      · simpa [State.setReg] using h.hi_le_length
      · intro i hil hip
        have hip' : i ≤ midpoint s := by
          change i < (midpointWord s + 1).toNat at hip
          rw [hinc] at hip
          omega
        exact (sorted_lookup_le hsorted hil hi hip').trans_lt hkey
      · simpa [State.setReg] using h.after
      · intro r hr
        simpa [State.setReg, (hother r hr).1, (hother r hr).2.2] using h.other r hr
    · change (s.regs 3).toNat - (midpointWord s + 1).toNat ≤ _
      rw [hinc]
      dsimp [midpoint]
      omega
  · have hkey : key.toNat ≤ xs[midpoint s].toNat := by
      rw [hload, h.key_reg] at hc
      omega
    simp only [if_neg hc]
    constructor
    · refine ⟨h.array, ?_, ?_, ?_, ?_, ?_, ?_, h.mem, h.input, h.output, ?_⟩
      · simpa [State.setReg] using h.base_reg
      · simpa [State.setReg] using h.key_reg
      · simpa [State.setReg, hmn] using hmid.1
      · simpa [State.setReg, hmn] using Nat.le_trans (Nat.le_of_lt hmid.2) h.hi_le_length
      · simpa [State.setReg] using h.before
      · intro i hil hpi
        have hpi' : midpoint s ≤ i := by simpa [State.setReg, hmn] using hpi
        exact hkey.trans (sorted_lookup_le hsorted hi hil hpi')
      · intro r hr
        simpa [State.setReg, (hother r hr).2.1, (hother r hr).2.2] using h.other r hr
    · change (midpointWord s).toNat - (s.regs 2).toNat ≤ _
      rw [hmn]
      dsimp [midpoint]
      omega

/-- Binary search returns the insertion index in logarithmic machine time.
The cost includes initialization, all evaluated guards, branch jumps and loop
back edges. The final program halt belongs to the compiled-block theorem. -/
theorem lowerBound_contract {control heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    RelContract control program heapLimit depth lowerBound
      (LowerBoundPre heapLimit base key xs) (LowerBoundPost heapLimit base key xs)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 6) := by
  apply RelContract.iff_entry.mpr
  intro entry hpre
  let initialized := entry.setReg 2 0
  have hstart : SearchInvariant heapLimit base key xs entry initialized := by
    refine ⟨hpre.array, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simpa [initialized, State.setReg] using hpre.base_reg
    · simpa [initialized, State.setReg] using hpre.key_reg
    · simp [initialized, State.setReg]
    · simpa [initialized, State.setReg] using Nat.le_of_eq hpre.length_reg
    · intro i hi hip
      simp [initialized, State.setReg] at hip
    · intro i hi hip
      have hn : xs.length ≤ i := by
        simpa [initialized, State.setReg, hpre.length_reg] using hip
      omega
    · intro r hr
      have hne : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 5) hr)
      simp [initialized, State.setReg, hne]
  have hloop : Contract control program heapLimit depth lowerBoundLoop
      (SearchInvariant heapLimit base key xs entry)
      (LowerBoundPost heapLimit base key xs entry)
      (fun s => Nat.clog 2 ((s.regs 3).toNat - (s.regs 2).toNat + 1) * 25 + 4) := by
    apply Contract.while_div_post 2 (by decide)
      (SearchInvariant heapLimit base key xs entry)
      (fun s => (s.regs 3).toNat - (s.regs 2).toNat) 20
    · intro s hs
      exact ⟨trivial, trivial⟩
    · intro s hs hz
      have horder := condition_positive hs hz
      omega
    · intro s hs hz
      obtain ⟨ha, _⟩ := search_address hw hs hz
      apply (lowerBound_body_contract (by omega) s ha).mono_post
      intro t ht
      subst t
      exact search_step_preserves hw hsorted hs hz
    · intro t ht hz
      have hnot : ¬ (t.regs 2).toNat < (t.regs 3).toNat := by
        intro hlt
        have hone := Word.one_ne_zero (w := w) (by omega)
        exact hone (by simpa [lowerBoundCondition, State.eval, Expr.eval, BinOp.eval, hlt] using hz)
      have heq : (t.regs 2).toNat = (t.regs 3).toNat := by
        have hle := ht.lo_le_hi
        omega
      exact ⟨ht.array, ⟨heq.le.trans ht.hi_le_length, ht.before,
        by simpa only [heq] using ht.after⟩,
        ht.mem, ht.input, ht.output, ht.base_reg, ht.key_reg, ht.other⟩
  have hi : Contract control program heapLimit depth (.assign 2 (.const 0))
      (fun s => s = entry) (fun s => s = initialized) (fun _ => 2) := by
    ram_vc s hs [initialized, hs]
  have hl : Contract control program heapLimit depth lowerBoundLoop
      (fun s => s = initialized) (LowerBoundPost heapLimit base key xs entry)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 4) := by
    apply hloop.consequence (fun s hs => by subst s; exact hstart) (fun _ ht => ht)
    intro s hs
    subst s
    simp [initialized, State.setReg, hpre.length_reg, Nat.mul_comm]
  have hc := hi.seq_const hl
  apply hc.mono_budget
  intro s hs
  omega

end Ram.Source.Array
