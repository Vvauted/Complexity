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

The shared search block uses configurable register roles and unsigned comparisons.
The fixed specialization takes its base and key in registers 0 and 1, its length
in register 3, returns the insertion index in register 2, and uses register 4
as a temporary.
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

namespace Search

/-- Register roles of lower-bound search. The writable endpoints and midpoint
are distinct and do not overwrite either read-only operand. The read-only base
and key may share a register when their values agree. -/
structure Registers where
  base : Reg
  key : Reg
  lo : Reg
  hi : Reg
  mid : Reg
  base_ne_lo : base ≠ lo
  base_ne_hi : base ≠ hi
  base_ne_mid : base ≠ mid
  key_ne_lo : key ≠ lo
  key_ne_hi : key ≠ hi
  key_ne_mid : key ≠ mid
  lo_ne_hi : lo ≠ hi
  lo_ne_mid : lo ≠ mid
  hi_ne_mid : hi ≠ mid

variable (registers : Registers)

private abbrev conditionCode (lo hi : Reg) : Expr := .bin .ult (.var lo) (.var hi)

private abbrev midpointCode (lo hi : Reg) : Expr :=
  .bin .add (.var lo) (.bin .udiv (.bin .sub (.var hi) (.var lo)) (.const 2))

private abbrev comparisonCode (base key mid : Reg) : Expr :=
  .bin .ult (.load (address base mid)) (.var key)

private abbrev bodyCode (base key lo hi mid : Reg) : Stmt :=
  .seq (.assign mid (midpointCode lo hi))
    (.ite (comparisonCode base key mid)
      (.assign lo (.bin .add (.var mid) (.const 1)))
      (.assign hi (.var mid)))

/-- The source loop before register separation is proved. Declaration bindings
can determine the raw register roles from this syntax, then discharge the
distinctness conditions required by the shared search proofs. -/
abbrev loopCode (base key lo hi mid : Reg) : Stmt :=
  .while (conditionCode lo hi) (bodyCode base key lo hi mid)

/-- The interval is nonempty. -/
abbrev condition : Expr := conditionCode registers.lo registers.hi

/-- Compute the midpoint without adding both endpoints. -/
abbrev midpointExpr : Expr := midpointCode registers.lo registers.hi

/-- Compare the array entry at the midpoint with the key. -/
abbrev comparison : Expr :=
  comparisonCode registers.base registers.key registers.mid

/-- One midpoint assignment followed by the selected endpoint update. -/
abbrev body : Stmt :=
  bodyCode registers.base registers.key registers.lo registers.hi registers.mid

/-- Search an already initialized interval. -/
abbrev loop : Stmt :=
  loopCode registers.base registers.key registers.lo registers.hi registers.mid

/-- Initialize the left endpoint and search up to the supplied right endpoint. -/
abbrev lowerBound : Stmt := .seq (.assign registers.lo (.const 0)) (loop registers)

/-- The search block only reads and writes its five declared register roles. -/
theorem lowerBound_wellFormed {locals : Nat}
    (hbase : registers.base < locals) (hkey : registers.key < locals)
    (hlo : registers.lo < locals) (hhi : registers.hi < locals)
    (hmid : registers.mid < locals) :
    (lowerBound registers).WellFormed locals := by
  simp [address, Stmt.WellFormed, Expr.Bounded, hbase, hkey, hlo, hhi, hmid]

theorem body_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (body registers) = 22 := rfl

theorem lowerBound_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (lowerBound registers) = 29 := rfl

/-- The mathematical midpoint of the current interval. -/
def midpoint (s : State w) : Nat :=
  (s.regs registers.lo).toNat +
    ((s.regs registers.hi).toNat - (s.regs registers.lo).toNat) / 2

/-- The word expression used by the actual source body. -/
def midpointWord (s : State w) : Word w :=
  s.regs registers.lo + (s.regs registers.hi - s.regs registers.lo) / 2

/-- Exact state effect of one source body execution. -/
def step (s : State w) : State w :=
  if (s.mem (s.regs registers.base + midpointWord registers s)).toNat <
      (s.regs registers.key).toNat then
    (s.setReg registers.mid (midpointWord registers s)).setReg registers.lo
      (midpointWord registers s + 1)
  else
    (s.setReg registers.mid (midpointWord registers s)).setReg registers.hi
      (midpointWord registers s)

/-- Ordered word endpoints make the midpoint computation exact. -/
theorem midpoint_toNat (hw : 2 ≤ w) (s : State w)
    (horder : (s.regs registers.lo).toNat ≤ (s.regs registers.hi).toNat) :
    (midpointWord registers s).toNat = midpoint registers s := by
  have htwoFit : 2 < 2 ^ w := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have htwo : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt htwoFit
  have hdiv : ((s.regs registers.hi - s.regs registers.lo) / 2).toNat =
      ((s.regs registers.hi).toNat - (s.regs registers.lo).toNat) / 2 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_sub_of_le horder, htwo]
  have hfit : (s.regs registers.lo).toNat +
      ((s.regs registers.hi - s.regs registers.lo) / 2).toNat < 2 ^ w := by
    rw [hdiv]
    have hhalf := Nat.div_le_self
      ((s.regs registers.hi).toNat - (s.regs registers.lo).toNat) 2
    have hhi := Word.toNat_lt (s.regs registers.hi)
    omega
  exact (BitVec.toNat_add_of_lt hfit).trans
    (congrArg ((s.regs registers.lo).toNat + ·) hdiv)

/-- A nonempty interval contains its midpoint. -/
theorem midpoint_interval (s : State w)
    (horder : (s.regs registers.lo).toNat < (s.regs registers.hi).toNat) :
    (s.regs registers.lo).toNat ≤ midpoint registers s ∧
      midpoint registers s < (s.regs registers.hi).toNat := by
  unfold midpoint
  have hhalf := Nat.div_lt_self
    (show 0 < (s.regs registers.hi).toNat - (s.regs registers.lo).toNat by omega)
    (by decide : 1 < 2)
  omega

/-- The longest branch uses twenty generated instructions; the shorter one
uses seventeen. The full static block also contains the unselected branch. -/
theorem body_contract {control heapLimit depth : Nat} {program : Program}
    (hw : 0 < w) (s : State w)
    (haddress : (s.regs registers.base + midpointWord registers s).toNat < heapLimit) :
    Contract control program heapLimit depth (body registers) (fun t => t = s)
      (fun t => t = step registers s) (fun _ => 20) := by
  by_cases hcmp : (s.mem (s.regs registers.base + midpointWord registers s)).toNat <
      (s.regs registers.key).toNat
  · dsimp only [midpointWord] at hcmp
    ram_vc t ht [body, midpointExpr, comparison, address, step, midpointWord,
      ht, haddress, hcmp, Word.one_ne_zero hw,
      registers.base_ne_mid, registers.key_ne_mid]
    constructor
    · simpa [midpointWord] using haddress
    · intro hzero
      exact False.elim ((Nat.ne_of_gt hw) (hzero hcmp))
  · dsimp only [midpointWord] at hcmp
    ram_vc t ht [body, midpointExpr, comparison, address, step, midpointWord,
      ht, haddress, hcmp, registers.base_ne_mid, registers.key_ne_mid]
    constructor
    · simpa [midpointWord] using haddress
    · intro hlt
      exact False.elim (hcmp hlt)

/-- The represented array and operands are available in the chosen registers.
The right endpoint contains the word-representable array length. -/
structure Pre (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (s : State w) : Prop where
  array : ArrayAt heapLimit base xs s
  base_reg : s.regs registers.base = base
  key_reg : s.regs registers.key = key
  length_reg : (s.regs registers.hi).toNat = xs.length

/-- Search returns an exact insertion index, preserves shared state, and changes
no register other than the endpoints and midpoint. -/
structure Post (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (entry finish : State w) : Prop where
  array : ArrayAt heapLimit base xs finish
  result : LowerBoundSpec xs key (finish.regs registers.lo).toNat
  mem : finish.mem = entry.mem
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  base_reg : finish.regs registers.base = base
  key_reg : finish.regs registers.key = key
  other : ∀ r, r ≠ registers.lo → r ≠ registers.hi → r ≠ registers.mid →
    finish.regs r = entry.regs r

/-- A represented search interval with its already classified prefix and suffix.
The invariant also retains the entire shared state and unrelated registers. -/
structure Invariant (heapLimit : Nat) (base key : Word w)
    (xs : List (Word w)) (entry s : State w) : Prop where
  array : ArrayAt heapLimit base xs s
  base_reg : s.regs registers.base = base
  key_reg : s.regs registers.key = key
  lo_le_hi : (s.regs registers.lo).toNat ≤ (s.regs registers.hi).toNat
  hi_le_length : (s.regs registers.hi).toNat ≤ xs.length
  before : ∀ (i : Nat) (hi : i < xs.length), i < (s.regs registers.lo).toNat →
    xs[i].toNat < key.toNat
  after : ∀ (i : Nat) (hi : i < xs.length), (s.regs registers.hi).toNat ≤ i →
    key.toNat ≤ xs[i].toNat
  mem : s.mem = entry.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, r ≠ registers.lo → r ≠ registers.hi → r ≠ registers.mid →
    s.regs r = entry.regs r

private theorem sorted_lookup_le {xs : List (Word w)}
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    xs[i].toNat ≤ xs[j].toNat := by
  rcases Nat.eq_or_lt_of_le hij with he | hlt
  · subst j
    exact Nat.le_refl _
  · exact List.pairwise_iff_getElem.mp hsorted i j hi hj hlt

/-- A successful guard establishes strict endpoint order. -/
theorem condition_positive {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w}
    (_h : Invariant registers heapLimit base key xs entry s)
    (hz : s.eval (condition registers) ≠ 0) :
    (s.regs registers.lo).toNat < (s.regs registers.hi).toNat := by
  by_contra hn
  exact hz (by simp [State.eval, Expr.eval, BinOp.eval, hn])

/-- The midpoint lookup is a safe read of the corresponding ordinary list entry. -/
theorem search_address {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 2 ≤ w)
    (h : Invariant registers heapLimit base key xs entry s)
    (hz : s.eval (condition registers) ≠ 0) :
    (s.regs registers.base + midpointWord registers s).toNat < heapLimit ∧
      ∃ hi : midpoint registers s < xs.length,
        s.mem (s.regs registers.base + midpointWord registers s) =
          xs[midpoint registers s] := by
  have hmid := midpoint_interval registers s (condition_positive registers h hz)
  have hi : midpoint registers s < xs.length := lt_of_lt_of_le hmid.2 h.hi_le_length
  have hword : midpointWord registers s = BitVec.ofNat w (midpoint registers s) := by
    rw [← midpoint_toNat registers hw s h.lo_le_hi, Word.ofNat_toNat_self]
  have haddr : s.regs registers.base + midpointWord registers s =
      arrayAddr base (midpoint registers s) := by
    rw [h.base_reg, hword]
    rfl
  exact ⟨by rw [haddr]; exact h.array.addr_lt hi,
    hi, by rw [haddr]; exact h.array.1.lookup _ hi⟩

/-- The same source step preserves the search invariant and halves the remaining
interval. Correctness and logarithmic costs can reuse this mathematical fact. -/
theorem step_preserves {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (h : Invariant registers heapLimit base key xs entry s)
    (hz : s.eval (condition registers) ≠ 0) :
    Invariant registers heapLimit base key xs entry (step registers s) ∧
      ((step registers s).regs registers.hi).toNat -
          ((step registers s).regs registers.lo).toNat ≤
        ((s.regs registers.hi).toNat - (s.regs registers.lo).toNat) / 2 := by
  have horder := condition_positive registers h hz
  have hmid := midpoint_interval registers s horder
  have hmn := midpoint_toNat registers hw s h.lo_le_hi
  obtain ⟨_, hi, hload⟩ := search_address registers hw h hz
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one (by omega)
  have hinc : (midpointWord registers s + 1).toNat = midpoint registers s + 1 := by
    have hfit : (midpointWord registers s).toNat + (1 : Word w).toNat < 2 ^ w := by
      rw [hmn, hone]
      have hhi := Word.toNat_lt (s.regs registers.hi)
      omega
    rw [BitVec.toNat_add_of_lt hfit, hmn, hone]
  unfold step
  by_cases hc : (s.mem (s.regs registers.base + midpointWord registers s)).toNat <
      (s.regs registers.key).toNat
  · have hkey : xs[midpoint registers s].toNat < key.toNat := by
      simpa only [hload, h.key_reg] using hc
    simp only [if_pos hc]
    constructor
    · refine ⟨h.array, ?_, ?_, ?_, ?_, ?_, ?_, h.mem, h.input, h.output, ?_⟩
      · simpa [State.setReg, registers.base_ne_lo, registers.base_ne_mid] using h.base_reg
      · simpa [State.setReg, registers.key_ne_lo, registers.key_ne_mid] using h.key_reg
      · simp only [State.setReg, if_neg (Ne.symm registers.lo_ne_hi),
          if_neg registers.hi_ne_mid, ite_true]
        rw [hinc]
        omega
      · simpa [State.setReg, Ne.symm registers.lo_ne_hi, registers.hi_ne_mid]
          using h.hi_le_length
      · intro i hil hip
        have hip' : i ≤ midpoint registers s := by
          have hip'' : i < (midpointWord registers s + 1).toNat := by
            simpa [State.setReg] using hip
          rw [hinc] at hip''
          omega
        exact (sorted_lookup_le hsorted hil hi hip').trans_lt hkey
      · simpa [State.setReg, Ne.symm registers.lo_ne_hi, registers.hi_ne_mid] using h.after
      · intro r hlo hhi hmid
        simpa [State.setReg, hlo, hmid] using h.other r hlo hhi hmid
    · simp only [State.setReg, if_neg (Ne.symm registers.lo_ne_hi),
        if_neg registers.hi_ne_mid, ite_true]
      rw [hinc]
      dsimp [midpoint]
      omega
  · have hkey : key.toNat ≤ xs[midpoint registers s].toNat := by
      rw [hload, h.key_reg] at hc
      omega
    simp only [if_neg hc]
    constructor
    · refine ⟨h.array, ?_, ?_, ?_, ?_, ?_, ?_, h.mem, h.input, h.output, ?_⟩
      · simpa [State.setReg, registers.base_ne_hi, registers.base_ne_mid] using h.base_reg
      · simpa [State.setReg, registers.key_ne_hi, registers.key_ne_mid] using h.key_reg
      · simpa [State.setReg, registers.lo_ne_hi, registers.lo_ne_mid, hmn] using hmid.1
      · simpa [State.setReg, hmn] using
          Nat.le_trans (Nat.le_of_lt hmid.2) h.hi_le_length
      · simpa [State.setReg, registers.lo_ne_hi, registers.lo_ne_mid] using h.before
      · intro i hil hpi
        have hpi' : midpoint registers s ≤ i := by
          simpa [State.setReg, hmn] using hpi
        exact hkey.trans (sorted_lookup_le hsorted hi hil hpi')
      · intro r hlo hhi hmid
        simpa [State.setReg, hhi, hmid] using h.other r hlo hhi hmid
    · simp only [State.setReg, if_neg registers.lo_ne_hi,
        if_neg registers.lo_ne_mid, ite_true]
      rw [hmn]
      dsimp [midpoint]
      omega

/-- An already initialized zero left endpoint establishes the loop invariant,
with shared state and unrelated registers framed against the current state. -/
theorem Pre.invariant {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {current : State w}
    (hpre : Pre registers heapLimit base key xs current)
    (hlo : current.regs registers.lo = 0) :
    Invariant registers heapLimit base key xs current current := by
  refine ⟨hpre.array, hpre.base_reg, hpre.key_reg, ?_, hpre.length_reg.le,
    ?_, ?_, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  · simp [hlo]
  · intro i hi hip
    simp [hlo] at hip
  · intro i hi hip
    rw [hpre.length_reg] at hip
    exact (Nat.not_le_of_gt hi hip).elim

/-- The zero-left-endpoint initialization establishes the shared loop invariant. -/
theorem Pre.initialize {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry : State w}
    (hpre : Pre registers heapLimit base key xs entry) :
    Invariant registers heapLimit base key xs entry (entry.setReg registers.lo 0) := by
  refine ⟨hpre.array, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simpa [State.setReg, registers.base_ne_lo] using hpre.base_reg
  · simpa [State.setReg, registers.key_ne_lo] using hpre.key_reg
  · simp [State.setReg]
  · simpa [State.setReg, Ne.symm registers.lo_ne_hi] using Nat.le_of_eq hpre.length_reg
  · intro i hi hip
    simp [State.setReg] at hip
  · intro i hi hip
    have hn : xs.length ≤ i := by
      simpa [State.setReg, Ne.symm registers.lo_ne_hi, hpre.length_reg] using hip
    omega
  · intro r hlo _ _
    simp [State.setReg, hlo]

/-- At loop exit, the classified prefix and suffix meet at the insertion index. -/
theorem Invariant.exit {heapLimit : Nat} {base key : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (h : Invariant registers heapLimit base key xs entry s)
    (hz : s.eval (condition registers) = 0) :
    Post registers heapLimit base key xs entry s := by
  have hnot : ¬ (s.regs registers.lo).toNat < (s.regs registers.hi).toNat := by
    intro hlt
    exact (Word.one_ne_zero (w := w) hw)
      (by simpa [condition, State.eval, Expr.eval, BinOp.eval, hlt] using hz)
  have heq : (s.regs registers.lo).toNat = (s.regs registers.hi).toNat := by
    have hle := h.lo_le_hi
    omega
  exact ⟨h.array, ⟨heq.le.trans h.hi_le_length, h.before,
    by simpa only [heq] using h.after⟩,
    h.mem, h.input, h.output, h.base_reg, h.key_reg, h.other⟩

/-- Search any interval satisfying the shared invariant. The bound counts actual
guards, selected body instructions and backedges, independently of register names. -/
theorem loop_contract {control heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) (entry : State w) :
    Contract control program heapLimit depth (loop registers)
      (Invariant registers heapLimit base key xs entry)
      (Post registers heapLimit base key xs entry)
      (fun s => Nat.clog 2 ((s.regs registers.hi).toNat -
        (s.regs registers.lo).toNat + 1) * 25 + 4) := by
  apply Contract.while_div_post 2 (by decide)
    (Invariant registers heapLimit base key xs entry)
    (fun s => (s.regs registers.hi).toNat - (s.regs registers.lo).toNat) 20
  · intro s hs
    exact ⟨trivial, trivial⟩
  · intro s hs hz
    have horder := condition_positive registers hs hz
    omega
  · intro s hs hz
    obtain ⟨ha, _⟩ := search_address registers hw hs hz
    apply (body_contract registers (by omega) s ha).mono_post
    intro t ht
    subst t
    exact step_preserves registers hw hsorted hs hz
  · intro s hs hz
    exact Invariant.exit registers (by omega) hs hz

/-- Initialize and search the complete represented array in logarithmic machine
time. The final halt belongs to the compiled-block or function invocation rule. -/
theorem lowerBound_contract {control heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    RelContract control program heapLimit depth (lowerBound registers)
      (Pre registers heapLimit base key xs) (Post registers heapLimit base key xs)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 6) := by
  apply RelContract.iff_entry.mpr
  intro entry hpre
  let initialized := entry.setReg registers.lo 0
  have hstart : Invariant registers heapLimit base key xs entry initialized :=
    Pre.initialize registers hpre
  have hi : Contract control program heapLimit depth (.assign registers.lo (.const 0))
      (fun s => s = entry) (fun s => s = initialized) (fun _ => 2) := by
    ram_vc s hs [initialized, hs]
  have hl : Contract control program heapLimit depth (loop registers)
      (fun s => s = initialized) (Post registers heapLimit base key xs entry)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 4) := by
    apply (loop_contract registers hw hsorted entry).consequence
      (fun s hs => by subst s; exact hstart) (fun _ ht => ht)
    intro s hs
    subst s
    simp [initialized, State.setReg, Ne.symm registers.lo_ne_hi,
      hpre.length_reg, Nat.mul_comm]
  have hc := hi.seq_const hl
  apply hc.mono_budget
  intro s hs
  omega

/-- The register layout used by the preloaded lower-bound block. -/
def fixedRegisters : Registers where
  base := 0
  key := 1
  lo := 2
  hi := 3
  mid := 4
  base_ne_lo := by decide
  base_ne_hi := by decide
  base_ne_mid := by decide
  key_ne_lo := by decide
  key_ne_hi := by decide
  key_ne_mid := by decide
  lo_ne_hi := by decide
  lo_ne_mid := by decide
  hi_ne_mid := by decide

end Search

def lowerBoundCondition : Expr := Search.condition Search.fixedRegisters

def lowerBoundMidpoint : Expr := Search.midpointExpr Search.fixedRegisters

def lowerBoundComparison : Expr := Search.comparison Search.fixedRegisters

def lowerBoundBody : Stmt := Search.body Search.fixedRegisters

def lowerBoundLoop : Stmt := Search.loop Search.fixedRegisters

/-- Initialize the left endpoint and run the fixed binary-search loop. -/
def lowerBound : Stmt := Search.lowerBound Search.fixedRegisters

theorem lowerBound_wellFormed {locals : Nat} (h : 5 ≤ locals) :
    lowerBound.WellFormed locals :=
  Search.lowerBound_wellFormed Search.fixedRegisters
    (by change 0 < locals; omega) (by change 1 < locals; omega)
    (by change 2 < locals; omega) (by change 3 < locals; omega)
    (by change 4 < locals; omega)

theorem lowerBound_body_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable lowerBoundBody = 22 := rfl

theorem lowerBound_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable lowerBound = 29 := rfl

/-- Exact state effect of the body: one midpoint assignment and one endpoint update. -/
def lowerBoundStep (s : State w) : State w := Search.step Search.fixedRegisters s

/-- The longest branch uses twenty generated instructions; the shorter one
uses seventeen. The full static block also contains the unselected branch. -/
theorem lowerBound_body_contract {control heapLimit depth : Nat} {program : Program}
    (hw : 0 < w) (s : State w)
    (haddress : (s.regs 0 + (s.regs 2 + (s.regs 3 - s.regs 2) / 2)).toNat < heapLimit) :
    Contract control program heapLimit depth lowerBoundBody (fun t => t = s)
      (fun t => t = lowerBoundStep s) (fun _ => 20) :=
  Search.body_contract Search.fixedRegisters hw s haddress

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

/-- Binary search returns the insertion index in logarithmic machine time.
The cost includes initialization, all evaluated guards, branch jumps and loop
back edges. The final program halt belongs to the compiled-block theorem. -/
theorem lowerBound_contract {control heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (hsorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    RelContract control program heapLimit depth lowerBound
      (LowerBoundPre heapLimit base key xs) (LowerBoundPost heapLimit base key xs)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 6) := by
  intro entry hpre
  obtain ⟨steps, finish, execution, post, bound⟩ :=
    Search.lowerBound_contract Search.fixedRegisters hw hsorted entry
      ⟨hpre.array, hpre.base_reg, hpre.key_reg, hpre.length_reg⟩
  refine ⟨steps, finish, execution,
    ⟨post.array, post.result, post.mem, post.input, post.output,
      post.base_reg, post.key_reg, ?_⟩, bound⟩
  intro r hr
  have hlo : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 5) hr)
  have hhi : r ≠ 3 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 3 < 5) hr)
  have hmid : r ≠ 4 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 4 < 5) hr)
  exact post.other r hlo hhi hmid

end Ram.Source.Array
