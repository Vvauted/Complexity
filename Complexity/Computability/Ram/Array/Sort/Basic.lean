/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.BinaryInsertion
import Complexity.Computability.Ram.Array.Range
import Complexity.Computability.Ram.Verification.Loop.Basic
import Complexity.Tactic.Ram.Basic

/-!
# Binary insertion sort on a preloaded RAM array

The outer loop reads the next original element, searches the already sorted
sortedPrefix, shifts its suffix right with actual stores, and inserts the element.
The invariant uses standard `List.insertionSort`, `take`, and `drop`; none of
these mathematical list operations is available to the executed RAM program.

Registers 0 and 5 hold base and total length. Register 6 is the growing prefix
length; registers 1–4 are the insertion module's working registers. Other
source registers, I/O, and memory outside the array are preserved. This is a
preloaded-array contract, with no implicit input loader or output conversion.
-/

namespace Ram.Source.Array.Sort

/-- The canonical mathematical contents of the processed prefix. -/
def sortedPrefix (xs : List (Word w)) (i : Nat) : List (Word w) :=
  (xs.take i).insertionSort unsignedLE

/-- Sorted processed elements followed by the untouched original suffix. -/
def contents (xs : List (Word w)) (i : Nat) : List (Word w) :=
  sortedPrefix xs i ++ xs.drop i

@[simp] theorem prefix_length {xs : List (Word w)} {i : Nat} (hi : i ≤ xs.length) :
    (sortedPrefix xs i).length = i := by
  simp [sortedPrefix, List.length_take, Nat.min_eq_left hi]

@[simp] theorem contents_length (xs : List (Word w)) (i : Nat) :
    (contents xs i).length = xs.length := by
  simp only [contents, sortedPrefix, List.length_append, List.length_insertionSort,
    List.length_take, List.length_drop]
  omega

@[simp] theorem contents_zero (xs : List (Word w)) : contents xs 0 = xs := by
  simp [contents, sortedPrefix]

@[simp] theorem contents_length_eq (xs : List (Word w)) :
    contents xs xs.length = xs.insertionSort unsignedLE := by
  simp [contents, sortedPrefix]

/-- Borrow exactly the sorted prefix plus the next original cell. -/
theorem contents_take_next {xs : List (Word w)} {i : Nat} (hi : i < xs.length) :
    (contents xs i).take (i + 1) = sortedPrefix xs i ++ [xs[i]] := by
  have hp : (sortedPrefix xs i).length = i := prefix_length (Nat.le_of_lt hi)
  simpa only [hp, contents, List.drop_eq_getElem_cons hi, List.take_succ_cons,
    List.take_zero] using
    (List.take_length_add_append (l₁ := sortedPrefix xs i) (l₂ := xs.drop i) 1)

/-- The next unprocessed element has not been changed by earlier insertions. -/
theorem contents_get_next {xs : List (Word w)} {i : Nat} (hi : i < xs.length) :
    (contents xs i)[i]'(by simpa using hi) = xs[i] := by
  have hp : (sortedPrefix xs i).length = i := prefix_length (Nat.le_of_lt hi)
  simp only [contents, List.getElem_append_right (by omega : (sortedPrefix xs i).length ≤ i),
    hp, Nat.sub_self, List.getElem_drop, Nat.add_zero]

/-- Framing the extended prefix retains exactly the remaining original tail. -/
theorem contents_drop_next {xs : List (Word w)} {i : Nat} (hi : i < xs.length) :
    (contents xs i).drop (i + 1) = xs.drop (i + 1) := by
  have hp : (sortedPrefix xs i).length = i := prefix_length (Nat.le_of_lt hi)
  simpa only [hp, contents, List.drop_drop, Nat.add_comm] using
    (List.drop_length_add_append (l₁ := sortedPrefix xs i) (l₂ := xs.drop i) 1)

theorem prefix_step {xs : List (Word w)} {i : Nat} (hi : i < xs.length) :
    (sortedPrefix xs i).orderedInsert unsignedLE xs[i] = sortedPrefix xs (i + 1) :=
  orderedInsert_insertionSort_take_succ hi

/-- Reassemble a borrowed, modified prefix with the original suffix by its
verified frame; this theorem performs no memory copy or runtime operation. -/
theorem advance_array {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {i : Nat} {s t : State w} (hi : i < xs.length)
    (whole : ArrayAt heapLimit base (contents xs i) s)
    (front : ArrayAt heapLimit base (sortedPrefix xs (i + 1)) t)
    (frame : ArrayFrame base (i + 1) s.mem t.mem) :
    ArrayAt heapLimit base (contents xs (i + 1)) t := by
  have hp : (sortedPrefix xs (i + 1)).length = i + 1 := prefix_length (by omega)
  have hlen : (sortedPrefix xs (i + 1)).length ≤ (contents xs i).length := by
    rw [hp, contents_length]
    omega
  have hf : ArrayFrame base (sortedPrefix xs (i + 1)).length s.mem t.mem := by
    simpa only [hp] using frame
  have h := whole.replace_prefix front hlen hf
  rw [hp, contents_drop_next hi] at h
  exact h

def condition : Expr := .bin .ult (.var 6) (.var 5)
def loadKey : Stmt := .assign 1 (.load (address 0 6))
def increment : Stmt := .assign 6 (.bin .add (.var 6) (.const 1))

def body : Stmt := .seq loadKey (.seq BinaryInsertion.program increment)
def loop : Stmt := .while condition body
def program : Stmt := .seq (.assign 6 (.const 0)) loop

theorem wellFormed {locals : Nat} (h : 7 ≤ locals) : program.WellFormed locals := by
  have h0 : 0 < locals := by omega
  have h1 : 1 < locals := by omega
  have h5 : 5 < locals := by omega
  have h6 : 6 < locals := by omega
  simp [program, loop, body, loadKey, increment, condition, address,
    Stmt.WellFormed, Expr.Bounded, BinaryInsertion.wellFormed h, h0, h1, h5, h6]

theorem callsValid (functions : Program) : Compiler.CallsValid functions program := by
  simp [program, loop, body, loadKey, increment, Compiler.CallsValid,
    BinaryInsertion.callsValid functions]

theorem code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable program = 75 := rfl

structure Pre (heapLimit : Nat) (base : Word w) (xs : List (Word w))
    (s : State w) : Prop where
  array : ArrayAt heapLimit base xs s
  base_reg : s.regs 0 = base
  length_reg : (s.regs 5).toNat = xs.length

structure Post (heapLimit : Nat) (base : Word w) (xs : List (Word w))
    (entry s : State w) : Prop where
  array : ArrayAt heapLimit base (xs.insertionSort unsignedLE) s
  frame : ArrayFrame base xs.length entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  base_reg : s.regs 0 = base
  length_reg : s.regs 5 = entry.regs 5
  processed_reg : (s.regs 6).toNat = xs.length
  other : ∀ r, 7 ≤ r → s.regs r = entry.regs r

private structure Invariant (heapLimit : Nat) (base : Word w) (xs : List (Word w))
    (entry s : State w) : Prop where
  index_le : (s.regs 6).toNat ≤ xs.length
  array : ArrayAt heapLimit base (contents xs (s.regs 6).toNat) s
  frame : ArrayFrame base xs.length entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  base_reg : s.regs 0 = base
  length_reg : s.regs 5 = entry.regs 5
  other : ∀ r, 7 ≤ r → s.regs r = entry.regs r

private theorem index_lt {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {entry s : State w} (hw : 0 < w) (hp : Pre heapLimit base xs entry)
    (hs : Invariant heapLimit base xs entry s) (hz : s.eval condition ≠ 0) :
    (s.regs 6).toNat < xs.length := by
  have hcmp := (BinOp.eval_ult_ne_zero_iff hw (s.regs 6) (s.regs 5)).mp hz
  simpa only [hs.length_reg, hp.length_reg] using hcmp

/-- The only heap load added by the outer traversal is the next key. The
binary-insertion module supplies its own proved stores, bounds, and frame. -/
private theorem body_contract {control heapLimit depth : Nat} {functions : Program}
    {base : Word w} {xs : List (Word w)} {entry s : State w}
    (hw : 2 ≤ w) (hp : Pre heapLimit base xs entry)
    (hs : Invariant heapLimit base xs entry s) (hz : s.eval condition ≠ 0) :
    Contract control functions heapLimit depth body (fun t => t = s)
      (fun t => Invariant heapLimit base xs entry t ∧
        xs.length - (t.regs 6).toNat < xs.length - (s.regs 6).toNat)
      (fun _ => 25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 30) := by
  let i := (s.regs 6).toNat
  have hi : i < xs.length := index_lt (by omega) hp hs hz
  let key := xs[i]
  let saved := s.setReg 1 key
  have hprefix : (sortedPrefix xs i).length = i := prefix_length (Nat.le_of_lt hi)
  have haddr : s.regs 0 + s.regs 6 = arrayAddr base i := by
    simp only [arrayAddr, i, Word.ofNat_toNat_self, hs.base_reg]
  have haddress : (s.regs 0 + s.regs 6).toNat < heapLimit := by
    rw [haddr]
    exact hs.array.addr_lt (by simpa only [contents_length] using hi)
  have hkey : s.mem (s.regs 0 + s.regs 6) = key := by
    rw [haddr, hs.array.1.lookup i (by simpa only [contents_length] using hi)]
    exact contents_get_next hi
  have hload : Contract control functions heapLimit depth loadKey (fun t => t = s)
      (fun t => t = saved) (fun _ => 5) := by
    ram_vc t ht [loadKey, address, ht, haddress, hkey, saved]
  have hborrow : ArrayAt heapLimit base (sortedPrefix xs i ++ [key]) saved := by
    have h := (hs.array.take (i + 1)).setReg 1 key
    change ArrayAt heapLimit base ((contents xs i).take (i + 1)) saved at h
    rw [contents_take_next hi] at h
    exact h
  have hpre : BinaryInsertion.Pre heapLimit base key (sortedPrefix xs i) key saved := by
    refine ⟨hborrow, ?_, ?_, ?_⟩
    · simpa [saved, State.setReg] using hs.base_reg
    · simp [saved, State.setReg]
    · simpa [saved, State.setReg, i] using hprefix.symm
  have hsorted : (sortedPrefix xs i).Pairwise unsignedLE :=
    (SortedPerm.insertionSort (xs.take i)).sorted
  have hbin : Contract control functions heapLimit depth BinaryInsertion.program
      (fun t => t = saved) (BinaryInsertion.Post heapLimit base key (sortedPrefix xs i) saved)
      (fun _ => 25 * Nat.clog 2 (i + 1) + 19 * i + 21) := by
    have h := RelContract.iff_entry.mp
      (BinaryInsertion.contract (control := control) (functions := functions)
        (depth := depth) hw hsorted) saved hpre
    simpa only [hprefix] using h
  have hinc : Contract control functions heapLimit depth increment
      (BinaryInsertion.Post heapLimit base key (sortedPrefix xs i) saved)
      (fun t => Invariant heapLimit base xs entry t ∧
        xs.length - (t.regs 6).toNat < xs.length - (s.regs 6).toNat)
      (fun _ => 4) := by
    apply Verification.verify
    intro t ht
    have h6 : t.regs 6 = s.regs 6 := by
      simpa [saved, State.setReg] using ht.other 6 (by decide)
    have h5 : t.regs 5 = s.regs 5 := by
      simpa [saved, State.setReg] using ht.other 5 (by decide)
    have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one (by omega)
    have hfit : (t.regs 6).toNat + (1 : Word w).toNat < 2 ^ w := by
      have hN : xs.length < 2 ^ w := by
        rw [← hp.length_reg]
        exact Word.toNat_lt _
      rw [h6, hone]
      change i + 1 < 2 ^ w
      omega
    have hv : ((t.setReg 6 (t.regs 6 + 1)).regs 6).toNat = i + 1 := by
      change (t.regs 6 + 1).toNat = i + 1
      rw [BitVec.toNat_add_of_lt hfit, hone, h6]
    have hfront : ArrayAt heapLimit base (sortedPrefix xs (i + 1)) t := by
      have h := ht.array
      change ArrayAt heapLimit base ((sortedPrefix xs i).orderedInsert unsignedLE xs[i]) t at h
      rw [prefix_step hi] at h
      exact h
    have hframe : ArrayFrame base (i + 1) s.mem t.mem := by
      simpa only [hprefix, saved, State.setReg_mem] using ht.frame
    have hwhole := advance_array hi hs.array hfront hframe
    have hpost : Invariant heapLimit base xs entry (t.setReg 6 (t.regs 6 + 1)) ∧
        xs.length - ((t.setReg 6 (t.regs 6 + 1)).regs 6).toNat <
          xs.length - (s.regs 6).toNat := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hv]
        omega
      · rw [hv]
        exact hwhole.setReg _ _
      · exact hs.frame.trans (hframe.mono (by omega))
      · exact ht.input.trans hs.input
      · exact ht.output.trans hs.output
      · simpa [State.setReg] using ht.base_reg
      · simpa [State.setReg, h5] using hs.length_reg
      · intro r hr
        have hr6 : r ≠ 6 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 6 < 7) hr)
        have hr1 : r ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1 < 7) hr)
        simpa [State.setReg, saved, hr6, hr1] using
          (ht.other r (Nat.le_trans (by decide : 5 ≤ 7) hr)).trans
            (show saved.regs r = entry.regs r from by
              simpa [saved, State.setReg, hr1] using hs.other r hr)
      · rw [hv]
        change xs.length - (i + 1) < xs.length - i
        omega
    ram_vc [increment]
    simpa only [State.setReg_same, BitVec.toNat_add, hone] using hpost
  have h := hload.seq_const (hbin.seq_const hinc)
  apply h.mono_budget
  intro t ht
  have hlog : Nat.clog 2 (i + 1) ≤ Nat.clog 2 (xs.length + 1) :=
    Nat.clog_mono_right 2 (by omega)
  omega

/-- A quadratic word-RAM bound with logarithmic searches and linear shifts.
The expression is obtained by charging the proved insertion bound at most
once for each original element, plus every outer guard and back edge. -/
def budget (length : Nat) : Nat :=
  length * (25 * Nat.clog 2 (length + 1) + 19 * length + 35) + 6

theorem contract {control heapLimit depth : Nat} {functions : Program}
    {base : Word w} {xs : List (Word w)} (hw : 2 ≤ w) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit base xs) (Post heapLimit base xs) (fun _ => budget xs.length) := by
  apply RelContract.iff_entry.mpr
  intro entry hp
  have hinit : Contract control functions heapLimit depth (.assign 6 (.const 0))
      (fun s => s = entry) (Invariant heapLimit base xs entry) (fun _ => 2) := by
    apply Verification.verify
    intro s hs
    subst s
    have hpost : Invariant heapLimit base xs entry (entry.setReg 6 0) := by
      refine ⟨by simp [State.setReg], ?_, ArrayFrame.refl _ _ _, rfl, rfl, ?_, ?_, ?_⟩
      · simpa only [State.setReg_same, BitVec.toNat_zero, contents_zero] using
          hp.array.setReg 6 0
      · simpa [State.setReg] using hp.base_reg
      · simp [State.setReg]
      · intro r hr
        have hr6 : r ≠ 6 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 6 < 7) hr)
        simp [State.setReg, hr6]
    ram_vc []
    exact hpost
  have hloop : Contract control functions heapLimit depth loop
      (Invariant heapLimit base xs entry) (Post heapLimit base xs entry)
      (fun s => (xs.length - (s.regs 6).toNat) *
        (4 + (25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 30) + 1) + 4) := by
    apply Contract.while_linear_post (Invariant heapLimit base xs entry)
      (fun s => xs.length - (s.regs 6).toNat)
      (25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 30)
    · intro s hs
      exact ⟨True.intro, True.intro⟩
    · intro s hs hz
      exact body_contract hw hp hs hz
    · intro t ht hz
      have hnot : ¬ (t.regs 6).toNat < xs.length := by
        intro hlt
        have hlt' : (t.regs 6).toNat < (t.regs 5).toNat := by
          simpa only [ht.length_reg, hp.length_reg] using hlt
        exact ((BinOp.eval_ult_ne_zero_iff (by omega) _ _).mpr hlt') hz
      have hi : (t.regs 6).toNat = xs.length := by
        have hle := ht.index_le
        omega
      refine ⟨?_, ht.frame, ht.input, ht.output, ht.base_reg, ht.length_reg, hi, ht.other⟩
      simpa only [hi, contents_length_eq] using ht.array
  have hloop' : Contract control functions heapLimit depth loop
      (Invariant heapLimit base xs entry) (Post heapLimit base xs entry)
      (fun _ => xs.length *
        (25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 35) + 4) := by
    apply hloop.mono_budget
    intro s hs
    have hcost : 4 + (25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 30) + 1 =
        25 * Nat.clog 2 (xs.length + 1) + 19 * xs.length + 35 := by omega
    simp only [hcost]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
  have h := hinit.seq_const hloop'
  apply h.mono_budget
  intro s hs
  unfold budget
  omega

end Ram.Source.Array.Sort
