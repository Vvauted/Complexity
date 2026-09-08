/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Ordering
import Complexity.Computability.Ram.Array.Traversal
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Tactic.Ram.Total

/-!
# A linear RAM merge into a disjoint destination

This fixed five-register program performs ordinary loads, stores, increments,
and decrements. The two source arrays may overlap each other: only the
destination must be disjoint from each source. The loop guard is bitwise OR,
not addition, so the two remaining lengths need not have a word-sized sum.
The specification uses standard `List.merge`; this is a preloaded-array
block contract and does not include an uncharged loader or allocator.
-/

namespace Ram.Source.Array.Merge

def condition : Expr := .bin .bor (.var 3) (.var 4)
def comparison : Expr := .bin .ule (.load (.var 0)) (.load (.var 1))

/-- Emit a source word, advance both pointers, and decrement that source's count. -/
def emit (pointer count : Reg) : Stmt :=
  .seq (.store (.var 2) (.load (.var pointer)))
    (.seq (.assign pointer (.bin .add (.var pointer) (.const 1)))
      (.seq (.assign 2 (.bin .add (.var 2) (.const 1)))
        (.assign count (.bin .sub (.var count) (.const 1)))))

def body : Stmt :=
  .ite (.var 3)
    (.ite (.var 4) (.ite comparison (emit 0 3) (emit 1 4)) (emit 0 3))
    (emit 1 4)

def program : Stmt := .while condition body

theorem wellFormed {locals : Nat} (h : 5 ≤ locals) : program.WellFormed locals := by
  have h0 : 0 < locals := Nat.lt_of_lt_of_le (by decide : 0 < 5) h
  have h1 : 1 < locals := Nat.lt_of_lt_of_le (by decide : 1 < 5) h
  have h2 : 2 < locals := Nat.lt_of_lt_of_le (by decide : 2 < 5) h
  have h3 : 3 < locals := Nat.lt_of_lt_of_le (by decide : 3 < 5) h
  have h4 : 4 < locals := Nat.lt_of_lt_of_le (by decide : 4 < 5) h
  simp [program, body, emit, condition, comparison, Stmt.WellFormed,
    Expr.Bounded, h0, h1, h2, h3, h4]

theorem callsValid (functions : Program) : Compiler.CallsValid functions program := by
  simp [program, body, emit, Compiler.CallsValid]

theorem emit_code_size (control : Nat) (localsTable : Nat → Nat) (pointer count : Reg) :
    LocalCompiler.stmtSize control localsTable (emit pointer count) = 16 := rfl

theorem code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable program = 82 := rfl

def emitResult (pointer count : Reg) (s : State w) : State w :=
  (((s.setMem (s.regs 2) (s.mem (s.regs pointer))).setReg pointer
    (s.regs pointer + 1)).setReg 2 (s.regs 2 + 1)).setReg count (s.regs count - 1)

def chooseLeft (s : State w) : Prop :=
  s.regs 3 ≠ 0 ∧ (s.regs 4 = 0 ∨ (s.mem (s.regs 0)).toNat ≤ (s.mem (s.regs 1)).toNat)

instance (s : State w) : Decidable (chooseLeft s) := inferInstanceAs (Decidable (_ ∧ _))

def bodyResult (s : State w) : State w :=
  if chooseLeft s then emitResult 0 3 s else emitResult 1 4 s

/-- One merge iteration has the expected state effect, without a time bound. -/
theorem body_total_contract {heapLimit depth : Nat} {functions : Program}
    (hw : 0 < w) (s : State w)
    (hleft : s.regs 3 ≠ 0 → (s.regs 0).toNat < heapLimit)
    (hright : s.regs 4 ≠ 0 → (s.regs 1).toNat < heapLimit)
    (hdestination : (s.regs 2).toNat < heapLimit)
    (hactive : s.eval condition ≠ 0) :
    TotalContract functions heapLimit depth body (fun t => t = s)
      (fun t => t = bodyResult s) := by
  by_cases hl : s.regs 3 = 0
  · have hr : s.regs 4 ≠ 0 := by
      intro hr
      apply hactive
      simp [condition, State.eval, Expr.eval, BinOp.eval, hl, hr]
    have hs := hright hr
    ram_total_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
      ht, hl, hr, hs, hdestination]
  · have hs := hleft hl
    by_cases hr : s.regs 4 = 0
    · ram_total_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
        ht, hl, hr, hs, hdestination]
      all_goals simp_all
    · have hs' := hright hr
      by_cases hcmp : (s.mem (s.regs 0)).toNat ≤ (s.mem (s.regs 1)).toNat
      · ram_total_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
          ht, hl, hr, hs, hs', hdestination, hcmp, Word.one_ne_zero hw]
        all_goals simp_all [Nat.ne_of_gt hw]
      · ram_total_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
          ht, hl, hr, hs, hs', hdestination, hcmp]
        all_goals simp_all

/-- The longest actual branch has 29 instructions, including all its branches.
Unselected branch code is not charged as if it had executed. -/
theorem body_contract {control heapLimit depth : Nat} {functions : Program}
    (hw : 0 < w) (s : State w)
    (hleft : s.regs 3 ≠ 0 → (s.regs 0).toNat < heapLimit)
    (hright : s.regs 4 ≠ 0 → (s.regs 1).toNat < heapLimit)
    (hdestination : (s.regs 2).toNat < heapLimit)
    (hactive : s.eval condition ≠ 0) :
    Contract control functions heapLimit depth body (fun t => t = s)
      (fun t => t = bodyResult s) (fun _ => 29) := by
  by_cases hl : s.regs 3 = 0
  · have hr : s.regs 4 ≠ 0 := by
      intro hr
      apply hactive
      simp [condition, State.eval, Expr.eval, BinOp.eval, hl, hr]
    have hs := hright hr
    ram_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
      ht, hl, hr, hs, hdestination]
  · have hs := hleft hl
    by_cases hr : s.regs 4 = 0
    · ram_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
        ht, hl, hr, hs, hdestination]
      all_goals simp_all
    · have hs' := hright hr
      by_cases hcmp : (s.mem (s.regs 0)).toNat ≤ (s.mem (s.regs 1)).toNat
      · ram_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
          ht, hl, hr, hs, hs', hdestination, hcmp, Word.one_ne_zero hw]
        all_goals simp_all [Nat.ne_of_gt hw]
      · ram_vc t ht [body, emit, comparison, bodyResult, chooseLeft, emitResult,
          ht, hl, hr, hs, hs', hdestination, hcmp]
        all_goals simp_all

structure Pre (heapLimit : Nat) (left right destination : Word w)
    (xs ys scratch : List (Word w)) (s : State w) : Prop where
  left_array : ArrayAt heapLimit left xs s
  right_array : ArrayAt heapLimit right ys s
  destination_array : ArrayAt heapLimit destination scratch s
  left_pointer : s.regs 0 = left
  right_pointer : s.regs 1 = right
  destination_pointer : s.regs 2 = destination
  left_count : (s.regs 3).toNat = xs.length
  right_count : (s.regs 4).toNat = ys.length

structure Post (heapLimit : Nat) (left right destination : Word w)
    (xs ys : List (Word w)) (entry finish : State w) : Prop where
  left_array : ArrayAt heapLimit left xs finish
  right_array : ArrayAt heapLimit right ys finish
  destination_array : ArrayAt heapLimit destination (unsignedMerge xs ys) finish
  frame : ArrayFrame destination (xs.length + ys.length) entry.mem finish.mem
  left_pointer : finish.regs 0 = arrayAddr left xs.length
  right_pointer : finish.regs 1 = arrayAddr right ys.length
  destination_pointer : finish.regs 2 = arrayAddr destination (xs.length + ys.length)
  left_count : finish.regs 3 = 0
  right_count : finish.regs 4 = 0
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → finish.regs r = entry.regs r

private structure InvariantAt (heapLimit : Nat) (left right destination : Word w)
    (xs ys scratch : List (Word w)) (entry : State w) (i j : Nat) (s : State w) : Prop where
  left_le : i ≤ xs.length
  right_le : j ≤ ys.length
  left_array : ArrayAt heapLimit left xs s
  right_array : ArrayAt heapLimit right ys s
  destination_array : ArrayAt heapLimit destination
    ((unsignedMerge xs ys).take (i + j) ++ scratch.drop (i + j)) s
  residual : (unsignedMerge xs ys).drop (i + j) = unsignedMerge (xs.drop i) (ys.drop j)
  left_pointer : s.regs 0 = arrayAddr left i
  right_pointer : s.regs 1 = arrayAddr right j
  destination_pointer : s.regs 2 = arrayAddr destination (i + j)
  left_count : (s.regs 3).toNat = xs.length - i
  right_count : (s.regs 4).toNat = ys.length - j
  frame : ArrayFrame destination (xs.length + ys.length) entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → s.regs r = entry.regs r

private def Invariant (heapLimit : Nat) (left right destination : Word w)
    (xs ys scratch : List (Word w)) (entry s : State w) : Prop :=
  ∃ i j, InvariantAt heapLimit left right destination xs ys scratch entry i j s

private theorem arrayAddr_succ (base : Word w) (i : Nat) :
    arrayAddr base (i + 1) = arrayAddr base i + 1 := by
  simp only [arrayAddr, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

private theorem decrement_toNat (hw : 0 < w) (x : Word w) (hpositive : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  change (BinOp.eval .sub x 1).toNat = _
  rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hone]; omega), hone]

private theorem other_emit (s : State w) {pointer count r : Reg}
    (hp : pointer < 5) (hc : count < 5) (hr : 5 ≤ r) :
    (emitResult pointer count s).regs r = s.regs r := by
  have hp' : r ≠ pointer := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hp hr))
  have hc' : r ≠ count := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hc hr))
  have h2 : r ≠ 2 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 5) hr))
  simp [emitResult, State.setReg, State.setMem, hp', hc', h2]

private theorem residual_step {xs : List α} {i : Nat} {value : α} {rest : List α}
    (hi : i < xs.length) (h : xs.drop i = value :: rest) :
    xs[i] = value ∧ xs.drop (i + 1) = rest := by
  rw [List.drop_eq_getElem_cons hi] at h
  exact List.cons.inj h

private theorem store_progress {heapLimit i j : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s t : State w}
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (h : InvariantAt heapLimit left right destination xs ys scratch entry i j s)
    (hk : i + j < (unsignedMerge xs ys).length)
    (hmem : t.mem = (s.setMem (arrayAddr destination (i + j)) (unsignedMerge xs ys)[i + j]).mem) :
    ArrayAt heapLimit left xs t ∧ ArrayAt heapLimit right ys t ∧
    ArrayAt heapLimit destination
      ((unsignedMerge xs ys).take (i + j + 1) ++ scratch.drop (i + j + 1)) t ∧
    ArrayFrame destination (xs.length + ys.length) entry.mem t.mem := by
  have hlen' : scratch.length = (unsignedMerge xs ys).length := by
    rw [length_unsignedMerge]; exact hlen
  have hlength := copy_prefix_length (unsignedMerge xs ys) scratch hlen' (Nat.le_of_lt hk)
  have hindex : i + j < ((unsignedMerge xs ys).take (i + j) ++ scratch.drop (i + j)).length := by
    rw [hlength]; exact hk
  have hf : ArrayFrame destination (xs.length + ys.length) s.mem t.mem := by
    rw [hmem]
    have hf' := ArrayFrame.store h.destination_array.1 hindex (unsignedMerge xs ys)[i + j]
    rw [hlength, length_unsignedMerge] at hf'
    exact hf'
  refine ⟨h.left_array.frame hf hdl, h.right_array.frame hf hdr, ?_, h.frame.trans hf⟩
  have ha := h.destination_array.setMem hindex (unsignedMerge xs ys)[i + j]
  rw [copy_prefix_step (unsignedMerge xs ys) scratch hlen' hk] at ha
  change ArrayRep t.mem destination _ ∧ _
  rw [hmem]
  exact ha

private theorem emit_left_preserves {heapLimit i j : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (h : InvariantAt heapLimit left right destination xs ys scratch entry i j s)
    (hi : i < xs.length)
    (hchoose : ∀ hj : j < ys.length, unsignedLE xs[i] ys[j]) :
    InvariantAt heapLimit left right destination xs ys scratch entry (i + 1) j
      (emitResult 0 3 s) ∧
    ((emitResult 0 3 s).regs 3).toNat + ((emitResult 0 3 s).regs 4).toNat <
      (s.regs 3).toNat + (s.regs 4).toNat := by
  have hk : i + j < (unsignedMerge xs ys).length := by
    rw [length_unsignedMerge]
    have hj := h.right_le
    omega
  have hnext := residual_step hk (h.residual.trans (unsignedMerge_drop_left hi hchoose))
  have hload : s.mem (s.regs 0) = xs[i] := by
    rw [h.left_pointer]
    exact h.left_array.1.lookup i hi
  have hmem : (emitResult 0 3 s).mem =
      (s.setMem (arrayAddr destination (i + j)) (unsignedMerge xs ys)[i + j]).mem := by
    change (s.setMem (s.regs 2) (s.mem (s.regs 0))).mem = _
    rw [h.destination_pointer, hload, hnext.1]
  obtain ⟨hl, hr, hd, hf⟩ := store_progress hlen hdl hdr h hk hmem
  have hpos : 0 < (s.regs 3).toNat := by rw [h.left_count]; omega
  have hcount : ((emitResult 0 3 s).regs 3).toNat = (s.regs 3).toNat - 1 := by
    simp only [emitResult, State.setReg]
    exact decrement_toNat hw (s.regs 3) hpos
  have hright : (emitResult 0 3 s).regs 4 = s.regs 4 := by
    simp [emitResult, State.setReg, State.setMem]
  have hind : i + 1 + j = i + j + 1 := by omega
  refine ⟨⟨Nat.succ_le_of_lt hi, h.right_le, hl, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hf, h.input, h.output, ?_⟩, ?_⟩
  · simpa only [hind] using hd
  · simpa only [hind] using hnext.2
  · simp [emitResult, State.setReg, State.setMem, h.left_pointer, arrayAddr_succ]
  · simpa [emitResult, State.setReg, State.setMem] using h.right_pointer
  · simp [emitResult, State.setReg, State.setMem, h.destination_pointer, hind, arrayAddr_succ]
  · rw [hcount, h.left_count]
    omega
  · rw [hright]; exact h.right_count
  · intro r hr
    exact (other_emit s (by decide : 0 < 5) (by decide : 3 < 5) hr).trans (h.other r hr)
  · rw [hcount, hright]
    omega

private theorem emit_right_preserves {heapLimit i j : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (h : InvariantAt heapLimit left right destination xs ys scratch entry i j s)
    (hj : j < ys.length)
    (hchoose : ∀ hi : i < xs.length, ys[j].toNat < xs[i].toNat) :
    InvariantAt heapLimit left right destination xs ys scratch entry i (j + 1)
      (emitResult 1 4 s) ∧
    ((emitResult 1 4 s).regs 3).toNat + ((emitResult 1 4 s).regs 4).toNat <
      (s.regs 3).toNat + (s.regs 4).toNat := by
  have hk : i + j < (unsignedMerge xs ys).length := by
    rw [length_unsignedMerge]
    have hi := h.left_le
    omega
  have hnext := residual_step hk (h.residual.trans (unsignedMerge_drop_right hj hchoose))
  have hload : s.mem (s.regs 1) = ys[j] := by
    rw [h.right_pointer]
    exact h.right_array.1.lookup j hj
  have hmem : (emitResult 1 4 s).mem =
      (s.setMem (arrayAddr destination (i + j)) (unsignedMerge xs ys)[i + j]).mem := by
    change (s.setMem (s.regs 2) (s.mem (s.regs 1))).mem = _
    rw [h.destination_pointer, hload, hnext.1]
  obtain ⟨hl, hr, hd, hf⟩ := store_progress hlen hdl hdr h hk hmem
  have hpos : 0 < (s.regs 4).toNat := by rw [h.right_count]; omega
  have hcount : ((emitResult 1 4 s).regs 4).toNat = (s.regs 4).toNat - 1 := by
    simp only [emitResult, State.setReg]
    exact decrement_toNat hw (s.regs 4) hpos
  have hleft : (emitResult 1 4 s).regs 3 = s.regs 3 := by
    simp [emitResult, State.setReg, State.setMem]
  have hind : i + (j + 1) = i + j + 1 := by omega
  refine ⟨⟨h.left_le, Nat.succ_le_of_lt hj, hl, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hf, h.input, h.output, ?_⟩, ?_⟩
  · simpa only [hind] using hd
  · simpa only [hind] using hnext.2
  · simpa [emitResult, State.setReg, State.setMem] using h.left_pointer
  · simp [emitResult, State.setReg, State.setMem, h.right_pointer, arrayAddr_succ]
  · simp [emitResult, State.setReg, State.setMem, h.destination_pointer, hind, arrayAddr_succ]
  · rw [hleft]; exact h.left_count
  · rw [hcount, h.right_count]
    omega
  · intro r hr
    exact (other_emit s (by decide : 1 < 5) (by decide : 4 < 5) hr).trans (h.other r hr)
  · rw [hcount, hleft]
    omega

private theorem active_indices {heapLimit i j : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s : State w}
    (h : InvariantAt heapLimit left right destination xs ys scratch entry i j s)
    (hactive : s.eval condition ≠ 0) : i < xs.length ∨ j < ys.length := by
  by_contra hn
  have hi : i = xs.length := Nat.le_antisymm h.left_le (Nat.le_of_not_gt (fun hi => hn (Or.inl hi)))
  have hj : j = ys.length := Nat.le_antisymm h.right_le (Nat.le_of_not_gt (fun hj => hn (Or.inr hj)))
  have hl : s.regs 3 = 0 := (Word.toNat_eq_zero_iff _).mp (by rw [h.left_count, hi, Nat.sub_self])
  have hr : s.regs 4 = 0 := (Word.toNat_eq_zero_iff _).mp (by rw [h.right_count, hj, Nat.sub_self])
  apply hactive
  simp [condition, State.eval, Expr.eval, BinOp.eval, hl, hr]

private theorem body_preserves {heapLimit i j : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (h : InvariantAt heapLimit left right destination xs ys scratch entry i j s)
    (hactive : s.eval condition ≠ 0) :
    Invariant heapLimit left right destination xs ys scratch entry (bodyResult s) ∧
      ((bodyResult s).regs 3).toNat + ((bodyResult s).regs 4).toNat <
        (s.regs 3).toNat + (s.regs 4).toNat := by
  by_cases hc : chooseLeft s
  · have hi : i < xs.length := by
      have hn : (s.regs 3).toNat ≠ 0 := fun hz => hc.1 ((Word.toNat_eq_zero_iff _).mp hz)
      rw [h.left_count] at hn
      omega
    have hchoose : ∀ hj : j < ys.length, unsignedLE xs[i] ys[j] := by
      intro hj
      have hloadLeft := h.left_array.1.lookup i hi
      have hloadRight := h.right_array.1.lookup j hj
      rcases hc.2 with hz | hle
      · have hzero : (s.regs 4).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hz
        rw [h.right_count] at hzero
        omega
      · rw [h.left_pointer, h.right_pointer, hloadLeft, hloadRight] at hle
        exact hle
    obtain ⟨hn, hv⟩ := emit_left_preserves hw hlen hdl hdr h hi hchoose
    rw [bodyResult, if_pos hc]
    exact ⟨⟨i + 1, j, hn⟩, hv⟩
  · have hj : j < ys.length := by
      rcases active_indices h hactive with hi | hj
      · by_contra hn
        have hzero : s.regs 4 = 0 := (Word.toNat_eq_zero_iff _).mp (by rw [h.right_count]; omega)
        have hnonzero : s.regs 3 ≠ 0 := by
          intro hz
          have hz' := (Word.toNat_eq_zero_iff _).mpr hz
          rw [h.left_count] at hz'
          omega
        exact hc ⟨hnonzero, Or.inl hzero⟩
      · exact hj
    have hchoose : ∀ hi : i < xs.length, ys[j].toNat < xs[i].toNat := by
      intro hi
      have hnonzero : s.regs 3 ≠ 0 := by
        intro hz
        have hz' := (Word.toNat_eq_zero_iff _).mpr hz
        rw [h.left_count] at hz'
        omega
      have hn : ¬ (s.mem (s.regs 0)).toNat ≤ (s.mem (s.regs 1)).toNat :=
        fun hle => hc ⟨hnonzero, Or.inr hle⟩
      rw [h.left_pointer, h.right_pointer, h.left_array.1.lookup i hi,
        h.right_array.1.lookup j hj] at hn
      exact Nat.lt_of_not_ge hn
    obtain ⟨hn, hv⟩ := emit_right_preserves hw hlen hdl hdr h hj hchoose
    rw [bodyResult, if_neg hc]
    exact ⟨⟨i, j + 1, hn⟩, hv⟩

private theorem invariant_start {heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry : State w}
    (hpre : Pre heapLimit left right destination xs ys scratch entry) :
    Invariant heapLimit left right destination xs ys scratch entry entry := by
  refine ⟨0, 0, ⟨Nat.zero_le _, Nat.zero_le _, hpre.left_array, hpre.right_array,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ArrayFrame.refl _ _ _, rfl, rfl, fun _ _ => rfl⟩⟩
  · simpa only [Nat.zero_add, List.take_zero, List.drop_zero, List.nil_append]
      using hpre.destination_array
  · simp
  · simpa only [arrayAddr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hpre.left_pointer
  · simpa only [arrayAddr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hpre.right_pointer
  · simpa only [Nat.zero_add, arrayAddr, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      using hpre.destination_pointer
  · simpa only [Nat.sub_zero] using hpre.left_count
  · simpa only [Nat.sub_zero] using hpre.right_count

private theorem body_safety {heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry s : State w}
    (hlen : scratch.length = xs.length + ys.length)
    (hs : Invariant heapLimit left right destination xs ys scratch entry s)
    (hz : s.eval condition ≠ 0) :
    (s.regs 3 ≠ 0 → (s.regs 0).toNat < heapLimit) ∧
    (s.regs 4 ≠ 0 → (s.regs 1).toNat < heapLimit) ∧
    (s.regs 2).toNat < heapLimit := by
  obtain ⟨i, j, h⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    have hi : i < xs.length := by
      have hp : (s.regs 3).toNat ≠ 0 := fun hp => hn ((Word.toNat_eq_zero_iff _).mp hp)
      rw [h.left_count] at hp
      omega
    rw [h.left_pointer]
    exact h.left_array.addr_lt hi
  · intro hn
    have hj : j < ys.length := by
      have hp : (s.regs 4).toNat ≠ 0 := fun hp => hn ((Word.toNat_eq_zero_iff _).mp hp)
      rw [h.right_count] at hp
      omega
    rw [h.right_pointer]
    exact h.right_array.addr_lt hj
  · have hk : i + j < (unsignedMerge xs ys).length := by
      have ha := active_indices h hz
      rw [length_unsignedMerge]
      have hi := h.left_le
      have hj := h.right_le
      omega
    have hlen' : scratch.length = (unsignedMerge xs ys).length := by
      rw [length_unsignedMerge]; exact hlen
    rw [h.destination_pointer]
    apply h.destination_array.addr_lt
    rw [copy_prefix_length (unsignedMerge xs ys) scratch hlen' (Nat.le_of_lt hk)]
    exact hk

private theorem iteration_total {heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)}
    (hw : 0 < w) (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length)
    (entry : State w) :
    TotalRelContract functions heapLimit depth body
      (fun s => Invariant heapLimit left right destination xs ys scratch entry s ∧
        s.eval condition ≠ 0)
      (fun s t => Invariant heapLimit left right destination xs ys scratch entry t ∧
        (t.regs 3).toNat + (t.regs 4).toNat < (s.regs 3).toNat + (s.regs 4).toNat) := by
  rintro s ⟨hs, hz⟩
  obtain ⟨hleft, hright, hdest⟩ := body_safety hlen hs hz
  apply Verification.TotalWP.of_contract (body_total_contract hw s hleft hright hdest hz) rfl
  intro t ht
  subst t
  obtain ⟨i, j, h⟩ := hs
  exact body_preserves hw hlen hdl hdr h hz

private theorem invariant_exit {heapLimit : Nat} {left right destination : Word w}
    {xs ys scratch : List (Word w)} {entry finish : State w}
    (hlen : scratch.length = xs.length + ys.length)
    (hf : Invariant heapLimit left right destination xs ys scratch entry finish)
    (hz : finish.eval condition = 0) :
    Post heapLimit left right destination xs ys entry finish := by
  obtain ⟨i, j, h⟩ := hf
  have hzero : finish.regs 3 = 0 ∧ finish.regs 4 = 0 := BitVec.or_eq_zero_iff.mp hz
  have hi : i = xs.length := by
    have hz : (finish.regs 3).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hzero.1
    rw [h.left_count] at hz
    have hi := h.left_le
    omega
  have hj : j = ys.length := by
    have hz : (finish.regs 4).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hzero.2
    rw [h.right_count] at hz
    have hj := h.right_le
    omega
  refine ⟨h.left_array, h.right_array, ?_, h.frame, ?_, ?_, ?_,
    hzero.1, hzero.2, h.input, h.output, h.other⟩
  · have ha := h.destination_array
    rw [hi, hj, ← length_unsignedMerge xs ys] at ha
    have hlen' : scratch.length = (unsignedMerge xs ys).length := by
      rw [length_unsignedMerge]; exact hlen
    simpa only [copy_prefix_finish (unsignedMerge xs ys) scratch hlen'] using ha
  · simpa only [hi] using h.left_pointer
  · simpa only [hj] using h.right_pointer
  · simpa only [hi, hj] using h.destination_pointer

/-- Merge terminates safely with the ordinary list result and frame facts.
The remaining input length is a termination variant, not a running-time bound. -/
theorem total_contract {heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length) :
    TotalRelContract functions heapLimit depth program
      (Pre heapLimit left right destination xs ys scratch)
      (Post heapLimit left right destination xs ys) := by
  intro entry hpre
  apply Verification.TotalWP.while_variant
    (Invariant heapLimit left right destination xs ys scratch entry)
    (fun s => (s.regs 3).toNat + (s.regs 4).toNat)
  · intro s hs
    trivial
  · intro s hs hz
    exact iteration_total hw hlen hdl hdr entry s ⟨hs, hz⟩
  · exact invariant_start hpre
  · intro finish hf hz
    exact invariant_exit hlen hf hz

/-- The separate time proof counts the generated guards, selected body
branches and back-edges of every completed merge execution. -/
theorem timeBound {control heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length) :
    TimeBound control functions heapLimit depth program
      (Pre heapLimit left right destination xs ys scratch)
      (fun _ => 34 * (xs.length + ys.length) + 4) := by
  intro entry hpre steps finish execution
  have hloop : TimeBound control functions heapLimit depth program
      (Invariant heapLimit left right destination xs ys scratch entry)
      (fun s => ((s.regs 3).toNat + (s.regs 4).toNat) * 34 + 4) := by
    apply TimeBound.while_linear
      (Invariant heapLimit left right destination xs ys scratch entry)
      (fun s => (s.regs 3).toNat + (s.regs 4).toNat) 29
    · exact iteration_total hw hlen hdl hdr entry
    · rintro s ⟨hs, hz⟩ count t hx
      obtain ⟨hleft, hright, hdest⟩ := body_safety hlen hs hz
      exact (body_contract hw s hleft hright hdest hz).timeBound s rfl count t hx
  have bound := hloop entry (invariant_start hpre) steps finish execution
  simpa only [hpre.left_count, hpre.right_count, Nat.mul_comm] using bound

/-- Merge arbitrary preloaded inputs into an independent allocated destination.
Sorted inputs consequently give a sorted permutation via `SortedPerm.merge`.
Every iteration costs at most 29 body instructions, four guard instructions,
and one back-edge. The final guard costs four. No natural sum is performed
in a word register, and no disjointness between the two sources is required. -/
theorem contract {control heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)} (hw : 0 < w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit left right destination xs ys scratch)
      (Post heapLimit left right destination xs ys)
      (fun _ => 34 * (xs.length + ys.length) + 4) :=
  (total_contract hw hlen hdl hdr).with_timeBound (timeBound hw hlen hdl hdr)

end Ram.Source.Array.Merge
