/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Computability.Ram.Verification.Time.StraightLine
import Complexity.Tactic.Ram.Total
import Init.Data.List.Nat.TakeDrop

/-!
# Copying a non-overlapping array with a fixed traversal

The program uses three source registers: source pointer, destination pointer,
and remaining length. Each iteration performs one ordinary load/store and
three register updates. Logical progress is the standard list expression
`xs.take i ++ ys.drop i`, not a second executable copying primitive.

The relational contract preserves the original source array and every word
outside the destination. It is a preloaded-heap block contract: it does not
claim to load an input list into memory for free, and overlapping intervals
are explicitly excluded.
-/

namespace Ram

theorem ArraysDisjoint.symm {base other : Word w} {len otherLen : Nat}
    (h : ArraysDisjoint base len other otherLen) :
    ArraysDisjoint other otherLen base len := Or.symm h

namespace Source.Array

/-- Updating the next position advances the standard list prefix/suffix view. -/
theorem copy_prefix_step (xs ys : List α) {i : Nat}
    (hlen : ys.length = xs.length) (hi : i < xs.length) :
    (xs.take i ++ ys.drop i).set i xs[i] =
      xs.take (i + 1) ++ ys.drop (i + 1) := by
  have htake : (xs.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  have hiy : i < ys.length := by simpa only [hlen] using hi
  rw [List.set_append_right i xs[i] (List.length_take_le i xs), htake,
    Nat.sub_self, List.drop_eq_getElem_cons hiy, List.set_cons_zero,
    List.take_succ_eq_append_getElem hi, List.append_assoc, List.singleton_append]

theorem copy_prefix_length (xs ys : List α) {i : Nat}
    (hlen : ys.length = xs.length) (hi : i ≤ xs.length) :
    (xs.take i ++ ys.drop i).length = xs.length := by
  rw [List.length_append, List.length_take_of_le hi, List.length_drop, hlen]
  exact Nat.add_sub_of_le hi

theorem copy_prefix_finish (xs ys : List α) (hlen : ys.length = xs.length) :
    xs.take xs.length ++ ys.drop xs.length = xs := by
  rw [List.take_length, ← hlen, List.drop_length, List.append_nil]

def copyCondition : Expr := .var 2

/-- One word is copied before either pointer advances. -/
def copyBody : Stmt :=
  .seq (.store (.var 1) (.load (.var 0)))
    (.seq (.assign 0 (.bin .add (.var 0) (.const 1)))
      (.seq (.assign 1 (.bin .add (.var 1) (.const 1)))
        (.assign 2 (.bin .sub (.var 2) (.const 1)))))

/-- One fixed source loop, independent of the length and contents. -/
def copy : Stmt := .while copyCondition copyBody

theorem copy_wellFormed {locals : Nat} (h : 3 ≤ locals) : copy.WellFormed locals := by
  have h0 : 0 < locals := Nat.lt_of_lt_of_le (by decide : 0 < 3) h
  have h1 : 1 < locals := Nat.lt_of_lt_of_le (by decide : 1 < 3) h
  have h2 : 2 < locals := Nat.lt_of_lt_of_le (by decide : 2 < 3) h
  simp [copy, copyCondition, copyBody, Stmt.WellFormed, Expr.Bounded, h0, h1, h2]

theorem copy_body_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable copyBody = 16 := rfl

theorem copy_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable copy = 19 := rfl

/-- Exact source-state effect of the emitted load/store and assignments. -/
def copyStep (s : State w) : State w :=
  (((s.setMem (s.regs 1) (s.mem (s.regs 0))).setReg 0 (s.regs 0 + 1)).setReg 1
    (s.regs 1 + 1)).setReg 2 (s.regs 2 - 1)

@[simp] theorem copyStep_source (s : State w) : (copyStep s).regs 0 = s.regs 0 + 1 := by
  simp [copyStep, State.setReg]

@[simp] theorem copyStep_destination (s : State w) : (copyStep s).regs 1 = s.regs 1 + 1 := by
  simp [copyStep, State.setReg]

@[simp] theorem copyStep_count (s : State w) : (copyStep s).regs 2 = s.regs 2 - 1 := by
  simp [copyStep, State.setReg]

@[simp] theorem copyStep_mem (s : State w) :
    (copyStep s).mem = (s.setMem (s.regs 1) (s.mem (s.regs 0))).mem := rfl

@[simp] theorem copyStep_input (s : State w) : (copyStep s).input = s.input := rfl
@[simp] theorem copyStep_output (s : State w) : (copyStep s).outputRev = s.outputRev := rfl

theorem copyStep_other (s : State w) {r : Reg} (hr : 3 ≤ r) :
    (copyStep s).regs r = s.regs r := by
  have h0 : r ≠ 0 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 3) hr))
  have h1 : r ≠ 1 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 3) hr))
  have h2 : r ≠ 2 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 3) hr))
  simp [copyStep, State.setReg, State.setMem, h0, h1, h2]

/-- The ordinary state effect and memory safety of one copy iteration,
without choosing an instruction budget. -/
theorem copy_body_total_contract {heapLimit depth : Nat} {program : Program}
    (s : State w) (hsource : (s.regs 0).toNat < heapLimit)
    (hdestination : (s.regs 1).toNat < heapLimit) :
    TotalContract program heapLimit depth copyBody (fun t => t = s)
      (fun t => t = copyStep s) := by
  ram_total_vc t ht [copyBody, copyStep, ht, hsource, hdestination]

/-- The body budget is the generated block's length. Its only safety
obligations are the two actual word addresses used by the load and store. -/
theorem copy_body_contract {control heapLimit depth : Nat} {program : Program}
    (s : State w) (hsource : (s.regs 0).toNat < heapLimit)
    (hdestination : (s.regs 1).toNat < heapLimit) :
    Contract control program heapLimit depth copyBody (fun t => t = s)
      (fun t => t = copyStep s) (fun _ => 16) := by
  exact (copy_body_total_contract s hsource hdestination).with_timeBound
    (TimeBound.of_isStraightLine (by simp [copyBody, Stmt.IsStraightLine]))

/-- Preloaded input arrays and the three runtime operands. Destination
contents are arbitrary but its allocated interval has the source length. -/
structure CopyPre (heapLimit : Nat) (source destination : Word w)
    (xs ys : List (Word w)) (s : State w) : Prop where
  source_array : ArrayAt heapLimit source xs s
  destination_array : ArrayAt heapLimit destination ys s
  source_pointer : s.regs 0 = source
  destination_pointer : s.regs 1 = destination
  count : (s.regs 2).toNat = xs.length

/-- The list in the result is the original source list. The whole source
interval, the array-external memory, and I/O are retained. End pointers are
word addresses; they may wrap only after the last element has been copied. -/
structure CopyPost (heapLimit : Nat) (source destination : Word w)
    (xs : List (Word w)) (entry finish : State w) : Prop where
  source_array : ArrayAt heapLimit source xs finish
  destination_array : ArrayAt heapLimit destination xs finish
  frame : ArrayFrame destination xs.length entry.mem finish.mem
  source_pointer : finish.regs 0 = arrayAddr source xs.length
  destination_pointer : finish.regs 1 = arrayAddr destination xs.length
  count : finish.regs 2 = 0
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ r, 3 ≤ r → finish.regs r = entry.regs r

private def copied (xs : List (Word w)) (s : State w) : Nat :=
  xs.length - (s.regs 2).toNat

private structure CopyInvariant (heapLimit : Nat) (source destination : Word w)
    (xs ys : List (Word w)) (entry s : State w) : Prop where
  remaining_le : (s.regs 2).toNat ≤ xs.length
  source_array : ArrayAt heapLimit source xs s
  destination_array : ArrayAt heapLimit destination
    (xs.take (copied xs s) ++ ys.drop (copied xs s)) s
  source_pointer : s.regs 0 = arrayAddr source (copied xs s)
  destination_pointer : s.regs 1 = arrayAddr destination (copied xs s)
  frame : ArrayFrame destination xs.length entry.mem s.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, 3 ≤ r → s.regs r = entry.regs r

private theorem copy_start {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {entry : State w}
    (hpre : CopyPre heapLimit source destination xs ys entry) :
    CopyInvariant heapLimit source destination xs ys entry entry := by
  have hz : copied xs entry = 0 := by simp [copied, hpre.count]
  refine ⟨Nat.le_of_eq hpre.count, hpre.source_array, ?_, ?_, ?_,
    ArrayFrame.refl _ _ _, rfl, rfl, fun _ _ => rfl⟩
  · simpa only [hz, List.take_zero, List.drop_zero, List.nil_append] using hpre.destination_array
  · simpa only [hz, arrayAddr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hpre.source_pointer
  · simpa only [hz, arrayAddr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hpre.destination_pointer

private theorem copy_index_lt {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {entry s : State w}
    (h : CopyInvariant heapLimit source destination xs ys entry s)
    (hz : s.eval copyCondition ≠ 0) : copied xs s < xs.length := by
  have hp : 0 < (s.regs 2).toNat := by
    have hne : (s.regs 2).toNat ≠ 0 := fun he => hz ((Word.toNat_eq_zero_iff _).mp he)
    omega
  have hle := h.remaining_le
  dsimp [copied]
  omega

private theorem copy_addresses {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {entry s : State w}
    (hlen : ys.length = xs.length)
    (h : CopyInvariant heapLimit source destination xs ys entry s)
    (hz : s.eval copyCondition ≠ 0) :
    (s.regs 0).toNat < heapLimit ∧ (s.regs 1).toNat < heapLimit := by
  have hi := copy_index_lt h hz
  have hlength := copy_prefix_length xs ys hlen (Nat.le_of_lt hi)
  constructor
  · rw [h.source_pointer]
    exact h.source_array.addr_lt hi
  · rw [h.destination_pointer]
    exact h.destination_array.addr_lt (by rw [hlength]; exact hi)

private theorem arrayAddr_succ (base : Word w) (i : Nat) :
    arrayAddr base (i + 1) = arrayAddr base i + 1 := by
  simp only [arrayAddr, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

private theorem copyStep_preserves {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (h : CopyInvariant heapLimit source destination xs ys entry s)
    (hz : s.eval copyCondition ≠ 0) :
    CopyInvariant heapLimit source destination xs ys entry (copyStep s) ∧
      ((copyStep s).regs 2).toNat < (s.regs 2).toNat := by
  let i := copied xs s
  have hi : i < xs.length := copy_index_lt h hz
  have hip : i ≤ xs.length := Nat.le_of_lt hi
  have hlength := copy_prefix_length xs ys hlen hip
  have hstoreIndex : i < (xs.take i ++ ys.drop i).length := by rw [hlength]; exact hi
  have hload : s.mem (s.regs 0) = xs[i] := by
    rw [h.source_pointer]
    exact h.source_array.1.lookup i hi
  let stored := s.setMem (arrayAddr destination i) xs[i]
  have hmem : (copyStep s).mem = stored.mem := by
    rw [copyStep_mem, h.destination_pointer, hload]
  have hframe : ArrayFrame destination xs.length s.mem (copyStep s).mem := by
    rw [hmem]
    have hf : ArrayFrame destination (xs.take i ++ ys.drop i).length s.mem stored.mem :=
      ArrayFrame.store h.destination_array.1 hstoreIndex xs[i]
    rw [hlength] at hf
    exact hf
  have hsource : ArrayAt heapLimit source xs (copyStep s) :=
    h.source_array.frame hframe hdisjoint.symm
  have hdestination : ArrayAt heapLimit destination
      (xs.take (i + 1) ++ ys.drop (i + 1)) (copyStep s) := by
    have hs := h.destination_array.setMem hstoreIndex xs[i]
    rw [copy_prefix_step xs ys hlen hi] at hs
    change ArrayRep (copyStep s).mem destination _ ∧ _
    rw [hmem]
    exact hs
  have hp : 0 < (s.regs 2).toNat := by
    have hne : (s.regs 2).toNat ≠ 0 := fun he => hz ((Word.toNat_eq_zero_iff _).mp he)
    omega
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hcount : ((copyStep s).regs 2).toNat = (s.regs 2).toNat - 1 := by
    rw [copyStep_count]
    change (BinOp.eval .sub (s.regs 2) 1).toNat = _
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hone]; omega), hone]
  have hnext : copied xs (copyStep s) = i + 1 := by
    have hle := h.remaining_le
    dsimp [copied, i]
    rw [hcount]
    omega
  refine ⟨⟨?_, hsource, ?_, ?_, ?_, h.frame.trans hframe,
    h.input, h.output, ?_⟩, ?_⟩
  · rw [hcount]
    exact Nat.le_trans (Nat.sub_le _ _) h.remaining_le
  · rw [hnext]
    exact hdestination
  · rw [copyStep_source, h.source_pointer, hnext, arrayAddr_succ]
  · rw [copyStep_destination, h.destination_pointer, hnext, arrayAddr_succ]
  · intro r hr
    exact (copyStep_other s hr).trans (h.other r hr)
  · rw [hcount]
    omega

private theorem copy_iteration_total_contract {heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (entry : State w) :
    TotalRelContract program heapLimit depth copyBody
      (fun s => CopyInvariant heapLimit source destination xs ys entry s ∧
        s.eval copyCondition ≠ 0)
      (fun s t => CopyInvariant heapLimit source destination xs ys entry t ∧
        (t.regs 2).toNat < (s.regs 2).toNat) := by
  intro s ⟨hs, hz⟩
  have addresses := copy_addresses hlen hs hz
  obtain ⟨t, execution, ht⟩ :=
    copy_body_total_contract s addresses.1 addresses.2 s rfl
  subst t
  exact ⟨copyStep s, execution, copyStep_preserves hw hlen hdisjoint hs hz⟩

private theorem copy_finish {heapLimit : Nat} {source destination : Word w}
    {xs ys : List (Word w)} {entry t : State w}
    (hlen : ys.length = xs.length)
    (h : CopyInvariant heapLimit source destination xs ys entry t)
    (hz : t.eval copyCondition = 0) :
    CopyPost heapLimit source destination xs entry t := by
  have hzero : t.regs 2 = 0 := hz
  have hindex : copied xs t = xs.length := by simp [copied, hzero]
  refine ⟨h.source_array, ?_, h.frame, ?_, ?_, hzero, h.input, h.output, h.other⟩
  · simpa only [hindex, copy_prefix_finish xs ys hlen] using h.destination_array
  · simpa only [hindex] using h.source_pointer
  · simpa only [hindex] using h.destination_pointer

/-- Copying is safe and terminates with the original list at the destination.
The remaining length is only a termination variant, not a time budget. -/
theorem copy_total_contract {heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length) :
    TotalRelContract program heapLimit depth copy
      (CopyPre heapLimit source destination xs ys)
      (CopyPost heapLimit source destination xs) := by
  intro entry hpre
  apply Verification.TotalWP.while_variant
    (CopyInvariant heapLimit source destination xs ys entry) (fun s => (s.regs 2).toNat)
  · intro s hs
    trivial
  · intro s hs hz
    exact copy_iteration_total_contract hw hlen hdisjoint entry s ⟨hs, hz⟩
  · exact copy_start hpre
  · intro t ht hz
    exact copy_finish hlen ht hz

/-- A separate bound on measured copy executions. The body contributes
sixteen generated instructions, with three loop instructions per iteration
and the final two-instruction guard. -/
theorem copy_timeBound {control heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length) :
    TimeBound control program heapLimit depth copy
      (CopyPre heapLimit source destination xs ys) (fun _ => 19 * xs.length + 2) := by
  intro entry hpre steps finish execution
  have hloop : TimeBound control program heapLimit depth copy
      (CopyInvariant heapLimit source destination xs ys entry)
      (fun s => (s.regs 2).toNat * 19 + 2) := by
    apply TimeBound.while_linear (CopyInvariant heapLimit source destination xs ys entry)
      (fun s => (s.regs 2).toNat) 16
    · exact copy_iteration_total_contract hw hlen hdisjoint entry
    · exact TimeBound.of_isStraightLine (by simp [copyBody, Stmt.IsStraightLine])
  have bound := hloop entry (copy_start hpre) steps finish execution
  simpa only [hpre.count, Nat.mul_comm] using bound

/-- A reusable non-overlapping array-copy contract. The linear budget comes
from sixteen body instructions, two guard instructions, one back-edge per
iteration, and the final two-instruction guard. Array bounds prevent every
access from wrapping; the final unused pointer may be the modular endpoint. -/
theorem copy_contract {control heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length) :
    RelContract control program heapLimit depth copy
      (CopyPre heapLimit source destination xs ys)
      (CopyPost heapLimit source destination xs) (fun _ => 19 * xs.length + 2) := by
  exact (copy_total_contract hw hlen hdisjoint).with_timeBound
    (copy_timeBound hw hlen hdisjoint)

end Source.Array
end Ram
