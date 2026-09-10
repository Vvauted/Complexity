/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Arena.Basic
import Complexity.Computability.Ram.Array.Fold

/-!
# Allocation at the configured local registers

One initialized-prefix proof covers both standalone and inline allocation.
The eleven-instruction filling body reuses the existing countdown counting
theorem. Reservation and setup execute twelve instructions, so every successful
allocation executes exactly `14 * length + 14` body instructions, including
zero-length allocation. Calls and their ABI costs are separate.
-/

namespace Ram.Source.Arena.Registers

/-- State produced by reservation and traversal setup, not an evaluator. -/
def prepared (r : Registers) (s : State w) : State w :=
  (((s.setReg r.base (s.mem 0)).setMem 0 (s.mem 0 + s.regs r.length)).setReg r.pointer
    (s.mem 0)).setReg r.remaining (s.regs r.length)

/-- State produced by one initialization store and cursor update. -/
def fillStep (r : Registers) (s : State w) : State w :=
  ((s.setMem (s.regs r.pointer) (s.regs r.value)).setReg r.pointer
    (s.regs r.pointer + 1)).setReg r.remaining (s.regs r.remaining - 1)

theorem prepared_base (r : Registers) (s : State w) :
    (r.prepared s).regs r.base = s.mem 0 := by
  simp [prepared, State.setReg, r.base_ne_pointer, r.base_ne_remaining]

theorem prepared_length (r : Registers) (s : State w) :
    (r.prepared s).regs r.length = s.regs r.length := by
  simp [prepared, State.setReg, r.length_ne_remaining, r.length_ne_pointer,
    Ne.symm r.base_ne_length]

theorem prepared_value (r : Registers) (s : State w) :
    (r.prepared s).regs r.value = s.regs r.value := by
  simp [prepared, State.setReg, r.value_ne_remaining, r.value_ne_pointer,
    Ne.symm r.base_ne_value]

theorem prepared_pointer (r : Registers) (s : State w) :
    (r.prepared s).regs r.pointer = s.mem 0 := by
  simp [prepared, State.setReg, r.pointer_ne_remaining]

theorem prepared_remaining (r : Registers) (s : State w) :
    (r.prepared s).regs r.remaining = s.regs r.length := by
  simp [prepared, State.setReg]

theorem fillStep_pointer (r : Registers) (s : State w) :
    (r.fillStep s).regs r.pointer = s.regs r.pointer + 1 := by
  simp [fillStep, State.setReg, r.pointer_ne_remaining]

theorem fillStep_remaining (r : Registers) (s : State w) :
    (r.fillStep s).regs r.remaining = s.regs r.remaining - 1 := by
  simp [fillStep, State.setReg]

theorem fillStep_value (r : Registers) (s : State w) :
    (r.fillStep s).regs r.value = s.regs r.value := by
  simp [fillStep, State.setReg, r.value_ne_remaining, r.value_ne_pointer]

theorem prepare_safe (r : Registers) {program : Program} {heapLimit depth : Nat}
    (s : State w) (positive : 0 < heapLimit) :
    SafeExec program heapLimit depth r.prepare s (r.prepared s) := by
  have execution := SafeExec.seq
    (SafeExec.assign (program := program) (heapLimit := heapLimit) (d := depth)
      (s := s) (dst := r.base) (value := .load (.const 0)) ⟨trivial, by simpa using positive⟩)
    (SafeExec.seq
      (SafeExec.store (address := .const 0) (value := .bin .add (.var r.base) (.var r.length))
        trivial ⟨trivial, trivial⟩ (by simpa using positive))
      (SafeExec.seq (SafeExec.assign (dst := r.pointer) (value := .var r.base) trivial)
        (SafeExec.assign (dst := r.remaining) (value := .var r.length) trivial)))
  simpa [prepare, prepared, State.eval, Expr.eval, BinOp.eval, State.setReg,
    State.setMem, Ne.symm r.base_ne_length, r.length_ne_pointer] using execution

theorem prepare_localMeasured (r : Registers) {program : Program}
    {control heapLimit depth : Nat} (s : State w) (positive : 0 < heapLimit) :
    LocalMeasuredExec control program heapLimit depth r.prepare 12 s (r.prepared s) := by
  obtain ⟨steps, execution⟩ :=
    (r.prepare_safe (program := program) (depth := depth) s positive).exists_localMeasured control
  have count := execution.steps_eq_stmtSize r.prepare_isStraightLine
  rw [prepare_code_size] at count
  simpa only [count] using execution

theorem fillBody_safe (r : Registers) {program : Program} {heapLimit depth : Nat}
    (s : State w) (address : (s.regs r.pointer).toNat < heapLimit) :
    SafeExec program heapLimit depth r.fillBody s (r.fillStep s) := by
  have execution := SafeExec.seq
    (SafeExec.store (program := program) (heapLimit := heapLimit) (d := depth)
      (s := s) (address := .var r.pointer) (value := .var r.value) trivial trivial address)
    (SafeExec.seq
      (SafeExec.assign (dst := r.pointer)
        (value := .bin .add (.var r.pointer) (.const 1)) ⟨trivial, trivial⟩)
      (SafeExec.assign (dst := r.remaining)
        (value := .bin .sub (.var r.remaining) (.const 1)) ⟨trivial, trivial⟩))
  simpa [fillBody, fillStep, State.eval, Expr.eval, BinOp.eval, State.setReg,
    State.setMem, Ne.symm r.pointer_ne_remaining] using execution

theorem fillBody_result (r : Registers) {program : Program} {heapLimit depth : Nat}
    {s t : State w} (execution : SafeExec program heapLimit depth r.fillBody s t) :
    t = r.fillStep s := by
  cases execution with
  | seq store rest =>
    cases store with
    | store _ _ _ =>
      cases rest with
      | seq first second =>
        cases first with
        | assign _ =>
          cases second with
          | assign _ =>
            simp [fillStep, State.eval, Expr.eval, BinOp.eval, State.setReg, State.setMem,
              Ne.symm r.pointer_ne_remaining]

theorem fillBody_localMeasured (r : Registers) {program : Program}
    {control heapLimit depth : Nat} {s t : State w}
    (safe : SafeExec program heapLimit depth r.fillBody s t) :
    LocalMeasuredExec control program heapLimit depth r.fillBody 11 s t := by
  obtain ⟨steps, execution⟩ := safe.exists_localMeasured control
  have count := execution.steps_eq_stmtSize r.fillBody_isStraightLine
  rw [fillBody_code_size] at count
  simpa only [count] using execution

private def fillRegisters (r : Registers) : Array.Fold.Registers where
  pointer := r.pointer
  remaining := r.remaining
  accumulator := r.value
  pointer_ne_remaining := r.pointer_ne_remaining
  pointer_ne_accumulator := Ne.symm r.value_ne_pointer
  remaining_ne_accumulator := Ne.symm r.value_ne_remaining

/-- The existing countdown theorem counts the actual guard and backedge. -/
theorem fill_localMeasured (r : Registers) {program : Program}
    {control heapLimit depth : Nat} (hw : 0 < w) {s t : State w}
    (safe : SafeExec program heapLimit depth r.fill s t) :
    LocalMeasuredExec control program heapLimit depth r.fill
      (14 * (s.regs r.remaining).toNat + 2) s t := by
  apply Array.Fold.loop_localMeasured_of_body r.fillRegisters hw
    (body := r.fillBody) (bodySteps := 11) ?_ r.fillBody_localMeasured safe
  intro s t execution
  rw [r.fillBody_result execution]
  exact r.fillStep_remaining s

private def filled (r : Registers) (length : Nat) (s : State w) : Nat :=
  length - (s.regs r.remaining).toNat

private structure FillInvariant (r : Registers) (base value : Word w) (length : Nat)
    (entry s : State w) : Prop where
  remaining_le : (s.regs r.remaining).toNat ≤ length
  pointer : s.regs r.pointer = arrayAddr base (r.filled length s)
  value_reg : s.regs r.value = value
  initializedPrefix : InitializedPrefix entry.mem s.mem base value (r.filled length s)
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

private theorem fillStep_preserves (r : Registers) {heapLimit length : Nat}
    {base value : Word w} {entry s : State w} (hw : 0 < w)
    (capacity : base.toNat + length ≤ heapLimit) (fits : heapLimit < 2 ^ w)
    (invariant : r.FillInvariant base value length entry s) (active : s.regs r.remaining ≠ 0) :
    (s.regs r.pointer).toNat < heapLimit ∧
      r.FillInvariant base value length entry (r.fillStep s) ∧
      ((r.fillStep s).regs r.remaining).toNat < (s.regs r.remaining).toNat := by
  have positive : 0 < (s.regs r.remaining).toNat :=
    Nat.pos_of_ne_zero (fun zero => active ((Word.toNat_eq_zero_iff _).mp zero))
  have index_lt : r.filled length s < length := by
    have bound := invariant.remaining_le
    unfold filled
    omega
  have address_fit : base.toNat + r.filled length s < 2 ^ w := by omega
  have count : ((r.fillStep s).regs r.remaining).toNat = (s.regs r.remaining).toNat - 1 := by
    rw [r.fillStep_remaining]
    have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
    change (BinOp.eval .sub (s.regs r.remaining) 1).toNat = _
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [one]; omega), one]
  have next : r.filled length (r.fillStep s) = r.filled length s + 1 := by
    have bound := invariant.remaining_le
    simp only [filled, count]
    omega
  have memory : (r.fillStep s).mem =
      (fun address => if address = arrayAddr base (r.filled length s)
        then value else s.mem address) := by
    simp only [fillStep, State.setReg, State.setMem, invariant.pointer, invariant.value_reg]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, invariant.input, invariant.output⟩, ?_⟩
  · rw [invariant.pointer, arrayAddr_toNat address_fit]
    omega
  · rw [count]
    exact Nat.le_trans (Nat.sub_le _ _) invariant.remaining_le
  · rw [next, r.fillStep_pointer, invariant.pointer]
    simp only [arrayAddr, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · exact (r.fillStep_value s).trans invariant.value_reg
  · rw [next, memory]
    exact invariant.initializedPrefix.store address_fit
  · rw [count]
    omega

/-- The pending interval needs no fictitious array representation before filling. -/
theorem fill_safe (r : Registers) {program : Program} {heapLimit depth length : Nat}
    {base value : Word w} (hw : 0 < w) (entry : State w)
    (pointer : entry.regs r.pointer = base) (count : (entry.regs r.remaining).toNat = length)
    (initial : entry.regs r.value = value)
    (capacity : base.toNat + length ≤ heapLimit) (fits : heapLimit < 2 ^ w) :
    ∃ finish, SafeExec program heapLimit depth r.fill entry finish ∧
      InitializedPrefix entry.mem finish.mem base value length ∧
      finish.regs r.remaining = 0 ∧ finish.input = entry.input ∧
      finish.outputRev = entry.outputRev := by
  apply Verification.TotalWP.while_variant
    (r.FillInvariant base value length entry) (fun s => (s.regs r.remaining).toNat)
  · intro s _
    trivial
  · intro s invariant active
    have step := r.fillStep_preserves hw capacity fits invariant active
    exact ⟨r.fillStep s, r.fillBody_safe s step.1, step.2⟩
  · refine ⟨Nat.le_of_eq count, ?_, initial, ?_, rfl, rfl⟩
    · simpa [filled, count, arrayAddr] using pointer
    · simpa [filled, count] using InitializedPrefix.empty entry.mem base value
  · intro finish invariant zero
    have zero' : finish.regs r.remaining = 0 := zero
    have done : r.filled length finish = length := by simp [filled, zero']
    exact ⟨by simpa only [done] using invariant.initializedPrefix, zero',
      invariant.input, invariant.output⟩

/-- Runtime capacity and exact input words, at the chosen static layout. -/
structure Pre (r : Registers) (heapLimit : Nat) (base : Word w) (length : Nat)
    (value : Word w) (entry : State w) : Prop where
  cursor : entry.mem 0 = base
  length_reg : (entry.regs r.length).toNat = length
  value_reg : entry.regs r.value = value
  positive : 1 ≤ base.toNat
  capacity : base.toNat + length ≤ heapLimit
  fits : heapLimit < 2 ^ w

/-- All local slots other than the three actual destinations are preserved. -/
structure Post (r : Registers) (heapLimit : Nat) (base : Word w) (length : Nat)
    (value : Word w) (entry finish : State w) : Prop where
  cursor : finish.mem 0 = arrayAddr base length
  array : ArrayAt heapLimit base (List.replicate length value) finish
  base_reg : finish.regs r.base = base
  length_reg : finish.regs r.length = entry.regs r.length
  frame : ∀ address, address ≠ 0 →
    address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
    finish.mem address = entry.mem address
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ slot, slot ≠ r.base → slot ≠ r.pointer → slot ≠ r.remaining →
    finish.regs slot = entry.regs slot

/-- Uniform exact execution proof for every allocator layout, not a required
per-program adapter. Its capacity assumptions are ordinary runtime preconditions. -/
theorem allocate_measured (r : Registers) {program : Program}
    {control heapLimit depth length : Nat} {base value : Word w} {entry : State w}
    (pre : r.Pre heapLimit base length value entry) :
    ∃ finish, LocalMeasuredExec control program heapLimit depth r.allocate
      (14 * length + 14) entry finish ∧ r.Post heapLimit base length value entry finish := by
  have heapPositive : 0 < heapLimit := by have := pre.positive; have := pre.capacity; omega
  have hw : 0 < w := by
    by_contra zero
    have : w = 0 := by omega
    subst w
    have := pre.fits
    simp only [Nat.pow_zero] at this
    omega
  have pointer : (r.prepared entry).regs r.pointer = base :=
    (r.prepared_pointer entry).trans pre.cursor
  have count : ((r.prepared entry).regs r.remaining).toNat = length := by
    rw [r.prepared_remaining]
    exact pre.length_reg
  have initial : (r.prepared entry).regs r.value = value :=
    (r.prepared_value entry).trans pre.value_reg
  obtain ⟨finish, safe, initializedPrefix, _, input, output⟩ :=
    r.fill_safe (program := program) (depth := depth) hw (r.prepared entry)
      pointer count initial pre.capacity pre.fits
  have execution := LocalMeasuredExec.seq
    (r.prepare_localMeasured (program := program) (control := control) (depth := depth)
      entry heapPositive)
    (r.fill_localMeasured (control := control) hw safe)
  have resultBase : finish.regs r.base = base := by
    rw [safe.regs_eq_of_not_mem_writtenRegs (r := r.base)
      (by simp [fill, fillBody, Stmt.writtenRegs, r.base_ne_pointer, r.base_ne_remaining])]
    exact (r.prepared_base entry).trans pre.cursor
  have resultLength : finish.regs r.length = entry.regs r.length := by
    rw [safe.regs_eq_of_not_mem_writtenRegs (r := r.length)
      (by simp [fill, fillBody, Stmt.writtenRegs, r.length_ne_pointer, r.length_ne_remaining])]
    exact r.prepared_length entry
  have endpoint : entry.mem 0 + entry.regs r.length = arrayAddr base length := by
    rw [pre.cursor, arrayAddr, ← pre.length_reg, Word.ofNat_toNat_self]
  refine ⟨finish, ?_, ⟨?_, ?_, resultBase, resultLength, ?_, input, output, ?_⟩⟩
  · simpa only [allocate, count, Nat.add_comm 12, Nat.add_assoc] using execution
  · rw [initializedPrefix.frame 0 (Or.inl (by change 0 < base.toNat; have := pre.positive; omega))]
    simpa [prepared, State.setReg, State.setMem] using endpoint
  · exact ⟨initializedPrefix.initialized, by simpa using pre.capacity⟩
  · intro address nonzero outside
    rw [initializedPrefix.frame address outside]
    change (if address = 0 then entry.mem 0 + entry.regs r.length else entry.mem address) =
      entry.mem address
    exact if_neg nonzero
  · intro slot notBase notPointer notRemaining
    apply execution.erase.regs_eq_of_not_mem_writtenRegs
    change slot ∉ r.allocate.writtenRegs
    rw [r.allocate_writtenRegs]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨notBase, notPointer, notRemaining⟩

/-- Terminating allocation without choosing a time budget. -/
theorem allocate_total (r : Registers) {program : Program} {heapLimit depth length : Nat}
    {base value : Word w} :
    TotalRelContract program heapLimit depth r.allocate
      (r.Pre heapLimit base length value) (r.Post heapLimit base length value) := by
  intro entry pre
  obtain ⟨finish, execution, post⟩ :=
    r.allocate_measured (program := program) (control := 0) (depth := depth) pre
  exact ⟨finish, execution.erase, post⟩

end Ram.Source.Arena.Registers
