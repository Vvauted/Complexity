/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Basic
import Complexity.Computability.Ram.Compiler.ABI.Basic
import Complexity.Computability.Ram.Memory.Basic

/-!
# Word-by-word caller-frame preservation

The proofs in this module concern the concrete save/restore instruction lists
from `Ram.ABI`. A saved frame is an assertion about individual memory words,
not a new machine operation. Stack addresses use ordinary word addition; the
save theorem states the no-wrap condition needed to keep distinct slots apart.
-/

namespace Ram.ABI

/-- The first `k` saved locals, independently of the rest of target memory. -/
def FrameSaved (k : Nat) (base : Word w) (saved : Reg → Word w)
    (mem : Word w → Word w) : Prop :=
  ∀ i, i < k → mem (arrayAddr base (i + 1)) = saved i

private theorem local_ne_addr {n i : Nat} (hi : i < n) : i ≠ addr n := by
  unfold addr
  omega

private theorem local_ne_tmp {n i : Nat} (hi : i < n) : i ≠ tmp n := by
  unfold tmp
  omega

@[simp] theorem slotAddress_regs (n i : Nat) (s : State w) (r : Reg) :
    (execBlock (slotAddress n i) s).regs r =
      if r = addr n then arrayAddr (s.regs (sp n)) (i + 1)
      else if r = tmp n then BitVec.ofNat w (i + 1) else s.regs r := by
  simp [slotAddress, execBlock, execInstr, State.setReg, State.next,
    BinOp.eval, arrayAddr, sp, addr, tmp]

@[simp] theorem slotAddress_mem (n i : Nat) (s : State w) :
    (execBlock (slotAddress n i) s).mem = s.mem := rfl

theorem saveLocal_effect {n i : Nat} (s : State w) (hi : i < n) :
    execBlock (saveLocal n i) s =
      ((execBlock (slotAddress n i) s).setMem
        (arrayAddr (s.regs (sp n)) (i + 1)) (s.regs i)).next := by
  simp only [saveLocal, execBlock_append, execBlock_cons, execBlock_nil, execInstr]
  simp [slotAddress_regs, local_ne_addr hi, local_ne_tmp hi]

theorem restoreLocal_effect (n i : Nat) (s : State w) :
    execBlock (restoreLocal n i) s =
      ((execBlock (slotAddress n i) s).setReg i
        (s.mem (arrayAddr (s.regs (sp n)) (i + 1)))).next := by
  simp [restoreLocal, execBlock_append, execInstr, slotAddress_regs]

theorem saveLocal_regs (n i : Nat) (s : State w) (r : Reg)
    (ha : r ≠ addr n) (ht : r ≠ tmp n) :
    (execBlock (saveLocal n i) s).regs r = s.regs r := by
  simp [saveLocal, execBlock_append, execInstr, slotAddress_regs, ha, ht]

@[simp] theorem saveLocal_sp (n i : Nat) (s : State w) :
    (execBlock (saveLocal n i) s).regs (sp n) = s.regs (sp n) := by
  exact saveLocal_regs n i s (sp n) (by simp [sp, addr]) (by simp [sp, tmp])

theorem saveLocal_mem {n i : Nat} (s : State w) (hi : i < n) (a : Word w) :
    (execBlock (saveLocal n i) s).mem a =
      if a = arrayAddr (s.regs (sp n)) (i + 1) then s.regs i else s.mem a := by
  rw [saveLocal_effect s hi]
  rfl

@[simp] theorem restoreLocal_mem (n i : Nat) (s : State w) :
    (execBlock (restoreLocal n i) s).mem = s.mem := rfl

@[simp] theorem restoreLocal_same (n i : Nat) (s : State w) :
    (execBlock (restoreLocal n i) s).regs i =
      s.mem (arrayAddr (s.regs (sp n)) (i + 1)) := by
  rw [restoreLocal_effect]
  simp

theorem restoreLocal_regs (n i : Nat) (s : State w) (r : Reg)
    (ha : r ≠ addr n) (ht : r ≠ tmp n) (hi : r ≠ i) :
    (execBlock (restoreLocal n i) s).regs r = s.regs r := by
  rw [restoreLocal_effect]
  simp [slotAddress_regs, ha, ht, hi]

theorem restoreLocal_sp {n i : Nat} (s : State w) (hi : i < n) :
    (execBlock (restoreLocal n i) s).regs (sp n) = s.regs (sp n) := by
  exact restoreLocal_regs n i s (sp n) (by simp [sp, addr])
    (by simp [sp, tmp]) (by exact Nat.ne_of_gt hi)

theorem slotAddress_linear (n i : Nat) : ∀ instr ∈ slotAddress n i, instr.Linear := by
  simp [slotAddress, Instr.Linear]

theorem saveLocal_linear (n i : Nat) : ∀ instr ∈ saveLocal n i, instr.Linear := by
  simp [saveLocal, slotAddress, Instr.Linear]

theorem restoreLocal_linear (n i : Nat) : ∀ instr ∈ restoreLocal n i, instr.Linear := by
  simp [restoreLocal, slotAddress, Instr.Linear]

theorem saveLocals_linear (n k : Nat) : ∀ instr ∈ saveLocals n k, instr.Linear := by
  induction k with
  | zero => simp [saveLocals]
  | succ k ih =>
      intro instr hi
      simp only [saveLocals, List.mem_append] at hi
      exact hi.elim (ih instr) (saveLocal_linear n k instr)

theorem restoreLocals_linear (n k : Nat) : ∀ instr ∈ restoreLocals n k, instr.Linear := by
  induction k with
  | zero => simp [restoreLocals]
  | succ k ih =>
      intro instr hi
      simp only [restoreLocals, List.mem_append] at hi
      exact hi.elim (ih instr) (restoreLocal_linear n k instr)

/-- Saving locals changes only the two address-calculation registers. -/
theorem saveLocals_regs (n k : Nat) (s : State w) (r : Reg)
    (ha : r ≠ addr n) (ht : r ≠ tmp n) :
    (execBlock (saveLocals n k) s).regs r = s.regs r := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [saveLocals, execBlock_append, saveLocal_regs n k _ r ha ht, ih]

@[simp] theorem saveLocals_sp (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).regs (sp n) = s.regs (sp n) :=
  saveLocals_regs n k s (sp n) (by simp [sp, addr]) (by simp [sp, tmp])

@[simp] theorem saveLocals_rv (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).regs (rv n) = s.regs (rv n) :=
  saveLocals_regs n k s (rv n) (by simp [rv, addr]) (by simp [rv, tmp])

@[simp] theorem saveLocals_ra (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).regs (ra n) = s.regs (ra n) :=
  saveLocals_regs n k s (ra n) (by simp [ra, addr]) (by simp [ra, tmp])

@[simp] theorem saveLocals_arg (n k j : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).regs (arg n j) = s.regs (arg n j) := by
  apply saveLocals_regs
  · exact Nat.ne_of_gt (by unfold arg addr; omega)
  · exact Nat.ne_of_gt (by unfold arg tmp; omega)

/-- A destination outside the saved slots is unchanged. This statement uses
the actual word addresses and therefore does not itself need a no-wrap bound. -/
theorem saveLocals_mem_of_not_slot {n k : Nat} (s : State w) (hk : k ≤ n)
    (a : Word w) (hout : ∀ i, i < k → a ≠ arrayAddr (s.regs (sp n)) (i + 1)) :
    (execBlock (saveLocals n k) s).mem a = s.mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [saveLocals, execBlock_append, saveLocal_mem _ hkn, saveLocals_sp,
        if_neg (hout k (Nat.lt_succ_self k))]
      exact ih (Nat.le_of_lt hkn) (fun i hi => hout i (Nat.lt_trans hi (Nat.lt_succ_self k)))

/-- Every original caller local is saved in its distinct, non-wrapping slot. -/
theorem saveLocals_frame {n k : Nat} (s : State w) (hk : k ≤ n)
    (hfit : (s.regs (sp n)).toNat + k < 2 ^ w) :
    FrameSaved k (s.regs (sp n)) s.regs (execBlock (saveLocals n k) s).mem := by
  induction k with
  | zero =>
      intro i hi
      omega
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hfit' : (s.regs (sp n)).toNat + k < 2 ^ w := by omega
      have hsaved := ih (Nat.le_of_lt hkn) hfit'
      intro i hi
      rw [saveLocals, execBlock_append, saveLocal_mem _ hkn, saveLocals_sp]
      by_cases hik : i = k
      · subst i
        simp only [ite_true]
        exact saveLocals_regs n k s k (local_ne_addr hkn) (local_ne_tmp hkn)
      · have hik' : i < k := by omega
        have haddr : arrayAddr (s.regs (sp n)) (i + 1) ≠
            arrayAddr (s.regs (sp n)) (k + 1) := by
          intro he
          have hoff := (arrayAddr_eq_iff (by omega) hfit).mp he
          omega
        rw [if_neg haddr]
        exact hsaved i hik'

/-- Outside the local-slot interval, saving preserves memory, including the
return-address word at `SP` and every older stack or heap word below it. -/
theorem saveLocals_mem_outside {n k : Nat} (s : State w) (hk : k ≤ n)
    (hfit : (s.regs (sp n)).toNat + k < 2 ^ w) (a : Word w)
    (hout : a.toNat ≤ (s.regs (sp n)).toNat ∨
      (s.regs (sp n)).toNat + k < a.toNat) :
    (execBlock (saveLocals n k) s).mem a = s.mem a := by
  apply saveLocals_mem_of_not_slot s hk a
  intro i hi he
  have hn := congrArg (fun x : Word w => x.toNat) he
  change a.toNat = (arrayAddr (s.regs (sp n)) (i + 1)).toNat at hn
  rw [arrayAddr_toNat (by omega)] at hn
  omega

theorem saveLocals_heap {n k limit : Nat} {mem : Word w → Word w}
    (s : State w) (hk : k ≤ n) (hfit : (s.regs (sp n)).toNat + k < 2 ^ w)
    (hbase : limit ≤ (s.regs (sp n)).toNat) (hheap : HeapEqBelow limit mem s.mem) :
    HeapEqBelow limit mem (execBlock (saveLocals n k) s).mem := by
  intro a ha
  rw [saveLocals_mem_outside s hk hfit a (Or.inl (by omega))]
  exact hheap a ha

/-- Registers not restored, apart from the two address temporaries, survive. -/
theorem restoreLocals_regs (n k : Nat) (s : State w) (r : Reg)
    (hkr : k ≤ r) (ha : r ≠ addr n) (ht : r ≠ tmp n) :
    (execBlock (restoreLocals n k) s).regs r = s.regs r := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [restoreLocals, execBlock_append,
        restoreLocal_regs n k _ r ha ht (Nat.ne_of_gt (by omega))]
      exact ih (by omega)

theorem restoreLocals_sp {n k : Nat} (s : State w) (hk : k ≤ n) :
    (execBlock (restoreLocals n k) s).regs (sp n) = s.regs (sp n) :=
  restoreLocals_regs n k s (sp n) hk (by simp [sp, addr]) (by simp [sp, tmp])

theorem restoreLocals_rv {n k : Nat} (s : State w) (hk : k ≤ n) :
    (execBlock (restoreLocals n k) s).regs (rv n) = s.regs (rv n) := by
  exact restoreLocals_regs n k s (rv n) (by unfold rv; omega)
    (by simp [rv, addr]) (by simp [rv, tmp])

theorem restoreLocals_ra {n k : Nat} (s : State w) (hk : k ≤ n) :
    (execBlock (restoreLocals n k) s).regs (ra n) = s.regs (ra n) := by
  exact restoreLocals_regs n k s (ra n) (by unfold ra; omega)
    (by simp [ra, addr]) (by simp [ra, tmp])

theorem restoreLocals_arg {n k : Nat} (s : State w) (hk : k ≤ n) (j : Nat) :
    (execBlock (restoreLocals n k) s).regs (arg n j) = s.regs (arg n j) := by
  apply restoreLocals_regs
  · unfold arg
    omega
  · exact Nat.ne_of_gt (by unfold arg addr; omega)
  · exact Nat.ne_of_gt (by unfold arg tmp; omega)

@[simp] theorem restoreLocals_mem (n k : Nat) (s : State w) :
    (execBlock (restoreLocals n k) s).mem = s.mem := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [restoreLocals, execBlock_append, restoreLocal_mem, ih]

/-- Restoration reads each slot without altering memory or the stack pointer. -/
theorem restoreLocals_local {n k : Nat} (s : State w) (hk : k ≤ n)
    (i : Nat) (hi : i < k) :
    (execBlock (restoreLocals n k) s).regs i =
      s.mem (arrayAddr (s.regs (sp n)) (i + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hin : i < n := Nat.lt_of_lt_of_le hi hk
      rw [restoreLocals, execBlock_append]
      by_cases hik : i = k
      · subst i
        rw [restoreLocal_same, restoreLocals_mem, restoreLocals_sp s (Nat.le_of_lt hkn)]
      · rw [restoreLocal_regs n k _ i (local_ne_addr hin) (local_ne_tmp hin) hik]
        exact ih (Nat.le_of_lt hkn) (by omega)

/-- The frame can come from any earlier save, provided its words have survived.
No equality between the caller's entire heap and target memory is assumed. -/
theorem restoreLocals_frame {n k : Nat} (s : State w) (hk : k ≤ n)
    (saved : Reg → Word w) (hframe : FrameSaved k (s.regs (sp n)) saved s.mem) :
    ∀ i, i < k → (execBlock (restoreLocals n k) s).regs i = saved i := by
  intro i hi
  exact (restoreLocals_local s hk i hi).trans (hframe i hi)

theorem FrameSaved.congr {k : Nat} {base : Word w} {saved : Reg → Word w}
    {before after : Word w → Word w} (h : FrameSaved k base saved before)
    (hmem : ∀ i, i < k → after (arrayAddr base (i + 1)) = before (arrayAddr base (i + 1))) :
    FrameSaved k base saved after := by
  intro i hi
  exact (hmem i hi).trans (h i hi)

@[simp] theorem saveLocal_input (n i : Nat) (s : State w) :
    (execBlock (saveLocal n i) s).input = s.input := rfl

@[simp] theorem saveLocal_output (n i : Nat) (s : State w) :
    (execBlock (saveLocal n i) s).outputRev = s.outputRev := rfl

@[simp] theorem restoreLocal_input (n i : Nat) (s : State w) :
    (execBlock (restoreLocal n i) s).input = s.input := rfl

@[simp] theorem restoreLocal_output (n i : Nat) (s : State w) :
    (execBlock (restoreLocal n i) s).outputRev = s.outputRev := rfl

@[simp] theorem saveLocals_input (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).input = s.input := by
  induction k with
  | zero => rfl
  | succ k ih => simp [saveLocals, ih]

@[simp] theorem saveLocals_output (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).outputRev = s.outputRev := by
  induction k with
  | zero => rfl
  | succ k ih => simp [saveLocals, ih]

@[simp] theorem restoreLocals_input (n k : Nat) (s : State w) :
    (execBlock (restoreLocals n k) s).input = s.input := by
  induction k with
  | zero => rfl
  | succ k ih => simp [restoreLocals, ih]

@[simp] theorem restoreLocals_output (n k : Nat) (s : State w) :
    (execBlock (restoreLocals n k) s).outputRev = s.outputRev := by
  induction k with
  | zero => rfl
  | succ k ih => simp [restoreLocals, ih]

@[simp] theorem saveLocals_status (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).status = s.status :=
  execBlock_status _ _ (saveLocals_linear n k)

@[simp] theorem restoreLocals_status (n k : Nat) (s : State w) :
    (execBlock (restoreLocals n k) s).status = s.status :=
  execBlock_status _ _ (restoreLocals_linear n k)

@[simp] theorem saveLocals_pc (n k : Nat) (s : State w) :
    (execBlock (saveLocals n k) s).pc = s.pc + 3 * k := by
  simpa using execBlock_pc (saveLocals n k) s (saveLocals_linear n k)

@[simp] theorem restoreLocals_pc (n k : Nat) (s : State w) :
    (execBlock (restoreLocals n k) s).pc = s.pc + 3 * k := by
  simpa using execBlock_pc (restoreLocals n k) s (restoreLocals_linear n k)

/-- Single-slot save executes three fetched machine instructions. -/
theorem saveLocal_exec {code : Code} {n i : Nat} {s : State w}
    (hcode : CodeAt code s.pc (saveLocal n i)) (hrun : s.status = .running) :
    Exec code 3 s (execBlock (saveLocal n i) s) := by
  simpa using execBlock_exec hcode (saveLocal_linear n i) hrun

/-- Single-slot restore executes three fetched machine instructions. -/
theorem restoreLocal_exec {code : Code} {n i : Nat} {s : State w}
    (hcode : CodeAt code s.pc (restoreLocal n i)) (hrun : s.status = .running) :
    Exec code 3 s (execBlock (restoreLocal n i) s) := by
  simpa using execBlock_exec hcode (restoreLocal_linear n i) hrun

/-- The count follows from the emitted instruction list, not a frame-cost
annotation or a bulk-copy instruction. -/
theorem saveLocals_exec {code : Code} {n k : Nat} {s : State w}
    (hcode : CodeAt code s.pc (saveLocals n k)) (hrun : s.status = .running) :
    Exec code (3 * k) s (execBlock (saveLocals n k) s) := by
  simpa using execBlock_exec hcode (saveLocals_linear n k) hrun

theorem restoreLocals_exec {code : Code} {n k : Nat} {s : State w}
    (hcode : CodeAt code s.pc (restoreLocals n k)) (hrun : s.status = .running) :
    Exec code (3 * k) s (execBlock (restoreLocals n k) s) := by
  simpa using execBlock_exec hcode (restoreLocals_linear n k) hrun

end Ram.ABI
