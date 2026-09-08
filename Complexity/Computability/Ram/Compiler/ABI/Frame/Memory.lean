/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Basic
import Complexity.Computability.Ram.Execution.Block.Prefix

/-!
# Actual heap footprints of caller-frame save and restore blocks

Every set below is the existing footprint of real fetched machine transitions.
The slot address is evaluated after the two address-calculation instructions,
not inferred from the block's final memory. A restore has no writes because
none of its instructions is a store, not because its final heap happens to
equal the initial heap.

All addresses are relative to this block's entry SP. In the calling convention,
locals are saved before SP advances; on return, SP retreats before locals are
restored. These statements must be applied to those respective actual entry
states. `saveReturn` covers offset zero; local slots have offsets `i + 1`.

Exact word-address sets allow modular wraparound. Only the final interval
characterization assumes no wrap. Saving never changes SP; restoring `k`
locals requires `k ≤ control` for a footprint relative to the original SP,
since otherwise a restored register could itself be SP. Empty batches are
included. These are cumulative access sets, not a claim about peak live space.
-/

namespace Ram.ABI

theorem saveLocal_heapAccesses {code : Code} {n i : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveLocal n i)) (running : s.status = .running) :
    heapAccesses code 3 s = {arrayAddr (s.regs (sp n)) (i + 1)} := by
  ext address
  change address ∈ heapAccesses code (saveLocal n i).length s ↔ _
  rw [mem_heapAccesses_execBlock_iff atBlock (saveLocal_linear n i) running]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, access⟩
    have cases : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [saveLocal_length] at hj; omega
    rcases cases with rfl | rfl | rfl
    · simp [saveLocal, slotAddress, Instr.heapAccesses] at access
    · simp [saveLocal, slotAddress, Instr.heapAccesses] at access
    · change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)} at access
      simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using access
  · intro equal
    refine ⟨2, by simp, ?_⟩
    change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)}
    simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using equal

theorem saveLocal_heapWrites {code : Code} {n i : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveLocal n i)) (running : s.status = .running) :
    heapWrites code 3 s = {arrayAddr (s.regs (sp n)) (i + 1)} := by
  ext address
  change address ∈ heapWrites code (saveLocal n i).length s ↔ _
  rw [mem_heapWrites_execBlock_iff atBlock (saveLocal_linear n i) running]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, write⟩
    have cases : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [saveLocal_length] at hj; omega
    rcases cases with rfl | rfl | rfl
    · simp [saveLocal, slotAddress, Instr.heapWrites] at write
    · simp [saveLocal, slotAddress, Instr.heapWrites] at write
    · change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)} at write
      simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using write
  · intro equal
    refine ⟨2, by simp, ?_⟩
    change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)}
    simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using equal

theorem restoreLocal_heapAccesses {code : Code} {n i : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (restoreLocal n i)) (running : s.status = .running) :
    heapAccesses code 3 s = {arrayAddr (s.regs (sp n)) (i + 1)} := by
  ext address
  change address ∈ heapAccesses code (restoreLocal n i).length s ↔ _
  rw [mem_heapAccesses_execBlock_iff atBlock (restoreLocal_linear n i) running]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, access⟩
    have cases : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [restoreLocal_length] at hj; omega
    rcases cases with rfl | rfl | rfl
    · simp [restoreLocal, slotAddress, Instr.heapAccesses] at access
    · simp [restoreLocal, slotAddress, Instr.heapAccesses] at access
    · change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)} at access
      simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using access
  · intro equal
    refine ⟨2, by simp, ?_⟩
    change address ∈ {(execBlock (slotAddress n i) s).regs (addr n)}
    simpa only [slotAddress_regs, if_pos rfl, Finset.mem_singleton] using equal

theorem restoreLocal_heapWrites {code : Code} {n i : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (restoreLocal n i)) (running : s.status = .running) :
    heapWrites code 3 s = ∅ := by
  ext address
  change address ∈ heapWrites code (restoreLocal n i).length s ↔ _
  rw [mem_heapWrites_execBlock_iff atBlock (restoreLocal_linear n i) running]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨j, hj, write⟩
  have cases : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [restoreLocal_length] at hj; omega
  rcases cases with rfl | rfl | rfl <;>
    simp [restoreLocal, slotAddress, Instr.heapWrites] at write

theorem saveReturn_heapAccesses {code : Code} {n returnPC : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveReturn n returnPC)) (running : s.status = .running) :
    heapAccesses code 2 s = {s.regs (sp n)} := by
  have linear : ∀ instr ∈ saveReturn n returnPC, instr.Linear := by
    simp [saveReturn, Instr.Linear]
  ext address
  change address ∈ heapAccesses code (saveReturn n returnPC).length s ↔ _
  rw [mem_heapAccesses_execBlock_iff atBlock linear running]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, access⟩
    have cases : j = 0 ∨ j = 1 := by simp only [saveReturn, List.length_cons, List.length_nil] at hj; omega
    rcases cases with rfl | rfl
    · simp [saveReturn, Instr.heapAccesses] at access
    · simpa [saveReturn, Instr.heapAccesses, execBlock, execInstr, State.setReg,
        State.next, sp, tmp] using access
  · intro equal
    refine ⟨1, by simp [saveReturn], ?_⟩
    simpa [saveReturn, Instr.heapAccesses, execBlock, execInstr, State.setReg,
      State.next, sp, tmp] using equal

theorem saveReturn_heapWrites {code : Code} {n returnPC : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveReturn n returnPC)) (running : s.status = .running) :
    heapWrites code 2 s = {s.regs (sp n)} := by
  have linear : ∀ instr ∈ saveReturn n returnPC, instr.Linear := by
    simp [saveReturn, Instr.Linear]
  ext address
  change address ∈ heapWrites code (saveReturn n returnPC).length s ↔ _
  rw [mem_heapWrites_execBlock_iff atBlock linear running]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, write⟩
    have cases : j = 0 ∨ j = 1 := by simp only [saveReturn, List.length_cons, List.length_nil] at hj; omega
    rcases cases with rfl | rfl
    · simp [saveReturn, Instr.heapWrites] at write
    · simpa [saveReturn, Instr.heapWrites, execBlock, execInstr, State.setReg,
        State.next, sp, tmp] using write
  · intro equal
    refine ⟨1, by simp [saveReturn], ?_⟩
    simpa [saveReturn, Instr.heapWrites, execBlock, execInstr, State.setReg,
      State.next, sp, tmp] using equal

/-- Each saved local contributes its actual store address. No local-count or
no-wrap premise is needed merely to describe these modular addresses. -/
theorem saveLocals_heapAccesses {code : Code} {n k : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveLocals n k)) (running : s.status = .running) :
    heapAccesses code (3 * k) s =
      (Finset.range k).image (fun i => arrayAddr (s.regs (sp n)) (i + 1)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      change CodeAt code s.pc (saveLocals n k ++ saveLocal n k) at atBlock
      have first := saveLocals_exec atBlock.append_left running
      have atLast : CodeAt code (execBlock (saveLocals n k) s).pc (saveLocal n k) := by
        rw [execBlock_pc _ _ (saveLocals_linear n k)]
        exact atBlock.append_right
      have ready := (saveLocals_status n k s).trans running
      rw [Nat.mul_succ, heapAccesses_add first, ih atBlock.append_left running,
        saveLocal_heapAccesses atLast ready, saveLocals_sp,
        Finset.union_singleton, Finset.range_add_one, Finset.image_insert]

theorem saveLocals_heapWrites {code : Code} {n k : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (saveLocals n k)) (running : s.status = .running) :
    heapWrites code (3 * k) s =
      (Finset.range k).image (fun i => arrayAddr (s.regs (sp n)) (i + 1)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      change CodeAt code s.pc (saveLocals n k ++ saveLocal n k) at atBlock
      have first := saveLocals_exec atBlock.append_left running
      have atLast : CodeAt code (execBlock (saveLocals n k) s).pc (saveLocal n k) := by
        rw [execBlock_pc _ _ (saveLocals_linear n k)]
        exact atBlock.append_right
      have ready := (saveLocals_status n k s).trans running
      rw [Nat.mul_succ, heapWrites_add first, ih atBlock.append_left running,
        saveLocal_heapWrites atLast ready, saveLocals_sp,
        Finset.union_singleton, Finset.range_add_one, Finset.image_insert]

/-- Restoring only local registers leaves SP available for every later slot
calculation. This premise concerns register aliasing, not address wraparound. -/
theorem restoreLocals_heapAccesses {code : Code} {n k : Nat} {s : State w}
    (locals : k ≤ n) (atBlock : CodeAt code s.pc (restoreLocals n k))
    (running : s.status = .running) :
    heapAccesses code (3 * k) s =
      (Finset.range k).image (fun i => arrayAddr (s.regs (sp n)) (i + 1)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      have hk : k ≤ n := by omega
      change CodeAt code s.pc (restoreLocals n k ++ restoreLocal n k) at atBlock
      have first := restoreLocals_exec atBlock.append_left running
      have atLast : CodeAt code (execBlock (restoreLocals n k) s).pc (restoreLocal n k) := by
        rw [execBlock_pc _ _ (restoreLocals_linear n k)]
        exact atBlock.append_right
      have ready := (restoreLocals_status n k s).trans running
      rw [Nat.mul_succ, heapAccesses_add first, ih hk atBlock.append_left running,
        restoreLocal_heapAccesses atLast ready, restoreLocals_sp s hk,
        Finset.union_singleton, Finset.range_add_one, Finset.image_insert]

/-- Every restore instruction is write-free, even without the local-register
bound needed for the entry-SP description of the read addresses. -/
theorem restoreLocals_heapWrites {code : Code} {n k : Nat} {s : State w}
    (atBlock : CodeAt code s.pc (restoreLocals n k)) (running : s.status = .running) :
    heapWrites code (3 * k) s = ∅ := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      change CodeAt code s.pc (restoreLocals n k ++ restoreLocal n k) at atBlock
      have first := restoreLocals_exec atBlock.append_left running
      have atLast : CodeAt code (execBlock (restoreLocals n k) s).pc (restoreLocal n k) := by
        rw [execBlock_pc _ _ (restoreLocals_linear n k)]
        exact atBlock.append_right
      have ready := (restoreLocals_status n k s).trans running
      rw [Nat.mul_succ, heapWrites_add first, ih atBlock.append_left running,
        restoreLocal_heapWrites atLast ready, Finset.empty_union]

/-- Without wrap, the exact image above is the natural interval of local
slots, excluding offset zero and including the final slot. For `k = 0` both
sides are empty. Use the exact word image when this no-wrap premise fails. -/
theorem mem_slot_image_iff {base address : Word w} {k : Nat}
    (fits : base.toNat + k < 2 ^ w) :
    address ∈ (Finset.range k).image (fun i => arrayAddr base (i + 1)) ↔
      base.toNat < address.toNat ∧ address.toNat ≤ base.toNat + k := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [arrayAddr_toNat (by omega)]
    omega
  · rintro ⟨lower, upper⟩
    have hi : address.toNat - base.toNat - 1 < k := by omega
    refine ⟨address.toNat - base.toNat - 1, hi, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [arrayAddr_toNat (by omega)]
    omega

end Ram.ABI
