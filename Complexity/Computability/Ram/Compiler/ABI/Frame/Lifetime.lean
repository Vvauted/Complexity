/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Prefix
import Complexity.Computability.Ram.Compiler.Local.ABI.Slots
import Mathlib.Order.Interval.Finset.Nat

/-!
# Partial saving and restoration of caller-frame words

After `k` real transitions of a local save or restore, precisely `k / 3`
local slots have been processed. The two address-calculation instructions
preceding each store or load do not process a slot. These counts come from
the actual instruction lists and footprints, not from changes to SP.

This module describes pending ABI restoration obligations. It does not
declare a general heap allocator, nor identify cumulative accesses with
simultaneously live memory across unrelated calls.
-/

namespace Ram.ABI

/-- Address calculation has no heap access, even at its intermediate state. -/
theorem slotAddress_prefix_heapAccesses_eq_empty {code : Code} {control slot k : Nat}
    {start : State w} (atBlock : CodeAt code start.pc (slotAddress control slot))
    (running : start.status = .running) (hk : k ≤ 2) :
    heapAccesses code k start = ∅ := by
  have complete : heapAccesses code 2 start = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro address member
    change address ∈ heapAccesses code (slotAddress control slot).length start at member
    obtain ⟨j, hj, access⟩ :=
      (mem_heapAccesses_execBlock_iff atBlock (slotAddress_linear control slot) running address).mp
        member
    have cases : j = 0 ∨ j = 1 := by
      simp only [slotAddress, List.length_cons, List.length_nil] at hj
      omega
    rcases cases with rfl | rfl <;> simp [slotAddress, Instr.heapAccesses] at access
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  have fullMember := heapAccesses_mono code start hk member
  simp only [complete, Finset.notMem_empty] at fullMember

/-- In particular, merely calculating the next slot address does not save it. -/
theorem slotAddress_prefix_heapWrites_eq_empty {code : Code} {control slot k : Nat}
    {start : State w} (atBlock : CodeAt code start.pc (slotAddress control slot))
    (running : start.status = .running) (hk : k ≤ 2) :
    heapWrites code k start = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  have access := heapWrites_subset_accesses code k start member
  simp only [slotAddress_prefix_heapAccesses_eq_empty atBlock running hk,
    Finset.notMem_empty] at access

/-- The exact words already saved at every actual prefix. Word-address sets
allow wrapping; distinctness and saved-value correctness need separate fits. -/
theorem saveLocals_prefix_heapWrites {code : Code} {control locals k : Nat}
    {start : State w} (atBlock : CodeAt code start.pc (saveLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals) :
    heapWrites code k start = (Finset.range (k / 3)).image
      (fun i => arrayAddr (start.regs (sp control)) (i + 1)) := by
  induction locals generalizing k with
  | zero =>
      have zero : k = 0 := by omega
      simp [zero]
  | succ locals ih =>
      by_cases before : k ≤ 3 * locals
      · exact ih atBlock.append_left before
      · by_cases complete : k = 3 * (locals + 1)
        · have quotient : k / 3 = locals + 1 := by omega
          rw [quotient, complete]
          exact saveLocals_heapWrites atBlock running
        · have tail : k - 3 * locals ≤ 2 := by omega
          have split : k = 3 * locals + (k - 3 * locals) := by omega
          have quotient : k / 3 = locals := by omega
          have first := saveLocals_exec atBlock.append_left running
          have atLast : CodeAt code (execBlock (saveLocals control locals) start).pc
              (saveLocal control locals) := by
            rw [saveLocals_pc]
            simpa only [saveLocals_length] using atBlock.append_right
          have ready := (saveLocals_status control locals start).trans running
          have empty := slotAddress_prefix_heapWrites_eq_empty atLast.append_left ready tail
          rw [quotient, split, heapWrites_add first,
            saveLocals_heapWrites atBlock.append_left running, empty, Finset.union_empty]

/-- A restore releases a local's pending memory obligation only at its load,
not at either address-calculation instruction. The register bound retains SP. -/
theorem restoreLocals_prefix_heapAccesses {code : Code} {control locals k : Nat}
    {start : State w} (localFit : locals ≤ control)
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals) :
    heapAccesses code k start = (Finset.range (k / 3)).image
      (fun i => arrayAddr (start.regs (sp control)) (i + 1)) := by
  induction locals generalizing k with
  | zero =>
      have zero : k = 0 := by omega
      simp [zero]
  | succ locals ih =>
      by_cases before : k ≤ 3 * locals
      · exact ih (by omega) atBlock.append_left before
      · by_cases complete : k = 3 * (locals + 1)
        · have quotient : k / 3 = locals + 1 := by omega
          rw [quotient, complete]
          exact restoreLocals_heapAccesses localFit atBlock running
        · have tail : k - 3 * locals ≤ 2 := by omega
          have split : k = 3 * locals + (k - 3 * locals) := by omega
          have quotient : k / 3 = locals := by omega
          have first := restoreLocals_exec atBlock.append_left running
          have atLast : CodeAt code (execBlock (restoreLocals control locals) start).pc
              (restoreLocal control locals) := by
            rw [restoreLocals_pc]
            simpa only [restoreLocals_length] using atBlock.append_right
          have ready := (restoreLocals_status control locals start).trans running
          have empty := slotAddress_prefix_heapAccesses_eq_empty atLast.append_left ready tail
          rw [quotient, split, heapAccesses_add first,
            restoreLocals_heapAccesses (by omega) atBlock.append_left running,
            empty, Finset.union_empty]

/-- The address-calculation prefix preserves every non-temporary register
at its actual intermediate state. -/
theorem slotAddress_prefix_regs {code : Code} {control slot k register : Nat}
    {start current : State w} (atBlock : CodeAt code start.pc (slotAddress control slot))
    (running : start.status = .running) (hk : k ≤ 2)
    (notAddr : register ≠ addr control) (notTmp : register ≠ tmp control)
    (execution : Exec code k start current) : current.regs register = start.regs register := by
  rw [execution.eq_execBlock_take atBlock (slotAddress_linear control slot) running hk]
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    simp [slotAddress, execBlock, execInstr, State.setReg, State.next, notAddr, notTmp]

/-- A partial save has exactly the memory of its fully completed local slots.
Any residual address calculation does not prematurely store the next local. -/
theorem saveLocals_prefix_mem_eq {code : Code} {control locals k : Nat}
    {start current : State w} (atBlock : CodeAt code start.pc (saveLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (execution : Exec code k start current) :
    current.mem = (execBlock (saveLocals control (k / 3)) start).mem := by
  induction locals generalizing k with
  | zero =>
      have zero : k = 0 := by omega
      subst k
      have same := Exec.zero_iff.mp execution
      simp [← same, saveLocals]
  | succ locals ih =>
      by_cases before : k ≤ 3 * locals
      · exact ih atBlock.append_left before execution
      · by_cases complete : k = 3 * (locals + 1)
        · have quotient : k / 3 = locals + 1 := by omega
          have endpoint := execution.deterministic
            (by simpa only [complete] using saveLocals_exec atBlock running)
          simpa only [quotient] using congrArg (fun s : State w => s.mem) endpoint
        · have tail : k - 3 * locals ≤ 2 := by omega
          have split : k = 3 * locals + (k - 3 * locals) := by omega
          have quotient : k / 3 = locals := by omega
          have first := saveLocals_exec atBlock.append_left running
          have atLast : CodeAt code (execBlock (saveLocals control locals) start).pc
              (saveLocal control locals) := by
            rw [saveLocals_pc]
            simpa only [saveLocals_length] using atBlock.append_right
          have ready := (saveLocals_status control locals start).trans running
          have cut : Exec code (3 * locals + (k - 3 * locals)) start current := by
            simpa only [← split] using execution
          obtain ⟨middle, left, right⟩ := cut.split
          have middleEq := left.deterministic first
          subst middle
          have same := right.prefix_mem_eq_of_heapWrites_empty (Nat.le_refl _)
            (slotAddress_prefix_heapWrites_eq_empty atLast.append_left ready tail)
          simpa only [quotient] using same

/-- Saving establishes the correct caller values incrementally, at every
real prefix, under the same register and no-wrap conditions as a full save. -/
theorem saveLocals_prefix_frame {code : Code} {control locals k : Nat}
    {start current : State w} (localFit : locals ≤ control)
    (fits : (start.regs (sp control)).toNat + locals < 2 ^ w)
    (atBlock : CodeAt code start.pc (saveLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (execution : Exec code k start current) :
    FrameSaved (k / 3) (start.regs (sp control)) start.regs current.mem := by
  rw [saveLocals_prefix_mem_eq atBlock running hk execution]
  exact saveLocals_frame start (by omega) (by omega)

/-- A restore prefix changes non-temporary registers exactly as its completed
loads do. The pending slot's address calculation does not restore its value. -/
theorem restoreLocals_prefix_regs {code : Code} {control locals k register : Nat}
    {start current : State w}
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (notAddr : register ≠ addr control) (notTmp : register ≠ tmp control)
    (execution : Exec code k start current) :
    current.regs register = (execBlock (restoreLocals control (k / 3)) start).regs register := by
  induction locals generalizing k with
  | zero =>
      have zero : k = 0 := by omega
      subst k
      have same := Exec.zero_iff.mp execution
      simp [← same, restoreLocals]
  | succ locals ih =>
      by_cases before : k ≤ 3 * locals
      · exact ih atBlock.append_left before execution
      · by_cases complete : k = 3 * (locals + 1)
        · have quotient : k / 3 = locals + 1 := by omega
          have endpoint := execution.deterministic
            (by simpa only [complete] using restoreLocals_exec atBlock running)
          simpa only [quotient] using congrArg (fun s : State w => s.regs register) endpoint
        · have tail : k - 3 * locals ≤ 2 := by omega
          have split : k = 3 * locals + (k - 3 * locals) := by omega
          have quotient : k / 3 = locals := by omega
          have first := restoreLocals_exec atBlock.append_left running
          have atLast : CodeAt code (execBlock (restoreLocals control locals) start).pc
              (restoreLocal control locals) := by
            rw [restoreLocals_pc]
            simpa only [restoreLocals_length] using atBlock.append_right
          have ready := (restoreLocals_status control locals start).trans running
          have cut : Exec code (3 * locals + (k - 3 * locals)) start current := by
            simpa only [← split] using execution
          obtain ⟨middle, left, right⟩ := cut.split
          have middleEq := left.deterministic first
          subst middle
          have same := slotAddress_prefix_regs atLast.append_left ready tail notAddr notTmp right
          simpa only [quotient] using same

/-- Completed restore loads recover their saved values in the real current
state. Slots not yet loaded retain their separate memory obligations. -/
theorem restoreLocals_prefix_restored {code : Code} {control locals k : Nat}
    {start current : State w} {saved : Reg → Word w} (localFit : locals ≤ control)
    (frame : FrameSaved locals (start.regs (sp control)) saved start.mem)
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (execution : Exec code k start current) :
    ∀ i, i < k / 3 → current.regs i = saved i := by
  intro i hi
  have prefixFit : k / 3 ≤ locals := by omega
  rw [restoreLocals_prefix_regs atBlock running hk
    (by unfold addr; omega) (by unfold tmp; omega) execution]
  exact restoreLocals_frame start (prefixFit.trans localFit) saved
    (fun j hj => frame j (hj.trans_le prefixFit)) i hi

/-- The local words whose restore loads have not yet executed. Indices count
occurrences in this fixed frame, not a global injective addressing scheme. -/
def pendingLocalSlots (base : Word w) (locals restored : Nat) : Finset (Word w) :=
  (Finset.Ico restored locals).image (fun i => arrayAddr base (i + 1))

private theorem local_slot_injOn {base : Word w} {locals : Nat}
    (fits : base.toNat + locals < 2 ^ w) :
    Set.InjOn (fun i => arrayAddr base (i + 1)) (Finset.range locals) := by
  intro i hi j hj equal
  have ilt := Finset.mem_range.mp hi
  have jlt := Finset.mem_range.mp hj
  have offsets := (arrayAddr_eq_iff (by omega) (by omega)).mp equal
  omega

/-- Pending and completed local slots partition the fitted save area. The
image-difference step reuses mathlib's finite-domain injectivity theorem. -/
theorem pendingLocalSlots_eq_sdiff {base : Word w} {locals restored : Nat}
    (fits : base.toNat + locals < 2 ^ w) (hle : restored ≤ locals) :
    pendingLocalSlots base locals restored =
      (Finset.range locals).image (fun i => arrayAddr base (i + 1)) \
        (Finset.range restored).image (fun i => arrayAddr base (i + 1)) := by
  have interval : Finset.Ico restored locals = Finset.range locals \ Finset.range restored := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
    omega
  rw [pendingLocalSlots, interval,
    Finset.image_sdiff_of_injOn (local_slot_injOn fits) (Finset.range_mono hle)]

/-- The exact remaining word count, including an empty or already completed
restore. The fit is local to this frame's actual word addresses. -/
theorem pendingLocalSlots_card {base : Word w} {locals restored : Nat}
    (fits : base.toNat + locals < 2 ^ w) :
    (pendingLocalSlots base locals restored).card = locals - restored := by
  rw [pendingLocalSlots, Finset.card_image_of_injOn, Nat.card_Ico]
  intro i hi j hj equal
  simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
  have offsets := (arrayAddr_eq_iff (by omega) (by omega)).mp equal
  omega

/-- The remaining local obligations are exactly those not yet loaded by the
actual restore prefix, rather than those above the instantaneous SP. -/
theorem restoreLocals_pending_slots {code : Code} {control locals k : Nat}
    {start : State w} (localFit : locals ≤ control)
    (fits : (start.regs (sp control)).toNat + locals < 2 ^ w)
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals) :
    pendingLocalSlots (start.regs (sp control)) locals (k / 3) =
      (Finset.range locals).image (fun i => arrayAddr (start.regs (sp control)) (i + 1)) \
        heapAccesses code k start := by
  rw [restoreLocals_prefix_heapAccesses localFit atBlock running hk]
  exact pendingLocalSlots_eq_sdiff fits (by omega)

/-- Count the pending words directly from the real prefix's access set. -/
theorem restoreLocals_pending_card {code : Code} {control locals k : Nat}
    {start : State w} (localFit : locals ≤ control)
    (fits : (start.regs (sp control)).toNat + locals < 2 ^ w)
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals) :
    ((Finset.range locals).image (fun i => arrayAddr (start.regs (sp control)) (i + 1)) \
      heapAccesses code k start).card = locals - k / 3 := by
  rw [← restoreLocals_pending_slots localFit fits atBlock running hk]
  exact pendingLocalSlots_card fits

/-- Partial restoration does not damage the pending saved values (or any
other saved slot). This conclusion observes an actual intermediate state. -/
theorem restoreLocals_prefix_frame {code : Code} {control locals k : Nat}
    {start current : State w} {saved : Reg → Word w}
    (frame : FrameSaved locals (start.regs (sp control)) saved start.mem)
    (atBlock : CodeAt code start.pc (restoreLocals control locals))
    (running : start.status = .running) (hk : k ≤ 3 * locals)
    (execution : Exec code k start current) :
    FrameSaved locals (start.regs (sp control)) saved current.mem := by
  rw [restoreLocals_prefix_mem atBlock running hk execution]
  exact frame

end Ram.ABI
