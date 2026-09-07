/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Execution
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Heap addresses accessed by actual machine transitions

`heapAccesses code n s` and `heapWrites code n s` observe the existing
`runExact` prefixes of lengths `k < n`. They do not introduce another runner or
execution relation. A stopped state or failed fetch contributes nothing; the
instruction at the unexecuted final state is not included. If fewer than `n`
transitions exist, only the successful prefixes contribute.

Only `load` and `store` access heap words. Input/output, register operations,
and instruction fetches are not heap accesses. Compiler-generated stack loads
and stores are ordinary heap instructions and therefore are included. A store
counts as a write even if its value equals the previous value.

These finite sets count distinct addresses visited cumulatively, not live or
peak storage. `heapAccesses_card_le` follows from the fixed instruction
vocabulary's at-most-one heap address per transition. Memory outside the
actual write set is unchanged by the same `Exec` witnessed elsewhere.
-/

namespace Ram

/-- The heap addresses used by an instruction body in its entry state. -/
def Instr.heapAccesses (instr : Instr) (s : State w) : Finset (Word w) :=
  match instr with
  | .load _ address | .store address _ => {s.regs address}
  | _ => ∅

/-- Only a store writes a heap word; the address is read before the update. -/
def Instr.heapWrites (instr : Instr) (s : State w) : Finset (Word w) :=
  match instr with
  | .store address _ => {s.regs address}
  | _ => ∅

/-- A heap access requires the same running-state guard and fetch as `step`. -/
def stepHeapAccesses (code : Code) (s : State w) : Finset (Word w) :=
  if s.status = .running then
    match code[s.pc]? with
    | some instr => instr.heapAccesses s
    | none => ∅
  else ∅

/-- The write addresses of the instruction that the existing `step` executes. -/
def stepHeapWrites (code : Code) (s : State w) : Finset (Word w) :=
  if s.status = .running then
    match code[s.pc]? with
    | some instr => instr.heapWrites s
    | none => ∅
  else ∅

private def prefixFootprint (observe : State w → Finset (Word w))
    (code : Code) (n : Nat) (s : State w) : Finset (Word w) :=
  (Finset.range n).biUnion fun k =>
    match runExact code k s with
    | some current => observe current
    | none => ∅

/-- Distinct heap addresses accessed in the first `n` actual transitions. -/
def heapAccesses (code : Code) (n : Nat) (s : State w) : Finset (Word w) :=
  prefixFootprint (stepHeapAccesses code) code n s

/-- Distinct heap addresses written in the first `n` actual transitions. -/
def heapWrites (code : Code) (n : Nat) (s : State w) : Finset (Word w) :=
  prefixFootprint (stepHeapWrites code) code n s

theorem stepHeapAccesses_of_fetch {code : Code} {s : State w} {instr : Instr}
    (running : s.status = .running) (fetch : code[s.pc]? = some instr) :
    stepHeapAccesses code s = instr.heapAccesses s := by
  simp [stepHeapAccesses, running, fetch]

theorem stepHeapWrites_of_fetch {code : Code} {s : State w} {instr : Instr}
    (running : s.status = .running) (fetch : code[s.pc]? = some instr) :
    stepHeapWrites code s = instr.heapWrites s := by
  simp [stepHeapWrites, running, fetch]

theorem stepHeapWrites_subset_accesses (code : Code) (s : State w) :
    stepHeapWrites code s ⊆ stepHeapAccesses code s := by
  by_cases running : s.status = .running
  · cases fetch : code[s.pc]? with
    | none => simp [stepHeapWrites, stepHeapAccesses, running, fetch]
    | some instr =>
        rw [stepHeapWrites_of_fetch running fetch, stepHeapAccesses_of_fetch running fetch]
        cases instr <;> simp [Instr.heapWrites, Instr.heapAccesses]
  · simp [stepHeapWrites, stepHeapAccesses, running]

private theorem step_exists_of_mem_accesses {code : Code} {s : State w} {address : Word w}
    (member : address ∈ stepHeapAccesses code s) : ∃ t, step code s = some t := by
  by_cases running : s.status = .running
  · cases fetch : code[s.pc]? with
    | none => simp [stepHeapAccesses, running, fetch] at member
    | some instr => exact ⟨execInstr instr s, step_of_fetch running fetch⟩
  · simp [stepHeapAccesses, running] at member

private theorem mem_prefixFootprint {observe : State w → Finset (Word w)}
    {code : Code} {n : Nat} {s : State w} {address : Word w} :
    address ∈ prefixFootprint observe code n s ↔
      ∃ k, k < n ∧ ∃ current, Exec code k s current ∧ address ∈ observe current := by
  simp only [prefixFootprint, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, member⟩
    cases run : runExact code k s with
    | none => simp [run] at member
    | some current =>
        exact ⟨k, hk, current, runExact_iff.mp run, by simpa only [run] using member⟩
  · rintro ⟨k, hk, current, execution, member⟩
    exact ⟨k, hk, by simpa only [runExact_iff.mpr execution] using member⟩

/-- Every recorded access has an actual prefix and a following executed step.
The strict prefix bound excludes an instruction merely present at the endpoint. -/
theorem mem_heapAccesses_iff {code : Code} {n : Nat} {s : State w} {address : Word w} :
    address ∈ heapAccesses code n s ↔
      ∃ k, k < n ∧ ∃ current next,
        Exec code k s current ∧ step code current = some next ∧
          address ∈ stepHeapAccesses code current := by
  constructor
  · intro member
    obtain ⟨k, hk, current, prefixRun, access⟩ := mem_prefixFootprint.mp member
    obtain ⟨next, transition⟩ := step_exists_of_mem_accesses access
    exact ⟨k, hk, current, next, prefixRun, transition, access⟩
  · rintro ⟨k, hk, current, _, prefixRun, _, access⟩
    exact mem_prefixFootprint.mpr ⟨k, hk, current, prefixRun, access⟩

/-- A recorded write likewise belongs to an actual store transition. -/
theorem mem_heapWrites_iff {code : Code} {n : Nat} {s : State w} {address : Word w} :
    address ∈ heapWrites code n s ↔
      ∃ k, k < n ∧ ∃ current next,
        Exec code k s current ∧ step code current = some next ∧
          address ∈ stepHeapWrites code current := by
  constructor
  · intro member
    obtain ⟨k, hk, current, prefixRun, write⟩ := mem_prefixFootprint.mp member
    obtain ⟨next, transition⟩ :=
      step_exists_of_mem_accesses (stepHeapWrites_subset_accesses code current write)
    exact ⟨k, hk, current, next, prefixRun, transition, write⟩
  · rintro ⟨k, hk, current, _, prefixRun, _, write⟩
    exact mem_prefixFootprint.mpr ⟨k, hk, current, prefixRun, write⟩

private theorem prefixFootprint_zero (observe : State w → Finset (Word w))
    (code : Code) (s : State w) : prefixFootprint observe code 0 s = ∅ := by
  simp [prefixFootprint]

private theorem prefixFootprint_one (observe : State w → Finset (Word w))
    (code : Code) (s : State w) : prefixFootprint observe code 1 s = observe s := by
  simp [prefixFootprint, Finset.range_one]

private theorem prefixFootprint_succ (observe : State w → Finset (Word w))
    (code : Code) (n : Nat) (s : State w) :
    prefixFootprint observe code (n + 1) s =
      (match runExact code n s with | some current => observe current | none => ∅) ∪
        prefixFootprint observe code n s := by
  simp [prefixFootprint, Finset.range_add_one, Finset.biUnion_insert]

private theorem prefixFootprint_add (observe : State w → Finset (Word w))
    {code : Code} {n : Nat} {s middle : State w} (prefixRun : Exec code n s middle) (m : Nat) :
    prefixFootprint observe code (n + m) s =
      prefixFootprint observe code n s ∪ prefixFootprint observe code m middle := by
  induction m with
  | zero => simp [prefixFootprint_zero]
  | succ m ih =>
      have run : runExact code (n + m) s = runExact code m middle := by
        rw [runExact_add, runExact_iff.mpr prefixRun]
        rfl
      rw [Nat.add_succ, prefixFootprint_succ, prefixFootprint_succ, run, ih]
      exact Finset.union_left_comm _ _ _

@[simp] theorem heapAccesses_zero (code : Code) (s : State w) :
    heapAccesses code 0 s = ∅ := prefixFootprint_zero _ _ _

@[simp] theorem heapWrites_zero (code : Code) (s : State w) :
    heapWrites code 0 s = ∅ := prefixFootprint_zero _ _ _

@[simp] theorem heapAccesses_one (code : Code) (s : State w) :
    heapAccesses code 1 s = stepHeapAccesses code s := prefixFootprint_one _ _ _

@[simp] theorem heapWrites_one (code : Code) (s : State w) :
    heapWrites code 1 s = stepHeapWrites code s := prefixFootprint_one _ _ _

/-- Cut the cumulative access set at a real execution endpoint. The suffix
may stop early; no hypothetical state is substituted for the actual cut point. -/
theorem heapAccesses_add {code : Code} {n : Nat} {s middle : State w}
    (prefixRun : Exec code n s middle) (m : Nat) :
    heapAccesses code (n + m) s = heapAccesses code n s ∪ heapAccesses code m middle :=
  prefixFootprint_add _ prefixRun m

theorem heapWrites_add {code : Code} {n : Nat} {s middle : State w}
    (prefixRun : Exec code n s middle) (m : Nat) :
    heapWrites code (n + m) s = heapWrites code n s ∪ heapWrites code m middle :=
  prefixFootprint_add _ prefixRun m

theorem heapWrites_subset_accesses (code : Code) (n : Nat) (s : State w) :
    heapWrites code n s ⊆ heapAccesses code n s := by
  intro address member
  obtain ⟨k, hk, current, prefixRun, write⟩ := mem_prefixFootprint.mp member
  exact mem_prefixFootprint.mpr
    ⟨k, hk, current, prefixRun, stepHeapWrites_subset_accesses code current write⟩

/-- No instruction in this machine vocabulary touches two heap addresses. -/
theorem stepHeapAccesses_card_le (code : Code) (s : State w) :
    (stepHeapAccesses code s).card ≤ 1 := by
  by_cases running : s.status = .running
  · cases fetch : code[s.pc]? with
    | none => simp [stepHeapAccesses, running, fetch]
    | some instr =>
        rw [stepHeapAccesses_of_fetch running fetch]
        cases instr <;> simp [Instr.heapAccesses]
  · simp [stepHeapAccesses, running]

/-- The number of distinct cumulative heap accesses is at most the number of
requested transitions. Repeated addresses are counted only once. -/
theorem heapAccesses_card_le (code : Code) (n : Nat) (s : State w) :
    (heapAccesses code n s).card ≤ n := by
  unfold heapAccesses prefixFootprint
  apply (Finset.card_biUnion_le_card_mul (Finset.range n) _ 1 ?_).trans
  · simp
  · intro k _
    cases runExact code k s with
    | none => simp
    | some current => exact stepHeapAccesses_card_le code current

theorem heapWrites_card_le (code : Code) (n : Nat) (s : State w) :
    (heapWrites code n s).card ≤ n :=
  (Finset.card_le_card (heapWrites_subset_accesses code n s)).trans
    (heapAccesses_card_le code n s)

private theorem instr_mem_eq_of_not_written (instr : Instr) (s : State w) {address : Word w}
    (unwritten : address ∉ instr.heapWrites s) :
    (execInstr instr s).mem address = s.mem address := by
  cases instr <;> try rfl
  case store addrReg src =>
    have ne : address ≠ s.regs addrReg := by simpa [Instr.heapWrites] using unwritten
    exact State.setMem_ne s _ address _ ne
  case branchZero cond target =>
    simp only [execInstr]
    split <;> rfl
  case read dst =>
    simp only [execInstr]
    split <;> rfl

/-- A real machine step preserves every heap word outside its actual writes. -/
theorem mem_eq_of_step_of_not_written {code : Code} {s t : State w} {address : Word w}
    (transition : step code s = some t) (unwritten : address ∉ stepHeapWrites code s) :
    t.mem address = s.mem address := by
  obtain ⟨running, instr, fetch, rfl⟩ := step_iff.mp transition
  rw [stepHeapWrites_of_fetch running fetch] at unwritten
  exact instr_mem_eq_of_not_written instr s unwritten

/-- The final heap equals the initial heap at every address never written by
this exact execution, irrespective of loads or unrelated register and I/O work. -/
theorem Exec.mem_eq_of_not_written {code : Code} {n : Nat} {s t : State w}
    (execution : Exec code n s t) {address : Word w}
    (unwritten : address ∉ heapWrites code n s) : t.mem address = s.mem address := by
  induction execution with
  | refl => rfl
  | @cons n s middle t transition rest ih =>
      have split : heapWrites code (n + 1) s =
          stepHeapWrites code s ∪ heapWrites code n middle := by
        simpa only [Nat.add_comm 1 n, heapWrites_one] using
          heapWrites_add (Exec.single transition) n
      rw [split, Finset.mem_union, not_or] at unwritten
      exact (ih unwritten.2).trans (mem_eq_of_step_of_not_written transition unwritten.1)

end Ram
