/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Basic

/-!
# Receiving a function's return fields

`receiveResults` copies buffered fields with one actual move per destination.
The register observation below uses the original return bank and updates locals
in destination order. Repeated destinations are allowed and keep their last
assigned value; distinctness is needed only to observe every field separately.
The receiver preserves memory, I/O, status, and all registers outside its
destination list, including the protected return bank.
-/

namespace Ram.ABI

/-- Register observation for ordered return-field assignment. The fixed `bank`
supplies every value; the fold changes only `regs`, with last-write-wins behavior.
This describes the moves in `receiveResults`, not a separate runtime operation. -/
def receiveResultRegs (n start : Nat) (dsts : List Reg)
    (bank regs : Reg → Word w) : Reg → Word w :=
  (dsts.zipIdx start).foldl
    (fun regs field => fun r => if r = field.1 then bank (resultReg n field.2) else regs r)
    regs

@[simp] theorem receiveResultRegs_nil (n start : Nat) (bank regs : Reg → Word w) :
    receiveResultRegs n start [] bank regs = regs := rfl

@[simp] theorem receiveResultRegs_cons (n start dst : Nat) (dsts : List Reg)
    (bank regs : Reg → Word w) :
    receiveResultRegs n start (dst :: dsts) bank regs =
      receiveResultRegs n (start + 1) dsts bank
        (fun r => if r = dst then bank (resultReg n start) else regs r) := rfl

/-- A register absent from the destination list is unchanged, even when other
destinations occur repeatedly. -/
theorem receiveResultRegs_preserved (n start : Nat) (dsts : List Reg)
    (bank regs : Reg → Word w) (r : Reg) (hout : r ∉ dsts) :
    receiveResultRegs n start dsts bank regs r = regs r := by
  induction dsts generalizing start regs with
  | nil => rfl
  | cons dst dsts ih =>
      have hne : r ≠ dst := fun h => hout (by simp [h])
      have htail : r ∉ dsts := fun h => hout (by simp [h])
      rw [receiveResultRegs_cons, ih (start + 1) _ htail]
      exact if_neg hne

/-- With distinct destinations, each one observes its corresponding original
buffered field. The execution and general register equation do not require this. -/
theorem receiveResultRegs_getElem (n start : Nat) (dsts : List Reg)
    (bank regs : Reg → Word w) (distinct : dsts.Nodup)
    (i : Nat) (hi : i < dsts.length) :
    receiveResultRegs n start dsts bank regs dsts[i] = bank (resultReg n (start + i)) := by
  induction dsts generalizing start regs i with
  | nil => simp at hi
  | cons dst dsts ih =>
      have hd := List.nodup_cons.mp distinct
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero, receiveResultRegs_cons]
          rw [receiveResultRegs_preserved n (start + 1) dsts bank _ dst hd.1]
          simp
      | succ i =>
          have hi' : i < dsts.length := by simpa using hi
          simpa only [receiveResultRegs_cons, List.getElem_cons_succ,
            Nat.add_assoc, Nat.add_comm 1 i] using
            ih (start + 1)
              (fun r => if r = dst then bank (resultReg n start) else regs r) hd.2 i hi'

/-- Receiving into locals reads each field from a fixed original bank. The
premise permits composition with a separately proved return-bank assertion. -/
theorem receiveResults_regs_of_bank {n start : Nat} {dsts : List Reg}
    {bank : Reg → Word w} (bounded : ∀ dst ∈ dsts, dst < n)
    (s : State w) (hbank : ∀ i, s.regs (resultReg n i) = bank (resultReg n i)) :
    (execBlock (receiveResults n start dsts) s).regs =
      receiveResultRegs n start dsts bank s.regs := by
  induction dsts generalizing start s with
  | nil => rfl
  | cons dst dsts ih =>
      have hdst : dst < n := bounded dst (by simp)
      have htail : ∀ r ∈ dsts, r < n := fun r hr => bounded r (by simp [hr])
      have hnext : ∀ i,
          (execInstr (.move dst (resultReg n start)) s).regs (resultReg n i) =
            bank (resultReg n i) := by
        intro i
        have hne : resultReg n i ≠ dst :=
          Nat.ne_of_gt (Nat.lt_trans hdst (lt_resultReg n i))
        simpa only [execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using hbank i
      rw [receiveResults, execBlock_cons, ih htail _ hnext, receiveResultRegs_cons]
      simp only [execInstr, State.next_regs, State.setReg, hbank start]

/-- The receiver's complete register effect, retaining ordered overwrites. -/
theorem receiveResults_regs {n start : Nat} {dsts : List Reg}
    (bounded : ∀ dst ∈ dsts, dst < n) (s : State w) :
    (execBlock (receiveResults n start dsts) s).regs =
      receiveResultRegs n start dsts s.regs s.regs :=
  receiveResults_regs_of_bank bounded s (fun _ => rfl)

theorem receiveResults_preserved (n start : Nat) (dsts : List Reg)
    (s : State w) (r : Reg) (hout : r ∉ dsts) :
    (execBlock (receiveResults n start dsts) s).regs r = s.regs r := by
  induction dsts generalizing start s with
  | nil => rfl
  | cons dst dsts ih =>
      have hne : r ≠ dst := fun h => hout (by simp [h])
      have htail : r ∉ dsts := fun h => hout (by simp [h])
      rw [receiveResults, execBlock_cons, ih (start + 1) _ htail]
      simp only [execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne]

/-- Local result assignments preserve every field in the protected return bank. -/
theorem receiveResults_bank {n start : Nat} {dsts : List Reg}
    (bounded : ∀ dst ∈ dsts, dst < n) (s : State w) (i : Nat) :
    (execBlock (receiveResults n start dsts) s).regs (resultReg n i) =
      s.regs (resultReg n i) := by
  apply receiveResults_preserved
  intro hmem
  exact Nat.lt_irrefl n (Nat.lt_trans (lt_resultReg n i) (bounded _ hmem))

@[simp] theorem receiveResults_mem (n start : Nat) (dsts : List Reg) (s : State w) :
    (execBlock (receiveResults n start dsts) s).mem = s.mem := by
  induction dsts generalizing start s with
  | nil => rfl
  | cons dst dsts ih => simp [receiveResults, ih, execInstr]

@[simp] theorem receiveResults_input (n start : Nat) (dsts : List Reg) (s : State w) :
    (execBlock (receiveResults n start dsts) s).input = s.input := by
  induction dsts generalizing start s with
  | nil => rfl
  | cons dst dsts ih => simp [receiveResults, ih, execInstr]

@[simp] theorem receiveResults_output (n start : Nat) (dsts : List Reg) (s : State w) :
    (execBlock (receiveResults n start dsts) s).outputRev = s.outputRev := by
  induction dsts generalizing start s with
  | nil => rfl
  | cons dst dsts ih => simp [receiveResults, ih, execInstr]

theorem receiveResults_linear (n start : Nat) (dsts : List Reg) :
    ∀ instr ∈ receiveResults n start dsts, instr.Linear := by
  induction dsts generalizing start with
  | nil => simp [receiveResults]
  | cons dst dsts ih =>
      intro instr hmem
      simp only [receiveResults, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · trivial
      · exact ih (start + 1) instr hmem

@[simp] theorem receiveResults_status (n start : Nat) (dsts : List Reg) (s : State w) :
    (execBlock (receiveResults n start dsts) s).status = s.status :=
  execBlock_status _ _ (receiveResults_linear n start dsts)

@[simp] theorem receiveResults_pc (n start : Nat) (dsts : List Reg) (s : State w) :
    (execBlock (receiveResults n start dsts) s).pc = s.pc + dsts.length := by
  simpa only [receiveResults_length] using
    execBlock_pc _ s (receiveResults_linear n start dsts)

/-- Observable effects of receiving fields into a caller's local registers. -/
structure ResultsReceived (n start : Nat) (dsts : List Reg) (s t : State w) : Prop where
  registers : t.regs = receiveResultRegs n start dsts s.regs s.regs
  preserved : ∀ r, r ∉ dsts → t.regs r = s.regs r
  bank : ∀ i, t.regs (resultReg n i) = s.regs (resultReg n i)
  memory : t.mem = s.mem
  input : t.input = s.input
  output : t.outputRev = s.outputRev
  status : t.status = s.status

/-- Buffered fields are copied without aliasing their source registers. No
distinctness requirement is imposed on the destination list. -/
theorem receiveResults_correct {n start : Nat} {dsts : List Reg}
    (bounded : ∀ dst ∈ dsts, dst < n) (s : State w) :
    ResultsReceived n start dsts s (execBlock (receiveResults n start dsts) s) :=
  ⟨receiveResults_regs bounded s, receiveResults_preserved n start dsts s,
    receiveResults_bank bounded s, receiveResults_mem n start dsts s,
    receiveResults_input n start dsts s, receiveResults_output n start dsts s,
    receiveResults_status n start dsts s⟩

/-- Each distinct destination contains the corresponding original return field. -/
theorem ResultsReceived.values {n start : Nat} {dsts : List Reg} {s t : State w}
    (h : ResultsReceived n start dsts s t) (distinct : dsts.Nodup)
    (i : Nat) (hi : i < dsts.length) :
    t.regs dsts[i] = s.regs (resultReg n (start + i)) := by
  rw [h.registers]
  exact receiveResultRegs_getElem n start dsts s.regs s.regs distinct i hi

/-- The emitted moves execute in exactly the number of destination fields,
including repeated destinations. An empty result has no receive instruction. -/
theorem receiveResults_exec {code : Code} {n start : Nat} {dsts : List Reg} {s : State w}
    (hcode : CodeAt code s.pc (receiveResults n start dsts)) (hrun : s.status = .running) :
    Exec code dsts.length s (execBlock (receiveResults n start dsts) s) := by
  simpa only [receiveResults_length] using
    execBlock_exec hcode (receiveResults_linear n start dsts) hrun

end Ram.ABI
