/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Execution

/-!
# Straight-line instruction blocks

`execBlock` is a convenient state transformer, not a second cost model.
`execBlock_exec` connects it to exactly one real machine transition per
instruction whenever a linear block is present at the current program counter.
-/

namespace Ram

/-- Instructions that always advance to the next address without changing
running status. Input reads are excluded because exhausted input faults. -/
def Instr.Linear : Instr → Prop
  | .const _ _ | .move _ _ | .binop _ _ _ _ | .load _ _ | .store _ _ | .write _ => True
  | _ => False

theorem execInstr_pc_of_linear {i : Instr} (s : State w) (h : i.Linear) :
    (execInstr i s).pc = s.pc + 1 := by
  cases i <;> simp_all [Instr.Linear, execInstr]

theorem execInstr_status_of_linear {i : Instr} (s : State w) (h : i.Linear) :
    (execInstr i s).status = s.status := by
  cases i <;> simp_all [Instr.Linear, execInstr]

/-- Fold instruction bodies in their program order. This transformer is used
only through the machine-execution theorem when assigning a transition count. -/
def execBlock (block : Code) (s : State w) : State w :=
  block.foldl (fun s i => execInstr i s) s

@[simp] theorem execBlock_nil (s : State w) : execBlock [] s = s := rfl

@[simp] theorem execBlock_cons (i : Instr) (block : Code) (s : State w) :
    execBlock (i :: block) s = execBlock block (execInstr i s) := rfl

@[simp] theorem execBlock_append (a b : Code) (s : State w) :
    execBlock (a ++ b) s = execBlock b (execBlock a s) := by
  simp [execBlock]

theorem execBlock_pc (block : Code) (s : State w)
    (hlinear : ∀ i ∈ block, i.Linear) :
    (execBlock block s).pc = s.pc + block.length := by
  induction block generalizing s with
  | nil => simp
  | cons i block ih =>
      have hi := hlinear i (by simp)
      have ht : ∀ j ∈ block, j.Linear := fun j hj => hlinear j (by simp [hj])
      rw [execBlock_cons, ih _ ht, execInstr_pc_of_linear s hi, List.length_cons]
      omega

theorem execBlock_status (block : Code) (s : State w)
    (hlinear : ∀ i ∈ block, i.Linear) :
    (execBlock block s).status = s.status := by
  induction block generalizing s with
  | nil => rfl
  | cons i block ih =>
      have hi := hlinear i (by simp)
      have ht : ∀ j ∈ block, j.Linear := fun j hj => hlinear j (by simp [hj])
      rw [execBlock_cons, ih _ ht, execInstr_status_of_linear s hi]

/-- A block occupies a contiguous interval of the surrounding machine code. -/
def CodeAt (code : Code) (pc : Nat) (block : Code) : Prop :=
  ∀ j, j < block.length → code[pc + j]? = block[j]?

namespace CodeAt

@[simp] theorem nil (code : Code) (pc : Nat) : CodeAt code pc [] := by
  intro j hj
  simp at hj

theorem refl (block : Code) : CodeAt block 0 block := by
  intro j _
  simp

theorem prefix_append (pre block suffix : Code) :
    CodeAt (pre ++ block ++ suffix) pre.length block := by
  intro j hj
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simpa using (List.getElem?_append_left (l₂ := suffix) hj)

theorem head {code : Code} {pc : Nat} {i : Instr} {block : Code}
    (h : CodeAt code pc (i :: block)) : code[pc]? = some i := by
  simpa using h 0 (by simp)

theorem tail {code : Code} {pc : Nat} {i : Instr} {block : Code}
    (h : CodeAt code pc (i :: block)) : CodeAt code (pc + 1) block := by
  intro j hj
  have he := h (j + 1) (by simp only [List.length_cons]; omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem cons {code : Code} {pc : Nat} {i : Instr} {block : Code}
    (hhead : code[pc]? = some i) (htail : CodeAt code (pc + 1) block) :
    CodeAt code pc (i :: block) := by
  intro j hj
  cases j with
  | zero => simpa using hhead
  | succ j =>
      have he := htail j (by simp only [List.length_cons] at hj; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem append_left {code a b : Code} {pc : Nat}
    (h : CodeAt code pc (a ++ b)) : CodeAt code pc a := by
  intro j hj
  exact (h j (by simp only [List.length_append]; omega)).trans
    (List.getElem?_append_left hj)

theorem append_right {code a b : Code} {pc : Nat}
    (h : CodeAt code pc (a ++ b)) : CodeAt code (pc + a.length) b := by
  intro j hj
  have he := h (a.length + j) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at he
  simpa [Nat.add_assoc] using he

theorem append {code a b : Code} {pc : Nat}
    (ha : CodeAt code pc a) (hb : CodeAt code (pc + a.length) b) :
    CodeAt code pc (a ++ b) := by
  intro j hj
  by_cases hja : j < a.length
  · rw [List.getElem?_append_left hja]
    exact ha j hja
  · rw [List.getElem?_append_right (by omega)]
    have hjb : j - a.length < b.length := by
      simp only [List.length_append] at hj
      omega
    have hp : pc + j = pc + a.length + (j - a.length) := by omega
    rw [hp]
    exact hb _ hjb

theorem append_iff {code a b : Code} {pc : Nat} :
    CodeAt code pc (a ++ b) ↔ CodeAt code pc a ∧ CodeAt code (pc + a.length) b :=
  ⟨fun h => ⟨h.append_left, h.append_right⟩, fun ⟨ha, hb⟩ => ha.append hb⟩

end CodeAt

/-- A linear block executes in exactly its length many transitions of the
machine's real `step`, starting from any running state at its first instruction. -/
theorem execBlock_exec {code block : Code} {s : State w}
    (hAt : CodeAt code s.pc block) (hlinear : ∀ i ∈ block, i.Linear)
    (hrun : s.status = .running) : Exec code block.length s (execBlock block s) := by
  induction block generalizing s with
  | nil => exact .refl s
  | cons i block ih =>
      have hi := hlinear i (by simp)
      have ht : ∀ j ∈ block, j.Linear := fun j hj => hlinear j (by simp [hj])
      have hs : step code s = some (execInstr i s) :=
        step_of_fetch hrun hAt.head
      have hat : CodeAt code (execInstr i s).pc block := by
        rw [execInstr_pc_of_linear s hi]
        exact hAt.tail
      have hr : (execInstr i s).status = .running :=
        (execInstr_status_of_linear s hi).trans hrun
      exact .cons hs (ih hat ht hr)

end Ram
