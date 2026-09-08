/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.ForIn
import Complexity.Computability.Ram.Source.State.Frame
import Complexity.Computability.Ram.Verification.Total

/-!
# Total correctness of iteration with an arbitrary body

The existing `Stmt.forIn` loads an element, executes its body, and advances two
cursor registers. The state descriptions below follow those actual assignments
and their evaluation order. They introduce no new execution or array model.

The loop rule uses an arbitrary source-state invariant and the existing natural
variant rule. The body may change shared memory and input/output, and later
iterations read the resulting memory. Load safety and the body postcondition are
required only at an actual nonzero guard. Cursor arithmetic remains modular;
there is no implicit nonoverflow premise or read-only frame.
-/

namespace Ram.Source.ForIn

/-- The actual element load observes the current heap before assigning its local. -/
def loadedState (pointer element : Reg) (s : State w) : State w :=
  s.setReg element (s.mem (s.regs pointer))

/-- Advance the pointer, then decrement the remaining word in that updated state. -/
def advanceState (pointer remaining : Reg) (s : State w) : State w :=
  let advanced := s.setReg pointer (s.regs pointer + 1)
  advanced.setReg remaining (advanced.regs remaining - 1)

/-- Setup evaluates length after assigning the base address to the pointer. -/
def initialState (pointer remaining : Reg) (base length : Expr) (s : State w) : State w :=
  let initialized := s.setReg pointer (s.eval base)
  initialized.setReg remaining (initialized.eval length)

/-- The two cursor assignments realize their sequential state description,
including when the two destination indices coincide. -/
theorem advance_safe (pointer remaining : Reg) {program : Program} {heapLimit depth : Nat}
    (s : State w) :
    SafeExec program heapLimit depth
      (.seq (.assign pointer (.bin .add (.var pointer) (.const 1)))
        (.assign remaining (.bin .sub (.var remaining) (.const 1))))
      s (advanceState pointer remaining s) :=
  .seq (.assign ⟨trivial, trivial⟩) (.assign ⟨trivial, trivial⟩)

/-- Distinct cursor locals make the second assignment decrement the old count. -/
theorem advance_remaining (pointer remaining : Reg) (distinct : pointer ≠ remaining)
    (s : State w) :
    (advanceState pointer remaining s).regs remaining = s.regs remaining - 1 := by
  simp [advanceState, State.setReg, Ne.symm distinct]

/-- Loading a distinct element local does not change the remaining count. -/
theorem loaded_remaining (pointer remaining element : Reg) (distinct : element ≠ remaining)
    (s : State w) :
    (loadedState pointer element s).regs remaining = s.regs remaining := by
  simp [loadedState, State.setReg, Ne.symm distinct]

/-- A safe load, arbitrary safe body and the actual cursor assignments compose.
The body's real shared effects are retained in the final state. -/
theorem body_safe (pointer remaining element : Reg) {program : Program}
    {heapLimit depth : Nat} {body : Stmt} {s middle : State w}
    (address : (s.regs pointer).toNat < heapLimit)
    (execution : SafeExec program heapLimit depth body (loadedState pointer element s) middle) :
    SafeExec program heapLimit depth (Stmt.forInBody pointer remaining element body)
      s (advanceState pointer remaining middle) :=
  .seq (.assign ⟨trivial, address⟩)
    (.seq execution (advance_safe pointer remaining middle))

/-- An arbitrary completed body preserving the count is followed by one actual
decrement. No shared-state preservation or body termination is assumed here. -/
theorem body_remaining (pointer remaining element : Reg) {body : Stmt} {program : Program}
    {heapLimit depth : Nat} (pointer_ne_remaining : pointer ≠ remaining)
    (element_ne_remaining : element ≠ remaining)
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs remaining = s.regs remaining)
    {s t : State w}
    (h : SafeExec program heapLimit depth
      (Stmt.forInBody pointer remaining element body) s t) :
    t.regs remaining = s.regs remaining - 1 := by
  cases h with
  | seq loaded rest =>
    cases loaded with
    | assign _ =>
      cases rest with
      | seq inner advanced =>
        rw [advanced.deterministic (advance_safe pointer remaining
          (program := program) (heapLimit := heapLimit) (depth := depth) _),
          advance_remaining pointer remaining pointer_ne_remaining, preserves inner]
        exact congrArg (fun value => value - 1)
          (loaded_remaining pointer remaining element element_ne_remaining s)

end Ram.Source.ForIn

namespace Ram.Source.Verification.TotalWP

variable {w heapLimit depth : Nat} {program : Program} {body : Stmt}
  {s : State w} {post : State w → Prop}

/-- Verify an already-initialized iteration with any state invariant and body.
The invariant holds before the element load, not automatically after it. The
body preserves the loaded state's count and establishes the invariant after
the actual cursor assignments; its memory and stream effects are unrestricted. -/
theorem forInLoop (pointer remaining element : Reg) (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining) (element_ne_remaining : element ≠ remaining)
    (invariant : State w → Prop)
    (reads : ∀ current, invariant current → current.regs remaining ≠ 0 →
      (current.regs pointer).toNat < heapLimit)
    (implementation : ∀ current, invariant current → current.regs remaining ≠ 0 →
      TotalWP program heapLimit depth body
        (fun middle => invariant (ForIn.advanceState pointer remaining middle) ∧
          middle.regs remaining = (ForIn.loadedState pointer element current).regs remaining)
        (ForIn.loadedState pointer element current))
    (pre : invariant s)
    (continuation : ∀ finish, invariant finish → finish.regs remaining = 0 → post finish) :
    TotalWP program heapLimit depth (Stmt.forInLoop pointer remaining element body) post s := by
  change TotalWP program heapLimit depth
    (.while (.var remaining) (Stmt.forInBody pointer remaining element body)) post s
  refine while_variant invariant (fun current => (current.regs remaining).toNat)
    (fun _ _ => trivial) ?_ pre continuation
  intro current invariant' nonzero
  obtain ⟨middle, execution, invariant'', count⟩ := implementation current invariant' nonzero
  refine ⟨ForIn.advanceState pointer remaining middle,
    ForIn.body_safe pointer remaining element (reads current invariant' nonzero) execution,
    invariant'', ?_⟩
  change ((ForIn.advanceState pointer remaining middle).regs remaining).toNat <
    (current.regs remaining).toNat
  rw [ForIn.advance_remaining pointer remaining pointer_ne_remaining, count,
    ForIn.loaded_remaining pointer remaining element element_ne_remaining]
  have positive : 0 < (current.regs remaining).toNat :=
    Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
  have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have one_le : (1 : Word w).toNat ≤ (current.regs remaining).toNat := by omega
  change (BinOp.eval .sub (current.regs remaining) 1).toNat <
    (current.regs remaining).toNat
  rw [BinOp.eval_sub_toNat_of_le _ _ one_le, one]
  omega

/-- Verify descriptor setup followed by the same arbitrary-body iteration.
The base expression is evaluated first; length safety and the initial invariant
refer to the resulting sequential bindings, without an implicit snapshot. -/
theorem forIn (pointer remaining element : Reg) {base length : Expr} (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining) (element_ne_remaining : element ≠ remaining)
    (invariant : State w → Prop)
    (reads : ∀ current, invariant current → current.regs remaining ≠ 0 →
      (current.regs pointer).toNat < heapLimit)
    (implementation : ∀ current, invariant current → current.regs remaining ≠ 0 →
      TotalWP program heapLimit depth body
        (fun middle => invariant (ForIn.advanceState pointer remaining middle) ∧
          middle.regs remaining = (ForIn.loadedState pointer element current).regs remaining)
        (ForIn.loadedState pointer element current))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg pointer (s.eval base)).regs (s.setReg pointer (s.eval base)).mem)
    (pre : invariant (ForIn.initialState pointer remaining base length s))
    (continuation : ∀ finish, invariant finish → finish.regs remaining = 0 → post finish) :
    TotalWP program heapLimit depth (Stmt.forIn pointer remaining element base length body)
      post s := by
  obtain ⟨finish, execution, result⟩ :=
    forInLoop pointer remaining element hw pointer_ne_remaining element_ne_remaining
      invariant reads implementation pre continuation
  exact ⟨finish, .seq (.assign baseReads) (.seq (.assign lengthReads) execution), result⟩

/-- Verify a traversal using a mathematical iteration index and an arbitrary
payload invariant. The rule maintains the private pointer and remaining count;
the payload need only describe the caller's values, heap and other effects.

The body starts after the real load from the current heap at `origin + i`, and
establishes the next payload after the actual cursor assignments. Preserving
the two cursor locals is a semantic endpoint premise: writing and restoring
them is allowed. Neither the body nor the payload must preserve shared state.

Setup evaluates length after the pointer assignment. Only executed positions
require safe addresses; the unused final pointer may wrap at the word boundary. -/
theorem forIn_indexed (pointer remaining element : Reg) {base length : Expr}
    (origin : Word w) (n : Nat) (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining) (element_ne_pointer : element ≠ pointer)
    (element_ne_remaining : element ≠ remaining)
    (invariant : Nat → State w → Prop)
    (reads : ∀ i current, i < n → invariant i current →
      (origin + BitVec.ofNat w i).toNat < heapLimit)
    (preserves : ∀ {entry finish : State w}, SafeExec program heapLimit depth body entry finish →
      finish.regs pointer = entry.regs pointer ∧ finish.regs remaining = entry.regs remaining)
    (implementation : ∀ i current, i < n → invariant i current →
      TotalWP program heapLimit depth body
        (fun middle => invariant (i + 1) (ForIn.advanceState pointer remaining middle))
        (current.setReg element (current.mem (origin + BitVec.ofNat w i))))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg pointer (s.eval base)).regs (s.setReg pointer (s.eval base)).mem)
    (base_eq : s.eval base = origin)
    (count_eq : ((s.setReg pointer (s.eval base)).eval length).toNat = n)
    (pre : invariant 0 (ForIn.initialState pointer remaining base length s))
    (continuation : ∀ finish, invariant n finish → post finish) :
    TotalWP program heapLimit depth (Stmt.forIn pointer remaining element base length body)
      post s := by
  let loopInvariant (current : State w) : Prop :=
    ∃ i, i ≤ n ∧ current.regs pointer = origin + BitVec.ofNat w i ∧
      (current.regs remaining).toNat = n - i ∧ invariant i current
  refine forIn pointer remaining element hw pointer_ne_remaining element_ne_remaining
    loopInvariant ?_ ?_ baseReads lengthReads ?_ ?_
  · rintro current ⟨i, _, pointer_eq, count, payload⟩ nonzero
    have positive : 0 < (current.regs remaining).toNat :=
      Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
    have inside : i < n := by omega
    simpa only [pointer_eq] using reads i current inside payload
  · rintro current ⟨i, _, pointer_eq, count, payload⟩ nonzero
    have positive : 0 < (current.regs remaining).toNat :=
      Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
    have inside : i < n := by omega
    have loaded : ForIn.loadedState pointer element current =
        current.setReg element (current.mem (origin + BitVec.ofNat w i)) := by
      simp only [ForIn.loadedState, pointer_eq]
    obtain ⟨middle, execution, next⟩ := implementation i current inside payload
    have execution' : SafeExec program heapLimit depth body
        (ForIn.loadedState pointer element current) middle := by
      simpa only [loaded] using execution
    have preserved := preserves execution'
    have middle_pointer : middle.regs pointer = current.regs pointer := by
      simpa [ForIn.loadedState, State.setReg, Ne.symm element_ne_pointer] using preserved.1
    have middle_remaining : middle.regs remaining = current.regs remaining := by
      simpa [ForIn.loadedState, State.setReg, Ne.symm element_ne_remaining] using preserved.2
    refine ⟨middle, execution', ?_, preserved.2⟩
    refine ⟨i + 1, by omega, ?_, ?_, next⟩
    · simp [ForIn.advanceState, State.setReg, pointer_ne_remaining, middle_pointer,
        pointer_eq, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [ForIn.advance_remaining pointer remaining pointer_ne_remaining, middle_remaining]
      have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
      have one_le : (1 : Word w).toNat ≤ (current.regs remaining).toNat := by omega
      change (BinOp.eval .sub (current.regs remaining) 1).toNat = n - (i + 1)
      rw [BinOp.eval_sub_toNat_of_le _ _ one_le, one, count]
      omega
  · refine ⟨0, Nat.zero_le _, ?_, ?_, pre⟩
    · simpa [ForIn.initialState, State.setReg, pointer_ne_remaining] using base_eq
    · simpa [ForIn.initialState, State.setReg] using count_eq
  · rintro finish ⟨i, index_le, _, count, payload⟩ zero
    have last : i = n := by
      rw [zero] at count
      change 0 = n - i at count
      omega
    subst i
    exact continuation finish payload

/-- Verify an indexed traversal whose mathematical payload ignores the two
private cursor locals. The body establishes its payload at its own endpoint;
the shared rule transports it through setup and cursor advance using ordinary
local frames. Those generated assignments preserve shared state, but no such
restriction is imposed on the body or on its actual heap and I/O effects. -/
theorem forIn_indexed_of_frame (pointer remaining element : Reg) {base length : Expr}
    (origin : Word w) (n : Nat) (hw : 0 < w)
    (pointer_ne_remaining : pointer ≠ remaining) (element_ne_pointer : element ≠ pointer)
    (element_ne_remaining : element ≠ remaining)
    (invariant : Nat → State w → Prop)
    (stable : ∀ i {current next : State w}, State.LocalFrame {pointer, remaining} current next →
      invariant i current → invariant i next)
    (reads : ∀ i current, i < n → invariant i current →
      (origin + BitVec.ofNat w i).toNat < heapLimit)
    (preserves : ∀ {entry finish : State w}, SafeExec program heapLimit depth body entry finish →
      finish.regs pointer = entry.regs pointer ∧ finish.regs remaining = entry.regs remaining)
    (implementation : ∀ i current, i < n → invariant i current →
      TotalWP program heapLimit depth body (invariant (i + 1))
        (current.setReg element (current.mem (origin + BitVec.ofNat w i))))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg pointer (s.eval base)).regs (s.setReg pointer (s.eval base)).mem)
    (base_eq : s.eval base = origin)
    (count_eq : ((s.setReg pointer (s.eval base)).eval length).toNat = n)
    (pre : invariant 0 s)
    (continuation : ∀ finish, invariant n finish → post finish) :
    TotalWP program heapLimit depth (Stmt.forIn pointer remaining element base length body)
      post s := by
  have updates (current : State w) (address count : Word w) :
      State.LocalFrame {pointer, remaining} current
        ((current.setReg pointer address).setReg remaining count) := by
    exact ((State.LocalFrame.setReg current pointer address).trans
      (State.LocalFrame.setReg (current.setReg pointer address) remaining count)).mono
        (by intro r hr; simpa [or_comm] using hr)
  refine forIn_indexed pointer remaining element origin n hw pointer_ne_remaining
    element_ne_pointer element_ne_remaining invariant reads preserves ?_
    baseReads lengthReads base_eq count_eq (stable 0 (updates s _ _) pre) continuation
  intro i current inside payload
  exact (implementation i current inside payload).mono_post
    (fun middle next => stable (i + 1) (updates middle _ _) next)

end Ram.Source.Verification.TotalWP
