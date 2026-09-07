/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Contracts

/-!
# Budget-threading weakest preconditions

`WP` describes terminating execution, not partial correctness. Its
postcondition receives the unused part of the supplied budget. The sequence
rule passes exactly that remainder to the second statement; it never resets
the budget between statements.

The rewriting rules below symbolically execute ordinary statements, exposing
their real state updates, heap-read obligations, and generated-code counts.
For example, `simp only [WP.seq_iff, WP.assign_iff, WP.write_iff]` generates
the verification conditions of an assignment followed by a write. No tactic
engine or second cost semantics is involved.

Loops and calls deliberately have no unfolding simplification rule. Reuse a
proved contract through `WP.of_contract`; `WP.while_contract` also exposes the
existing invariant/potential rule directly. These interfaces retain safety,
termination, and every instruction included in the compiler-derived budget.
-/

namespace Ram.Source.Verification

/-- A resource-sensitive total weakest precondition. `fuel - steps` is the
actual unused budget after the same measured source execution used by the
compiler's soundness theorem. -/
def WP (n : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (post : State w → Nat → Prop) (s : State w) (fuel : Nat) : Prop :=
  ∃ steps t, LocalMeasuredExec n program heapLimit depth stmt steps s t ∧
    steps ≤ fuel ∧ post t (fuel - steps)

/-- An assertion may ignore excess remaining budget, but this property is
explicit: arbitrary predicates of the remainder need not be monotone. -/
def BudgetMonotone (post : State w → Nat → Prop) : Prop :=
  ∀ s a b, a ≤ b → post s a → post s b

namespace WP

variable {w n heapLimit depth fuel : Nat} {program : Program} {stmt : Stmt}
variable {post post' : State w → Nat → Prop} {s : State w}

theorem mono_post (h : WP n program heapLimit depth stmt post s fuel)
    (imp : ∀ t remaining, post t remaining → post' t remaining) :
    WP n program heapLimit depth stmt post' s fuel := by
  obtain ⟨steps, t, hx, hb, hp⟩ := h
  exact ⟨steps, t, hx, hb, imp t _ hp⟩

theorem mono_fuel {fuel' : Nat} (h : WP n program heapLimit depth stmt post s fuel)
    (hle : fuel ≤ fuel') (monotone : BudgetMonotone post) :
    WP n program heapLimit depth stmt post s fuel' := by
  obtain ⟨steps, t, hx, hb, hp⟩ := h
  exact ⟨steps, t, hx, Nat.le_trans hb hle, monotone t _ _ (by omega) hp⟩

@[simp] theorem skip_iff : WP n program heapLimit depth .skip post s fuel ↔ post s fuel := by
  constructor
  · rintro ⟨steps, t, hx, _, hp⟩
    cases hx
    exact hp
  · intro hp
    exact ⟨0, s, .skip, Nat.zero_le _, hp⟩

@[simp] theorem assign_iff {dst : Reg} {value : Expr} :
    WP n program heapLimit depth (.assign dst value) post s fuel ↔
      value.ReadsBelow heapLimit s.regs s.mem ∧
      LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.assign dst value) ≤ fuel ∧
      post (s.setReg dst (s.eval value))
        (fuel - LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program)
          (.assign dst value)) := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | assign reads => exact ⟨reads, hb, hp⟩
  · rintro ⟨reads, hb, hp⟩
    exact ⟨_, _, .assign reads, hb, hp⟩

@[simp] theorem store_iff {address value : Expr} :
    WP n program heapLimit depth (.store address value) post s fuel ↔
      address.ReadsBelow heapLimit s.regs s.mem ∧
      value.ReadsBelow heapLimit s.regs s.mem ∧
      (s.eval address).toNat < heapLimit ∧
      LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.store address value) ≤ fuel ∧
      post (s.setMem (s.eval address) (s.eval value))
        (fuel - LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program)
          (.store address value)) := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | store addressReads valueReads destination =>
        exact ⟨addressReads, valueReads, destination, hb, hp⟩
  · rintro ⟨addressReads, valueReads, destination, hb, hp⟩
    exact ⟨_, _, .store addressReads valueReads destination, hb, hp⟩

/-- Empty input makes the total weakest precondition false. A successful read
consumes one actual instruction and passes the tail to its continuation. -/
@[simp] theorem read_iff {dst : Reg} :
    WP n program heapLimit depth (.read dst) post s fuel ↔
      match s.input with
      | [] => False
      | value :: rest =>
          LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.read dst) ≤ fuel ∧
          post { s.setReg dst value with input := rest }
            (fuel - LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.read dst)) := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | read available => simpa only [available] using And.intro hb hp
  · intro h
    cases hi : s.input with
    | nil => simp only [hi] at h
    | cons value rest =>
        simp only [hi] at h
        exact ⟨_, _, .read hi, h.1, h.2⟩

@[simp] theorem write_iff {value : Expr} :
    WP n program heapLimit depth (.write value) post s fuel ↔
      value.ReadsBelow heapLimit s.regs s.mem ∧
      LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.write value) ≤ fuel ∧
      post { s with outputRev := s.eval value :: s.outputRev }
        (fuel - LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program) (.write value)) := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | write reads => exact ⟨reads, hb, hp⟩
  · rintro ⟨reads, hb, hp⟩
    exact ⟨_, _, .write reads, hb, hp⟩

/-- Exact budget threading through the actual intermediate state. This rule
needs no arbitrary split and no uniform bound over unrelated middle states. -/
@[simp] theorem seq_iff {first second : Stmt} :
    WP n program heapLimit depth (.seq first second) post s fuel ↔
      WP n program heapLimit depth first
        (fun middle remaining => WP n program heapLimit depth second post middle remaining)
        s fuel := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | seq ha hbExec =>
        refine ⟨_, _, ha, by omega, _, _, hbExec, by omega, ?_⟩
        simpa only [Nat.sub_sub] using hp
  · rintro ⟨na, middle, ha, hna, nb, t, hb, hnb, hp⟩
    refine ⟨na + nb, t, .seq ha hb, by omega, ?_⟩
    simpa only [Nat.sub_sub] using hp

/-- Guard evaluation and branching are charged before the selected branch.
The true branch also pays the compiler's skip-over-else jump. Moving that
known charge before the branch changes no execution or remaining budget. -/
@[simp] theorem ite_iff {condition : Expr} {yes no : Stmt} :
    WP n program heapLimit depth (.ite condition yes no) post s fuel ↔
      condition.ReadsBelow heapLimit s.regs s.mem ∧
      if s.eval condition = 0 then
        (condition.compile (ABI.scratch n)).length + 1 ≤ fuel ∧
        WP n program heapLimit depth no post s
          (fuel - ((condition.compile (ABI.scratch n)).length + 1))
      else
        (condition.compile (ABI.scratch n)).length + 1 + 1 ≤ fuel ∧
        WP n program heapLimit depth yes post s
          (fuel - ((condition.compile (ABI.scratch n)).length + 1 + 1)) := by
  constructor
  · rintro ⟨steps, t, hx, hb, hp⟩
    cases hx with
    | iteTrue reads condition body =>
        refine ⟨reads, ?_⟩
        rw [if_neg condition]
        refine ⟨by omega, _, _, body, by omega, ?_⟩
        simpa only [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    | iteFalse reads condition body =>
        refine ⟨reads, ?_⟩
        rw [if_pos condition]
        refine ⟨by omega, _, _, body, by omega, ?_⟩
        simpa only [Nat.sub_sub] using hp
  · rintro ⟨reads, h⟩
    by_cases hz : s.eval condition = 0
    · rw [if_pos hz] at h
      obtain ⟨hguard, nb, t, hb, hbudget, hp⟩ := h
      refine ⟨_, _, .iteFalse reads hz hb, by omega, ?_⟩
      simpa only [Nat.sub_sub] using hp
    · rw [if_neg hz] at h
      obtain ⟨hguard, nb, t, hb, hbudget, hp⟩ := h
      refine ⟨_, _, .iteTrue reads hz hb, by omega, ?_⟩
      simpa only [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

/-- Reuse any proved contract, including a loop or function-call contract.
Because its budget is only an upper bound, the continuation must hold for
every remainder at least as large as the guaranteed one. -/
theorem of_contract {P Q : State w → Prop} {bound : State w → Nat}
    (contract : Contract n program heapLimit depth stmt P Q bound)
    (pre : P s) (budget : bound s ≤ fuel)
    (continuation : ∀ t, Q t → ∀ remaining,
      fuel - bound s ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel := by
  obtain ⟨steps, t, hx, hq, hb⟩ := contract s pre
  exact ⟨steps, t, hx, Nat.le_trans hb budget,
    continuation t hq _ (by omega)⟩

/-- For monotone continuations it suffices to prove the assertion at the
guaranteed remainder, not at every possible amount of unused fuel. -/
theorem of_contract_mono {P Q : State w → Prop} {bound : State w → Nat}
    (contract : Contract n program heapLimit depth stmt P Q bound)
    (pre : P s) (budget : bound s ≤ fuel) (monotone : BudgetMonotone post)
    (continuation : ∀ t, Q t → post t (fuel - bound s)) :
    WP n program heapLimit depth stmt post s fuel :=
  of_contract contract pre budget
    (fun t hq remaining hremaining => monotone t _ remaining hremaining (continuation t hq))

/-- Discharge a loop verification condition with an invariant, potential, and
an already proved body contract. Positive real guard/back-edge work supplies
the strict descent needed for termination; no separate fuelled runner is used. -/
theorem while_contract {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (potential bodyBound : State w → Nat)
    (reads : ∀ t, invariant t → condition.ReadsBelow heapLimit t.regs t.mem)
    (exitBudget : ∀ t, invariant t → t.eval condition = 0 →
      (condition.compile (ABI.scratch n)).length + 1 ≤ potential t)
    (iteration : ∀ entry, invariant entry → entry.eval condition ≠ 0 →
      Contract n program heapLimit depth body (fun initial => initial = entry)
        (fun t => invariant t ∧
          (condition.compile (ABI.scratch n)).length + 1 + bodyBound entry + 1 +
            potential t ≤ potential entry) (fun _ => bodyBound entry))
    (pre : invariant s) (budget : potential s ≤ fuel)
    (continuation : ∀ t, invariant t ∧ t.eval condition = 0 → ∀ remaining,
      fuel - potential s ≤ remaining → post t remaining) :
    WP n program heapLimit depth (.while condition body) post s fuel :=
  of_contract (Contract.while_contract invariant potential bodyBound reads exitBudget iteration)
    pre budget continuation

end WP

/-- An ordinary total contract is exactly a weakest-precondition obligation
whose final assertion does not observe the unused budget. -/
theorem contract_iff {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat} :
    Contract n program heapLimit depth stmt P Q bound ↔
      ∀ s, P s → WP n program heapLimit depth stmt (fun t _ => Q t) s (bound s) := by
  constructor
  · intro contract s hs
    obtain ⟨steps, t, hx, hq, hb⟩ := contract s hs
    exact ⟨steps, t, hx, hb, hq⟩
  · intro vc s hs
    obtain ⟨steps, t, hx, hb, hq⟩ := vc s hs
    exact ⟨steps, t, hx, hq, hb⟩

/-- Start verification of a total contract. Apply this theorem, introduce the
entry state and precondition, then rewrite the mechanical `WP` rules. -/
theorem verify {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat}
    (conditions : ∀ s, P s →
      WP n program heapLimit depth stmt (fun t _ => Q t) s (bound s)) :
    Contract n program heapLimit depth stmt P Q bound := contract_iff.mpr conditions

/-- Relational postconditions can retain the entry state as a ghost without
putting that state, or the proof budget, into the executed program. -/
theorem verify_rel {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop} {bound : State w → Nat}
    (conditions : ∀ s, P s →
      WP n program heapLimit depth stmt (fun t _ => Q s t) s (bound s)) :
    RelContract n program heapLimit depth stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hb, hq⟩ := conditions s hs
  exact ⟨steps, t, hx, hq, hb⟩

end Ram.Source.Verification
