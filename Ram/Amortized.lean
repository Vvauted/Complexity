/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Loop.Sum

/-!
# Amortized contracts for actual compiled execution

Potential is proof-only credit attached to the ordinary source state. An
operation must prove `steps + potential final ≤ charge entry + potential entry`
for its existing `LocalMeasuredExec`: charges never define runtime steps.

Keeping the final potential on the left makes sequential cancellation sound
over natural numbers, without truncated subtraction. Relational postconditions
retain the actual entry state; later charges may depend on the intermediate
state. Loop rules also keep the final potential, so a proved workload can be
composed with the next workload without discarding its unused credit.
-/

namespace Ram.Source

/-- A total relational contract with a nonnegative, state-dependent potential.
The charge is an upper bound to justify, not a price assigned to instructions. -/
def AmortizedContract (control : Nat) (program : Program) (heapLimit depth : Nat)
    (stmt : Stmt) (P : State w → Prop) (R : State w → State w → Prop)
    (potential charge : State w → Nat) : Prop :=
  ∀ entry, P entry → ∃ steps final,
    LocalMeasuredExec control program heapLimit depth stmt steps entry final ∧
      R entry final ∧ steps + potential final ≤ charge entry + potential entry

namespace AmortizedContract

variable {w control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P P' : State w → Prop} {R R' : State w → State w → Prop}
variable {potential charge charge' bound : State w → Nat}

/-- Reuse an ordinary relational execution bound and prove its potential
accounting using the same entry and final states. -/
theorem of_relContract
    (h : RelContract control program heapLimit depth stmt P R bound)
    (account : ∀ entry final, P entry → R entry final →
      bound entry + potential final ≤ charge entry + potential entry) :
    AmortizedContract control program heapLimit depth stmt P R potential charge := by
  intro entry hp
  obtain ⟨steps, final, hx, hr, hb⟩ := h entry hp
  exact ⟨steps, final, hx, hr,
    (Nat.add_le_add_right hb _).trans (account entry final hp hr)⟩

/-- Existing ghost-entry contracts, including those proved by the verification
condition tactic, can establish an amortized operation directly. -/
theorem of_contract
    (h : ∀ entry, P entry → Contract control program heapLimit depth stmt
      (fun s => s = entry) (R entry) (fun _ => bound entry))
    (account : ∀ entry final, P entry → R entry final →
      bound entry + potential final ≤ charge entry + potential entry) :
    AmortizedContract control program heapLimit depth stmt P R potential charge :=
  of_relContract (RelContract.iff_entry.mpr h) account

/-- Strengthen the precondition, weaken the entry-related postcondition, or
increase the charge while retaining exactly the same witnessed execution. -/
theorem consequence
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (pre : ∀ s, P' s → P s)
    (post : ∀ s t, P' s → R s t → R' s t)
    (budget : ∀ s, P' s → charge s ≤ charge' s) :
    AmortizedContract control program heapLimit depth stmt P' R' potential charge' := by
  intro s hs
  obtain ⟨steps, t, hx, hr, hb⟩ := h s (pre s hs)
  exact ⟨steps, t, hx, post s t hs hr,
    hb.trans (Nat.add_le_add_right (budget s hs) _)⟩

theorem mono_post
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (post : ∀ s t, P s → R s t → R' s t) :
    AmortizedContract control program heapLimit depth stmt P R' potential charge :=
  h.consequence (fun _ hp => hp) post (fun _ _ => Nat.le_refl _)

theorem mono_charge
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (budget : ∀ s, P s → charge s ≤ charge' s) :
    AmortizedContract control program heapLimit depth stmt P R potential charge' :=
  h.consequence (fun _ hp => hp) (fun _ _ _ hr => hr) budget

/-- Nonnegative final potential can be forgotten to obtain an ordinary total
contract, with initial potential explicitly included in its machine budget. -/
theorem toRelContract
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge) :
    RelContract control program heapLimit depth stmt P R
      (fun s => charge s + potential s) := by
  intro s hs
  obtain ⟨steps, t, hx, hr, hb⟩ := h s hs
  refine ⟨steps, t, hx, hr, ?_⟩
  change steps ≤ charge s + potential s
  omega

/-- Extract the usual user-facing contract and its existing checked-compiler
connection, without pretending that initial stored potential was free. -/
theorem toContract {Q : State w → Prop}
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (post : ∀ entry final, P entry → R entry final → Q final) :
    Contract control program heapLimit depth stmt P Q
      (fun s => charge s + potential s) :=
  h.toRelContract.toContract post

/-- Capture the complete initial state as a ghost parameter. This also allows
loop invariants and their final assertions to refer to the loop's entry state. -/
theorem with_entry
    (h : ∀ entry, P entry →
      AmortizedContract control program heapLimit depth stmt (fun s => s = entry)
        (fun _ t => R entry t) potential (fun _ => charge entry)) :
    AmortizedContract control program heapLimit depth stmt P R potential charge := by
  intro s hs
  exact h s hs s rfl

/-- Charges for the second statement are evaluated at its real intermediate
state and may also remember the original entry. The shared potential cancels,
but the final potential remains available to a subsequent composition. -/
theorem seq {a b : Stmt} {Q : State w → State w → Prop}
    {firstCharge : State w → Nat} {secondCharge : State w → State w → Nat}
    (first : AmortizedContract control program heapLimit depth a P R potential firstCharge)
    (second : ∀ entry, P entry →
      AmortizedContract control program heapLimit depth b (R entry)
        (fun _ t => Q entry t) potential (secondCharge entry))
    (compatible : ∀ entry middle, P entry → R entry middle →
      firstCharge entry + secondCharge entry middle ≤ charge entry) :
    AmortizedContract control program heapLimit depth (.seq a b) P Q potential charge := by
  intro s hs
  obtain ⟨na, middle, ha, hm, hna⟩ := first s hs
  obtain ⟨nb, t, hb, hq, hnb⟩ := second s hs middle hm
  have hc := compatible s middle hs hm
  exact ⟨na + nb, t, .seq ha hb, hq, by omega⟩

/-- A state-independent charge for the second statement needs no separate
compatibility calculation; its postcondition still remembers the first entry. -/
theorem seq_const {a b : Stmt} {Q : State w → State w → Prop} {secondCharge : Nat}
    (first : AmortizedContract control program heapLimit depth a P R potential charge)
    (second : ∀ entry, P entry →
      AmortizedContract control program heapLimit depth b (R entry)
        (fun _ t => Q entry t) potential (fun _ => secondCharge)) :
    AmortizedContract control program heapLimit depth (.seq a b) P Q potential
      (fun s => charge s + secondCharge) :=
  first.seq second (fun _ _ _ _ => Nat.le_refl _)

/-- The remaining charge pays for each guard, amortized body charge, and
back-edge, then the final guard. Termination follows from strict decrease of
`remaining + potential`; a separate termination variant is unnecessary.
The result retains the final potential rather than only an ordinary step bound. -/
theorem while_potential {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (potential remaining bodyCharge : State w → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (exitBudget : ∀ s, invariant s → s.eval condition = 0 →
      Contract.guardCost control condition ≤ remaining s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      AmortizedContract control program heapLimit depth body (fun entry => entry = s)
        (fun _ t => invariant t ∧
          Contract.guardCost control condition + bodyCharge s + 1 + remaining t ≤ remaining s)
        potential (fun _ => bodyCharge s)) :
    AmortizedContract control program heapLimit depth (.while condition body) invariant
      (fun _ t => invariant t ∧ t.eval condition = 0) potential remaining := by
  have loop : ∀ k s, remaining s + potential s = k → invariant s →
      ∃ steps t, LocalMeasuredExec control program heapLimit depth
        (.while condition body) steps s t ∧
        (invariant t ∧ t.eval condition = 0) ∧
          steps + potential t ≤ remaining s + potential s := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s hk hs
        by_cases hz : s.eval condition = 0
        · refine ⟨_, s, .whileFalse (reads s hs) hz, ⟨hs, hz⟩, ?_⟩
          exact Nat.add_le_add_right (exitBudget s hs hz) _
        · obtain ⟨bodySteps, middle, hbody, ⟨hmid, hc⟩, hb⟩ := iteration s hs hz s rfl
          change bodySteps + potential middle ≤ bodyCharge s + potential s at hb
          have hlt : remaining middle + potential middle < k := by omega
          obtain ⟨restSteps, t, hrest, hpost, hrestBudget⟩ :=
            ih (remaining middle + potential middle) hlt middle rfl hmid
          refine ⟨_, t, .whileTrue (reads s hs) hz hbody hrest, hpost, ?_⟩
          change Contract.guardCost control condition + bodySteps + 1 + restSteps +
            potential t ≤ remaining s + potential s
          omega
  intro s hs
  exact loop (remaining s + potential s) s rfl hs

/-- A decreasing natural variant and a uniform amortized body charge give a
linear aggregate charge. Actual expensive iterations may spend credit stored
by earlier iterations; the final potential is still retained in the result. -/
theorem while_linear {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant potential : State w → Nat) (bodyCharge : Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      AmortizedContract control program heapLimit depth body (fun entry => entry = s)
        (fun _ t => invariant t ∧ variant t < variant s) potential (fun _ => bodyCharge)) :
    AmortizedContract control program heapLimit depth (.while condition body) invariant
      (fun _ t => invariant t ∧ t.eval condition = 0) potential
      (fun s => variant s * (Contract.guardCost control condition + bodyCharge + 1) +
        Contract.guardCost control condition) := by
  apply while_potential invariant potential
    (fun s => variant s * (Contract.guardCost control condition + bodyCharge + 1) +
      Contract.guardCost control condition) (fun _ => bodyCharge) reads
  · intro s _ _
    omega
  · intro s hs hz
    apply (iteration s hs hz).mono_post
    intro _ t _ ht
    refine ⟨ht.1, ?_⟩
    have hmul := Nat.mul_le_mul_right (Contract.guardCost control condition + bodyCharge + 1)
      (Nat.succ_le_of_lt ht.2)
    rw [Nat.succ_mul] at hmul
    omega

/-- Variable amortized charges sum over possible variant values using the
existing mathlib finite-sum budget. Skipped values need no monotonicity of
the charge function, since every reserved summand is nonnegative. -/
theorem while_sum {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant potential : State w → Nat) (bodyCharge : Nat → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      AmortizedContract control program heapLimit depth body (fun entry => entry = s)
        (fun _ t => invariant t ∧ variant t < variant s) potential
        (fun _ => bodyCharge (variant s))) :
    AmortizedContract control program heapLimit depth (.while condition body) invariant
      (fun _ t => invariant t ∧ t.eval condition = 0) potential
      (fun s => Contract.sumBudget control condition bodyCharge (variant s)) := by
  apply while_potential invariant potential
    (fun s => Contract.sumBudget control condition bodyCharge (variant s))
    (fun s => bodyCharge (variant s)) reads
  · intro s _ _
    exact Nat.le_add_right _ _
  · intro s hs hz
    apply (iteration s hs hz).mono_post
    intro _ t _ ht
    exact ⟨ht.1, Contract.sumBudget_step_le control condition bodyCharge ht.2⟩

end AmortizedContract
end Ram.Source
