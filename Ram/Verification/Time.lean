/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalMeasured.Deterministic
import Ram.Verification.Total

/-!
# Separate functional correctness and execution-time bounds

`TimeBound` bounds every completed measured execution; it does not by itself
assert termination. `TotalContract.with_timeBound` combines it with a separate
safe total-correctness proof of the same statement. The resulting `Contract`
uses the existing compiler-derived counts and compilation theorem.

This separates behavior from cost without adding a cost field to executable
states or treating a proposed bound as an instruction price. Determinism gives
the converse decomposition for existing contracts, so clients can reuse them.
-/

namespace Ram.Source

/-- A conditional bound on the actual count of every completed execution.
Use with `TotalContract` to obtain termination as well as a time bound. -/
def TimeBound (control : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P : State w → Prop) (bound : State w → Nat) : Prop :=
  ∀ s, P s → ∀ steps t,
    LocalMeasuredExec control program heapLimit depth stmt steps s t → steps ≤ bound s

namespace TimeBound

variable {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P P' : State w → Prop} {bound bound' : State w → Nat}

theorem consequence (h : TimeBound control program heapLimit depth stmt P bound)
    (pre : ∀ s, P' s → P s) (budget : ∀ s, P' s → bound s ≤ bound' s) :
    TimeBound control program heapLimit depth stmt P' bound' :=
  fun s hs steps t hx => Nat.le_trans (h s (pre s hs) steps t hx) (budget s hs)

theorem mono_budget (h : TimeBound control program heapLimit depth stmt P bound)
    (budget : ∀ s, P s → bound s ≤ bound' s) :
    TimeBound control program heapLimit depth stmt P bound' :=
  h.consequence (fun _ hs => hs) budget

/-- A sequence adds costs at its actual entry and intermediate states.
The functional contract supplies the intermediate assertion, not a time budget. -/
theorem seq {a b : Stmt} {R : State w → Prop}
    {firstBound secondBound : State w → Nat}
    (functional : TotalContract program heapLimit depth a P R)
    (first : TimeBound control program heapLimit depth a P firstBound)
    (second : TimeBound control program heapLimit depth b R secondBound)
    (budget : ∀ s, P s → ∀ middle, R middle →
      firstBound s + secondBound middle ≤ bound s) :
    TimeBound control program heapLimit depth (.seq a b) P bound := by
  intro s hs steps t hx
  cases hx with
  | seq ha hb =>
    obtain ⟨middle, hm, hr⟩ := functional s hs
    have he := hm.deterministic ha.erase
    subst middle
    exact Nat.le_trans (Nat.add_le_add (first s hs _ _ ha) (second _ hr _ _ hb))
      (budget s hs _ hr)

/-- Branch costs retain the actual guard decision and generated jumps. -/
theorem ite {condition : Expr} {yes no : Stmt}
    {yesBound noBound : State w → Nat}
    (ifTrue : TimeBound control program heapLimit depth yes
      (fun s => P s ∧ s.eval condition ≠ 0) yesBound)
    (ifFalse : TimeBound control program heapLimit depth no
      (fun s => P s ∧ s.eval condition = 0) noBound) :
    TimeBound control program heapLimit depth (.ite condition yes no) P
      (fun s => (condition.compile (ABI.scratch control)).length + 1 +
        if s.eval condition = 0 then noBound s else yesBound s + 1) := by
  intro s hs steps t hx
  cases hx with
  | iteTrue _ hc hb =>
    have h := ifTrue s ⟨hs, hc⟩ _ _ hb
    simp only [if_neg hc]
    omega
  | iteFalse _ hc hb =>
    have h := ifFalse s ⟨hs, hc⟩ _ _ hb
    simp only [if_pos hc]
    omega

end TimeBound

/-- Forget the postcondition of an existing contract without reproving cost.
Count uniqueness ensures the bound applies to every completed execution. -/
theorem Contract.timeBound {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat}
    (h : Contract control program heapLimit depth stmt P Q bound) :
    TimeBound control program heapLimit depth stmt P bound := by
  intro s hs steps t hx
  obtain ⟨count, finish, execution, _, budget⟩ := h s hs
  exact (execution.deterministic hx).1 ▸ budget

theorem RelContract.timeBound {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop} {bound : State w → Nat}
    (h : RelContract control program heapLimit depth stmt P Q bound) :
    TimeBound control program heapLimit depth stmt P bound := by
  intro s hs steps t hx
  obtain ⟨count, finish, execution, _, budget⟩ := h s hs
  exact (execution.deterministic hx).1 ▸ budget

/-- Combine independent functional and time proofs for the same safe run. -/
theorem TotalContract.with_timeBound {control heapLimit depth : Nat} {program : Program}
    {stmt : Stmt} {P Q : State w → Prop} {bound : State w → Nat}
    (h : TotalContract program heapLimit depth stmt P Q)
    (cost : TimeBound control program heapLimit depth stmt P bound) :
    Contract control program heapLimit depth stmt P Q bound := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  obtain ⟨steps, measured⟩ := hx.exists_localMeasured control
  exact ⟨steps, t, measured, hq, cost s hs steps t measured⟩

theorem TotalRelContract.with_timeBound {control heapLimit depth : Nat} {program : Program}
    {stmt : Stmt} {P : State w → Prop} {Q : State w → State w → Prop}
    {bound : State w → Nat} (h : TotalRelContract program heapLimit depth stmt P Q)
    (cost : TimeBound control program heapLimit depth stmt P bound) :
    RelContract control program heapLimit depth stmt P Q bound := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  obtain ⟨steps, measured⟩ := hx.exists_localMeasured control
  exact ⟨steps, t, measured, hq, cost s hs steps t measured⟩

/-- Separating behavior and time loses none of the existing total contract. -/
theorem contract_iff_total_and_timeBound {control heapLimit depth : Nat} {program : Program}
    {stmt : Stmt} {P Q : State w → Prop} {bound : State w → Nat} :
    Contract control program heapLimit depth stmt P Q bound ↔
      TotalContract program heapLimit depth stmt P Q ∧
        TimeBound control program heapLimit depth stmt P bound :=
  ⟨fun h => ⟨h.total, h.timeBound⟩, fun h => h.1.with_timeBound h.2⟩

theorem relContract_iff_total_and_timeBound {control heapLimit depth : Nat}
    {program : Program} {stmt : Stmt} {P : State w → Prop}
    {Q : State w → State w → Prop} {bound : State w → Nat} :
    RelContract control program heapLimit depth stmt P Q bound ↔
      TotalRelContract program heapLimit depth stmt P Q ∧
        TimeBound control program heapLimit depth stmt P bound :=
  ⟨fun h => ⟨h.total, h.timeBound⟩, fun h => h.1.with_timeBound h.2⟩

end Ram.Source
