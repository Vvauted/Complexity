/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Amortized

/-!
# Changing and combining amortized potentials

These rules retain the same statement, precondition, relational postcondition,
and witnessed machine execution. Potential conversion is expressed entirely
with natural-number addition, retaining both initial and final credit.
-/

namespace Ram.Source.AmortizedContract

variable {w control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P : State w → Prop} {R : State w → State w → Prop}
variable {potential charge potential' charge' : State w → Nat}

/-- Change the potential and charge when their cross-added accounting condition
holds on the existing relational contract. No execution is changed or repriced. -/
theorem potential_consequence
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (account : ∀ entry final, P entry → R entry final →
      charge entry + potential entry + potential' final ≤
        charge' entry + potential' entry + potential final) :
    AmortizedContract control program heapLimit depth stmt P R potential' charge' := by
  intro entry hp
  obtain ⟨steps, final, hx, hr, hb⟩ := h entry hp
  have ha := account entry final hp hr
  exact ⟨steps, final, hx, hr, by omega⟩

/-- Add another potential, paying for any growth by an additional charge.
Both potentials remain available at the final state for later composition. -/
theorem add_potential
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (extraPotential extraCharge : State w → Nat)
    (growth : ∀ entry final, P entry → R entry final →
      extraPotential final ≤ extraCharge entry + extraPotential entry) :
    AmortizedContract control program heapLimit depth stmt P R
      (fun s => potential s + extraPotential s)
      (fun s => charge s + extraCharge s) := by
  apply h.potential_consequence
  intro entry final hp hr
  have hg := growth entry final hp hr
  omega

/-- A nonincreasing additional potential needs no additional charge. -/
theorem add_nonincreasing_potential
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (extraPotential : State w → Nat)
    (nonincreasing : ∀ entry final, P entry → R entry final →
      extraPotential final ≤ extraPotential entry) :
    AmortizedContract control program heapLimit depth stmt P R
      (fun s => potential s + extraPotential s) charge := by
  simpa only [Nat.add_zero] using
    h.add_potential extraPotential (fun _ => 0)
      (fun entry final hp hr => by
        simpa only [Nat.zero_add] using nonincreasing entry final hp hr)

end Ram.Source.AmortizedContract
