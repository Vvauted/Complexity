/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Amortized
import Ram.Verification

/-!
# Applying amortized contracts without losing stored credit

An amortized contract witnesses the same `LocalMeasuredExec` used by `WP`.
The continuation receives `fuel - steps` from that actual execution, retaining
both separately reserved fuel and the final state's potential. Initial
potential is explicitly included in the required budget; it is not free fuel.
The continuation may inspect the entry-related postcondition and need not be
monotone in the remaining budget.
-/

namespace Ram.Source.Verification.WP

variable {w n heapLimit depth fuel reserve : Nat} {program : Program} {stmt : Stmt}
variable {P : State w → Prop} {R : State w → State w → Prop}
variable {potential charge : State w → Nat}
variable {post : State w → Nat → Prop} {s : State w}

/-- Reuse a verified amortized operation while keeping its final potential in
addition to a chosen continuation reserve. Both are backed by real unused fuel. -/
theorem of_amortizedContract_reserve
    (contract : AmortizedContract n program heapLimit depth stmt P R potential charge)
    (pre : P s) (budget : charge s + potential s + reserve ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining,
      reserve + potential t ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel := by
  obtain ⟨steps, t, hx, hr, account⟩ := contract s pre
  exact ⟨steps, t, hx, by omega, continuation t hr _ (by omega)⟩

/-- Without choosing an explicit reserve, retain all budget beyond the
initial charge and potential, together with the final state's potential. -/
theorem of_amortizedContract
    (contract : AmortizedContract n program heapLimit depth stmt P R potential charge)
    (pre : P s) (budget : charge s + potential s ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining,
      fuel - (charge s + potential s) + potential t ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel :=
  of_amortizedContract_reserve (reserve := fuel - (charge s + potential s))
    contract pre (by omega) continuation

end Ram.Source.Verification.WP
