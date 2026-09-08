/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Amortized.WP
import Complexity.Computability.Ram.Verification.Composition

/-!
# Small contract-application automation

`ram_apply h` applies a supplied ordinary, relational, amortized, or recursive function
contract to the current WP goal. If the contract describes the first statement
of a sequence, it opens that sequence using the proved WP rule.

`ram_apply h reserving r` additionally leaves an additive budget obligation
and guarantees at least `r` actual remaining fuel in the continuation. Neither
form searches for an invariant, guesses a contract, or unfolds a loop/callee
execution. Preconditions, argument safety and depth remain explicit goals.

An amortized contract requires its initial potential in the available budget
and returns final potential as additional guaranteed continuation fuel.
-/

/-- Apply a supplied contract, optionally reserving fuel for the continuation. -/
syntax (name := ramApply) "ram_apply " term:max (" reserving " term)? : tactic

macro_rules
  | `(tactic| ram_apply $contract) =>
      `(tactic|
        first
        | apply Ram.Source.Verification.WP.of_relContract $contract
        | apply Ram.Source.Verification.WP.of_contract $contract
        | apply Ram.Source.Verification.WP.of_amortizedContract $contract
        | apply Ram.Source.Recursion.Spec.Correct.wp_call $contract
        | (rw [Ram.Source.Verification.WP.seq_iff]
           first
           | apply Ram.Source.Verification.WP.of_relContract $contract
           | apply Ram.Source.Verification.WP.of_contract $contract
           | apply Ram.Source.Verification.WP.of_amortizedContract $contract
           | apply Ram.Source.Recursion.Spec.Correct.wp_call $contract))
  | `(tactic| ram_apply $contract reserving $reserve) =>
      `(tactic|
        first
        | apply Ram.Source.Verification.WP.of_relContract_reserve (reserve := $reserve) $contract
        | apply Ram.Source.Verification.WP.of_contract_reserve (reserve := $reserve) $contract
        | apply Ram.Source.Verification.WP.of_amortizedContract_reserve (reserve := $reserve) $contract
        | apply Ram.Source.Recursion.Spec.Correct.wp_call_reserve (reserve := $reserve) $contract
        | (rw [Ram.Source.Verification.WP.seq_iff]
           first
           | apply Ram.Source.Verification.WP.of_relContract_reserve (reserve := $reserve) $contract
           | apply Ram.Source.Verification.WP.of_contract_reserve (reserve := $reserve) $contract
           | apply Ram.Source.Verification.WP.of_amortizedContract_reserve (reserve := $reserve) $contract
           | apply Ram.Source.Recursion.Spec.Correct.wp_call_reserve (reserve := $reserve) $contract))

namespace Ram.Source.Verification.WP

/-- Sequence a relationally specified block with a continuation at any actual
remainder above its reserve. This generic sequencing rule uses `ram_apply`
without specializing either statement to a particular algorithm. -/
theorem seq_of_relContract_reserve {w n heapLimit depth fuel reserve : Nat}
    {program : Program} {first second : Stmt} {P : State w → Prop}
    {R : State w → State w → Prop} {bound : State w → Nat}
    {post : State w → Nat → Prop} {s : State w}
    (contract : RelContract n program heapLimit depth first P R bound)
    (pre : P s) (budget : bound s + reserve ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining, reserve ≤ remaining →
      WP n program heapLimit depth second post t remaining) :
    WP n program heapLimit depth (.seq first second) post s fuel := by
  ram_apply contract reserving reserve
  · exact pre
  · exact budget
  · exact continuation

/-- Compose an amortized block with a continuation that reuses its retained
final credit. Both statements refer to the same actual intermediate state and
remaining budget; initial credit is included in the required starting fuel. -/
theorem seq_of_amortizedContract_reserve {w n heapLimit depth fuel reserve : Nat}
    {program : Program} {first second : Stmt} {P : State w → Prop}
    {R : State w → State w → Prop} {potential charge : State w → Nat}
    {post : State w → Nat → Prop} {s : State w}
    (contract : AmortizedContract n program heapLimit depth first P R potential charge)
    (pre : P s) (budget : charge s + potential s + reserve ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining, reserve + potential t ≤ remaining →
      WP n program heapLimit depth second post t remaining) :
    WP n program heapLimit depth (.seq first second) post s fuel := by
  ram_apply contract reserving reserve
  · exact pre
  · exact budget
  · exact continuation

end Ram.Source.Verification.WP
