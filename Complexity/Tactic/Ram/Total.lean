/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Recursion.Total
import Complexity.Tactic.Ram.Basic

/-!
# Budget-free verification automation

`ram_total_vc s hs [definitions, facts]` starts a total correctness proof and
rewrites the ordinary statement rules. The resulting obligations concern
mathematical values and safe memory access, not instruction counts or fuel.
The form without names performs the same rewrites on an existing `TotalWP`.
The precondition name can also be a native `rcases` pattern, as in
`ram_total_vc s ⟨hmodel, hbounds⟩ [hmodel, hbounds]`. Ordinary ghost witnesses
and logical structure are introduced by `rintro`; no representation predicate
is unfolded by this pattern support unless its structure must be matched.

`ram_total_apply contract [definitions, facts]` applies an already proved
contract or recursive function specification, including an existing measured
contract after forgetting its time bound. Calls and loops remain opaque: the
tactic uses the supplied specification without unfolding its implementation.
The optional simplification facts can discharge fixed lookup, arity and local
frame facts; input-dependent safety and functional obligations remain explicit.

These are transparent macros over the proved total rules and `ram_simp`.
They introduce no execution semantics, resource annotations or trusted solver.
-/

open Lean.Parser.Tactic

/-- Generate functional verification conditions without choosing a time
budget. Calls and loops are left to their supplied total specifications. -/
syntax (name := ramTotalVC) "ram_total_vc" (ppSpace ident ppSpace rcasesPat)?
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_total_vc) => `(tactic| ram_total_vc [])
  | `(tactic| ram_total_vc [$args,*]) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) only
          [Ram.Source.Verification.TotalWP.skip_iff,
            Ram.Source.Verification.TotalWP.assign_iff,
            Ram.Source.Verification.TotalWP.store_iff,
            Ram.Source.Verification.TotalWP.read_iff,
            Ram.Source.Verification.TotalWP.write_iff,
            Ram.Source.Verification.TotalWP.seq_iff,
            Ram.Source.Verification.TotalWP.ite_iff, $args,*] <;> ram_simp [$args,*]))
  | `(tactic| ram_total_vc $s:ident $hs:rcasesPat) => `(tactic| ram_total_vc $s $hs [])
  | `(tactic| ram_total_vc $s:ident $hs:rcasesPat [$args,*]) =>
      `(tactic|
        ((first
          | apply Ram.Source.Verification.verify_total
          | apply Ram.Source.Verification.verify_total_rel)
         intro $s:ident
         rintro $hs:rcasesPat <;> ram_total_vc [$args,*]))

/-- Apply an opaque functional specification, opening a leading sequence if
necessary, then simplify only the supplied facts and ordinary RAM vocabulary. -/
syntax (name := ramTotalApply) "ram_total_apply " term:max
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_total_apply $contract) => `(tactic| ram_total_apply $contract [])
  | `(tactic| ram_total_apply $contract [$args,*]) =>
      `(tactic|
        (first
        | apply Ram.Source.Verification.TotalWP.of_relContract $contract
        | apply Ram.Source.Verification.TotalWP.of_contract $contract
        | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call $contract
        | apply Ram.Source.Verification.TotalWP.call $contract
        | apply Ram.Source.Verification.TotalWP.of_relContract
            (Ram.Source.RelContract.total $contract)
        | apply Ram.Source.Verification.TotalWP.of_contract
            (Ram.Source.Contract.total $contract)
        | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call
            (Ram.Source.Recursion.Spec.Correct.total $contract)
        | (rw [Ram.Source.Verification.TotalWP.seq_iff]
           first
           | apply Ram.Source.Verification.TotalWP.of_relContract $contract
           | apply Ram.Source.Verification.TotalWP.of_contract $contract
           | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call $contract
           | apply Ram.Source.Verification.TotalWP.call $contract
           | apply Ram.Source.Verification.TotalWP.of_relContract
               (Ram.Source.RelContract.total $contract)
           | apply Ram.Source.Verification.TotalWP.of_contract
               (Ram.Source.Contract.total $contract)
           | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call
               (Ram.Source.Recursion.Spec.Correct.total $contract)) <;> ram_simp [$args,*]))

namespace Ram.Source.Verification.TotalWP

/-- Compose an entry-related functional specification with the next block.
The continuation receives the actual intermediate state, with no fuel to name
or split and no need to unfold either block's execution. -/
theorem seq_of_relContract {w heapLimit depth : Nat} {program : Program}
    {first second : Stmt} {P : State w → Prop} {R : State w → State w → Prop}
    {post : State w → Prop} {s : State w}
    (contract : TotalRelContract program heapLimit depth first P R)
    (pre : P s)
    (continuation : ∀ t, R s t → TotalWP program heapLimit depth second post t) :
    TotalWP program heapLimit depth (.seq first second) post s := by
  ram_total_apply contract
  · exact pre
  · exact continuation

end Ram.Source.Verification.TotalWP
