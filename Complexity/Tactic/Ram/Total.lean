/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Recursion.Total
import Complexity.Computability.Ram.Verification.Function
import Complexity.Computability.Ram.Verification.Function.Typed
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

`ram_total_vc args entry hp [definitions, facts]` starts a `FunctionContract`
or `TypedFunctionContract` proof directly from its arguments and entry state.
It selects the corresponding proved `of_wp` rule to generate result-shape,
arity, frame and body obligations, without a separate specification
of intermediate local-variable states. The precondition may again be a pattern,
such as `rfl` or `⟨rfl, hbound⟩`. Closed frame bounds are discharged by `decide`;
unresolved arity, frame and program obligations remain as ordinary goals.

`ram_total_bind mid hmid [definitions, facts]` names the value of one leading
assignment as `mid`, retaining `hmid : mid = entry.eval value` in its
continuation. Only the supplied definitions and facts are unfolded before
applying the assignment rule. Safety is discharged only when `ram_simp`
closes it; otherwise it remains a separate goal. The continuation is not
simplified, and subsequent statements are not advanced.

`ram_total_apply contract [definitions, facts]` applies an already proved
contract or recursive function specification, including an existing measured
contract after forgetting its time bound. An explicitly instantiated WP rule is
also accepted: `ram_total_apply (contract.wp_call (arg := input))` selects a
typed input by ordinary Lean application, without guessing it from an encoding.
Calls and loops remain opaque: the
tactic uses the supplied specification without unfolding its implementation.
Named lookup, argument fields and fixed arities come from `ram_def`'s dedicated
binding equations, including imported signatures. The author still chooses the
contract and typed input; input-dependent safety and functional obligations
remain explicit. Optional facts supply their mathematical or representation
reasoning, rather than repeating the caller and callee's argument definitions.

These are transparent macros over the proved total rules and `ram_simp`.
They introduce no execution semantics, resource annotations or trusted solver.
-/

open Lean.Parser.Tactic

/-- Name one actual assigned value and its evaluation equality, leaving the
continuation and any unresolved read safety as ordinary goals. -/
syntax (name := ramTotalBind) "ram_total_bind" ppSpace ident ppSpace ident
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_total_bind $mid:ident $hmid:ident) =>
      `(tactic| ram_total_bind $mid $hmid [])
  | `(tactic| ram_total_bind $mid:ident $hmid:ident [$args,*]) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) only [$args,*]
         first
         | apply Ram.Source.Verification.TotalWP.assign_value
         | (rw [Ram.Source.Verification.TotalWP.seq_iff]
            apply Ram.Source.Verification.TotalWP.assign_value)
         case' reads =>
           try (solve | ram_simp [$args,*])
         case' continuation =>
           intro $mid:ident $hmid:ident))

/-- Generate functional verification conditions without choosing a time
budget. Calls and loops are left to their supplied total specifications. -/
syntax (name := ramTotalVC) "ram_total_vc" (ppSpace ident ppSpace rcasesPat)?
  (" [" simpArg,* "]")? : tactic

/-- Start a callable function proof from its arguments and entry state, leaving
unresolved calling-convention and functional obligations visible. -/
syntax (name := ramTotalVCFunction) "ram_total_vc" ppSpace ident ppSpace ident ppSpace rcasesPat
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
            Ram.Source.Verification.TotalWP.ite_iff, $args,*] <;>
          ram_simp [Ram.DSL.ValueKind.width, Ram.DSL.ValueKind.encode,
            Ram.DSL.ValueKind.decode, Ram.ArrayRef.args, $args,*]))
  | `(tactic| ram_total_vc $s:ident $hs:rcasesPat) => `(tactic| ram_total_vc $s $hs [])
  | `(tactic| ram_total_vc $s:ident $hs:rcasesPat [$args,*]) =>
      `(tactic|
        ((first
          | apply Ram.Source.Verification.verify_total
          | apply Ram.Source.Verification.verify_total_rel)
         intro $s:ident
         rintro $hs:rcasesPat <;> ram_total_vc [$args,*]))
  | `(tactic| ram_total_vc $xs:ident $s:ident $hs:rcasesPat) =>
      `(tactic| ram_total_vc $xs $s $hs [])
elab_rules : tactic
  | `(tactic| ram_total_vc $xs:ident $s:ident $hs:rcasesPat [$args,*]) =>
      Lean.Elab.Tactic.withMainContext do
        let target ← Lean.Meta.whnfR (← Lean.Elab.Tactic.getMainTarget)
        let rule := Lean.mkCIdent <| if target.isAppOf ``Ram.Source.TypedFunctionContract then
          ``Ram.Source.TypedFunctionContract.of_wp else ``Ram.Source.FunctionContract.of_wp
        Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply $rule:ident
         all_goals
           first
           | (intro $xs:ident $s:ident
              rintro $hs:rcasesPat <;> ram_total_vc [$args,*])
           | try (first | decide | ram_simp [Ram.DSL.ValueKind.width, $args,*]))))

/-- Apply an opaque functional specification, opening a leading sequence if
necessary, then simplify only the supplied facts and ordinary RAM vocabulary. -/
syntax (name := ramTotalApply) "ram_total_apply " term:max
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_total_apply $contract) => `(tactic| ram_total_apply $contract [])
  | `(tactic| ram_total_apply $contract [$args,*]) => do
      if !args.getElems.isEmpty then
        return ← `(tactic|
          (ram_total_apply $contract <;>
            ram_simp [Ram.DSL.ValueKind.width, Ram.DSL.ValueKind.encode,
              Ram.DSL.ValueKind.decode, Ram.ArrayRef.args, $args,*] <;>
            simp (config := { failIfUnchanged := false }) only
              [Ram.Expr.ReadsBelow, and_true, true_and] <;> try assumption))
      `(tactic|
        (first
        | apply Ram.Source.Verification.TotalWP.of_relContract $contract
        | apply Ram.Source.Verification.TotalWP.of_contract $contract
        | apply Ram.Source.TypedFunctionContract.wp_call $contract
        | apply Ram.Source.FunctionContract.wp_call $contract
        | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call $contract
        | apply Ram.Source.Verification.TotalWP.call $contract
        | apply Ram.Source.Verification.TotalWP.of_relContract
            (Ram.Source.RelContract.total $contract)
        | apply Ram.Source.Verification.TotalWP.of_contract
            (Ram.Source.Contract.total $contract)
        | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call
            (Ram.Source.Recursion.Spec.Correct.total $contract)
        | apply $contract
        | (rw [Ram.Source.Verification.TotalWP.seq_iff]
           first
           | apply Ram.Source.Verification.TotalWP.of_relContract $contract
           | apply Ram.Source.Verification.TotalWP.of_contract $contract
           | apply Ram.Source.TypedFunctionContract.wp_call $contract
           | apply Ram.Source.FunctionContract.wp_call $contract
           | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call $contract
           | apply Ram.Source.Verification.TotalWP.call $contract
           | apply Ram.Source.Verification.TotalWP.of_relContract
               (Ram.Source.RelContract.total $contract)
           | apply Ram.Source.Verification.TotalWP.of_contract
               (Ram.Source.Contract.total $contract)
           | apply Ram.Source.Recursion.TotalSpec.Correct.wp_call
               (Ram.Source.Recursion.Spec.Correct.total $contract)
           | apply $contract) <;>
          ram_simp [Ram.DSL.ValueKind.width, Ram.DSL.ValueKind.encode,
            Ram.DSL.ValueKind.decode, Ram.ArrayRef.args, $args,*]))

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
