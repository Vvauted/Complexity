/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.Function
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Computability.Ram.Verification.Time.Typed
import Complexity.Computability.Ram.Source.Linking
import Complexity.Tactic.Ram.Budget

/-!
# Source-facing automation for separate function time bounds

`ram_time_vc args entry hp [facts]` starts a function's independent body-time
proof at its actual parameter-bound state. `ram_time_vc [facts]` advances leading
assignments and skips, retaining their compiled costs and actual state updates.
Both forms stop at calls and loops. `ram_time_call time [facts]` applies
a callee's separate bound to a final call. `ram_time_apply correct time reserving
remaining [facts]` additionally uses its functional contract to continue after
a leading call. Call arguments and destinations are inferred from the source
body, including anonymous destinations of discarded calls.

`ram_time_apply correct time on input [facts]` instead selects a typed input and
subtracts the proved call bound from the current reserve. The continuation sees
the actual shared effects with caller bindings already restored. The call must
fit the current reserve. Automation tries only lookup and argument obligations;
affordability, representation preconditions and the continuation remain explicit.
Local binding equations and supplied facts are tried only in complete solutions, so an
unsuccessful attempt does not unfold mathematical names in the continuation.
Value-dependent continuation bounds remain available through the underlying typed
call rules.

The remaining bound is a proof obligation, not execution fuel. The continuation
receives the actual shared-state postcondition and preserved caller registers;
`FunctionTimeBound.call_seq_at` also supports a state-dependent remaining bound.
The macros reuse existing expression simplification and proved call-length
formulas. They neither unfold callee bodies nor infer loop invariants or costs.
-/

open Lean.Parser.Tactic

/-- Advance assignment and skip prefixes in a separate time proof. Costs come
from compiled statement lengths, and calls and loops remain opaque. -/
syntax (name := ramTimeVCSteps) "ram_time_vc" (" [" simpArg,* "]")? : tactic

/-- Start a separate function time proof using source arguments and preconditions. -/
syntax (name := ramTimeVC) "ram_time_vc" ppSpace ident ppSpace ident ppSpace rcasesPat
  (" [" simpArg,* "]")? : tactic

/-- Bound a final call with its independent callee time theorem. -/
syntax (name := ramTimeCall) "ram_time_call " term:max (" [" simpArg,* "]")? : tactic

/-- Use an independent functional contract and time bound at a leading call.
The supplied reserve must bound the actual remaining execution. -/
syntax (name := ramTimeApply) "ram_time_apply " term:max ppSpace term:max
  " reserving " term:max (" [" simpArg,* "]")? : tactic

/-- Continue at a chosen typed input using the remaining proof reserve.
Only completely solved routine goals are discharged; mathematical obligations
and the actual restored-state continuation retain their original form. -/
syntax (name := ramTimeApplyTyped) "ram_time_apply " term:max ppSpace term:max
  " on " term:max (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_time_vc) => `(tactic| ram_time_vc [])
  | `(tactic| ram_time_vc [$args,*]) =>
      `(tactic|
        (try
           (change Ram.Source.TimeBound _ _ _ _ _ _ _
            conv =>
              arg 7
              simp (config := { failIfUnchanged := false }) only
                [ram_bindings, Ram.ABI.callPrefixLocals_length_eq,
                  Ram.ABI.returnCodeResultsLocals_length,
                  Ram.Func.renameCalls_locals, Ram.Func.renameCalls_results,
                  Ram.Tactic.compile_const_length, Ram.Tactic.compile_var_length,
                  Ram.Tactic.compile_bin_length, Ram.Tactic.compile_load_length,
                  List.map_nil, List.map_cons, List.sum_nil, List.sum_cons,
                  List.length_nil, List.length_cons, $args,*])
         ram_simp [$args,*]
         repeat' first
           | apply Ram.Source.TimeBound.seq_assoc_iff.mpr
           | apply Ram.Source.TimeBound.skip_seq_iff.mpr
           | (apply Ram.Source.TimeBound.assign_seq_at
              all_goals ram_simp [$args,*]
              all_goals try (solve | ram_bound [$args,*]))))
  | `(tactic| ram_time_vc $xs:ident $s:ident $hs:rcasesPat) =>
      `(tactic| ram_time_vc $xs $s $hs [])
  | `(tactic| ram_time_vc $xs:ident $s:ident $hs:rcasesPat [$args,*]) =>
      `(tactic|
        (apply Ram.Source.FunctionTimeBound.of_body_at
         intro $xs:ident $s:ident
         rintro $hs:rcasesPat <;> ram_time_vc [$args,*]))
  | `(tactic| ram_time_call $time) => `(tactic| ram_time_call $time [])
  | `(tactic| ram_time_call $time [$args,*]) =>
      `(tactic|
        (apply Ram.Source.FunctionTimeBound.call_at $time
         all_goals ram_simp [$args,*]
         all_goals ram_bound [$args,*]))
  | `(tactic| ram_time_apply $correct $time reserving $remaining) =>
      `(tactic| ram_time_apply $correct $time reserving $remaining [])
  | `(tactic| ram_time_apply $correct $time reserving $remaining [$args,*]) =>
      `(tactic|
        (apply Ram.Source.FunctionTimeBound.call_seq_at $time $correct
           (nextBound := fun _ _ => $remaining)
         all_goals ram_simp [$args,*]
         all_goals
           simp (config := { failIfUnchanged := false }) only
             [Ram.Expr.ReadsBelow, and_true, true_and]
         all_goals try (solve | (intros; ram_bound [$args,*]))))
  | `(tactic| ram_time_apply $correct $time on $input) =>
      `(tactic| ram_time_apply $correct $time on $input [])

elab_rules : tactic
  | `(tactic| ram_time_apply $correct $time on $input [$args,*]) =>
      Lean.Elab.Tactic.focus do
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          apply Ram.Source.FunctionTimeBound.call_seq_typed_remaining_at
            $time $correct $input))
        for goal in ← Lean.Elab.Tactic.getUnsolvedGoals do
          goal.setTag (← goal.getTag).eraseMacroScopes
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          case' lookup | arguments | argumentValues =>
            try (solve | (ram_simp [*, $args,*] <;> assumption))))
