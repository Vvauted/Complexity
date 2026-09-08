/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.Function
import Complexity.Tactic.Ram.Budget

/-!
# Source-facing automation for separate function time bounds

`ram_time_vc args entry hp [facts]` starts a function's independent body-time
proof at its actual parameter-bound state. `ram_time_call time [facts]` applies
a callee's separate bound to a final call. `ram_time_apply correct time reserving
remaining [facts]` additionally uses its functional contract to continue after
a leading call. Call arguments and destinations are inferred from the source
body, including anonymous destinations of discarded calls.

The remaining bound is a proof obligation, not execution fuel. The continuation
receives the actual shared-state postcondition and preserved caller registers;
`FunctionTimeBound.call_seq_at` also supports a state-dependent remaining bound.
The macros reuse existing expression simplification and proved call-length
formulas. They neither unfold callee bodies nor infer loop invariants or costs.
-/

open Lean.Parser.Tactic

/-- Start a separate function time proof using source arguments and preconditions. -/
syntax (name := ramTimeVC) "ram_time_vc" ppSpace ident ppSpace ident ppSpace rcasesPat
  (" [" simpArg,* "]")? : tactic

/-- Bound a final call with its independent callee time theorem. -/
syntax (name := ramTimeCall) "ram_time_call " term:max (" [" simpArg,* "]")? : tactic

/-- Use an independent functional contract and time bound at a leading call.
The supplied reserve must bound the actual remaining execution. -/
syntax (name := ramTimeApply) "ram_time_apply " term:max ppSpace term:max
  " reserving " term:max (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_time_vc $xs:ident $s:ident $hs:rcasesPat) =>
      `(tactic| ram_time_vc $xs $s $hs [])
  | `(tactic| ram_time_vc $xs:ident $s:ident $hs:rcasesPat [$args,*]) =>
      `(tactic|
        (apply Ram.Source.FunctionTimeBound.of_body_at
         intro $xs:ident $s:ident
         rintro $hs:rcasesPat <;> ram_simp [$args,*]))
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
