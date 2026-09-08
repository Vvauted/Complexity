/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Loop.Sum
import Complexity.Computability.Ram.Verification.Recursion.Basic
import Complexity.Tactic.Ram.Basic
import Mathlib.Tactic.Ring

/-!
# Focused normalization of verified budgets

`ram_bound [facts]` rewrites the proved formulas for call overhead, guard
costs, atomic instruction lengths and finite-sum loop reserves, then tries
numeric normalization, Presburger arithmetic and polynomial normalization.
The shared declaration binding set supplies static arities and local counts;
function bodies and returned expressions remain opaque unless supplied.
`ram_bound at h` and `ram_bound at *` explicitly select other locations; the
default changes only the goal.

This is a transparent macro over existing theorems and arithmetic tactics.
It does not unfold the compiler, execution, a loop or a callee body. Unknown
budgets, symbolic sums and logarithms remain atoms unless the caller supplies
appropriate facts. In particular it neither chooses a reserve or invariant,
nor infers a recurrence or an asymptotic bound. Logarithm identities with
base/positivity conditions must be supplied with their proofs.
-/

namespace Ram.Source.Recursion.Spec

/-- Normalize an invocation budget using the already proved total local-frame
call length. The parameter-evaluation and result-evaluation costs remain
explicit, and the local count is that of this callee. -/
theorem callBudget_eq {f : Func} {w : Nat} {Arg : Type}
    (spec : Spec f w Arg) (control : Nat) (args : List Expr) (arg : Arg) :
    spec.callBudget control args arg =
      (args.map (fun e => (e.compile (ABI.scratch control)).length)).sum +
        spec.budget arg +
        (f.results.map (fun e => (e.compile (ABI.scratch control)).length)).sum +
        7 * f.locals + args.length + 2 * f.results.length + 9 := by
  rw [callBudget, ABI.callPrefixLocals_length_eq, ABI.returnCodeResultsLocals_length]
  omega

end Ram.Source.Recursion.Spec

open Lean.Parser.Tactic

/-- Normalize compiler-derived budget formulas at the selected location and
try the existing arithmetic tactics. Unresolved obligations remain visible;
no hypotheses are rewritten unless their location is explicitly requested. -/
syntax (name := ramBound) "ram_bound" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| ram_bound $[$loc:location]?) => `(tactic| ram_bound [] $[$loc]?)
  | `(tactic| ram_bound [$args,*] $[$loc:location]?) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) only
          [ram_bindings, Ram.Source.Recursion.Spec.callBudget_eq,
            Ram.ABI.callResultsLocals_steps_eq, Ram.ABI.callLocals_steps_eq,
            Ram.ABI.callPrefixLocals_length_eq, Ram.ABI.returnCodeResultsLocals_length,
            Ram.ABI.returnCodeLocals_length, Ram.ABI.receiveResults_length,
            Ram.Source.Contract.sumBudget_eq, Ram.Source.Contract.guardCost,
            Ram.Tactic.stmtSize_assign, Ram.Tactic.stmtSize_store,
            Ram.Tactic.stmtSize_read, Ram.Tactic.stmtSize_write,
            Ram.Tactic.compile_const_length, Ram.Tactic.compile_var_length,
            Ram.Tactic.compile_bin_length, Ram.Tactic.compile_load_length,
            List.map_nil, List.map_cons, List.sum_nil, List.sum_cons,
            List.length_nil, List.length_cons, ite_true, ite_false,
            Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            Finset.range_zero, Finset.sum_empty, Nat.nsmul_eq_mul, $args,*] $[$loc]?
         <;> try norm_num only [] $[$loc]?
         <;> first
           | omega
           | (ring_nf $[$loc]? <;> omega)
           | skip))

namespace Ram.Source.Recursion.Spec

/-- Turn a body upper bound and an expanded additive reserve into the call
budget obligation expected by `Correct.wp_call_reserve`. All call overhead
comes from `callBudget_eq`, not from a client-provided instruction price. -/
theorem callBudget_add_reserve_le {f : Func} {w control bodyBound reserve fuel : Nat}
    {Arg : Type} (spec : Spec f w Arg) (args : List Expr) (arg : Arg)
    (hbody : spec.budget arg ≤ bodyBound)
    (hbudget :
      (args.map (fun e => (e.compile (ABI.scratch control)).length)).sum +
        bodyBound +
        (f.results.map (fun e => (e.compile (ABI.scratch control)).length)).sum +
        7 * f.locals + args.length + 2 * f.results.length + 9 + reserve ≤ fuel) :
    spec.callBudget control args arg + reserve ≤ fuel := by
  ram_bound at hbudget ⊢

end Ram.Source.Recursion.Spec

namespace Ram.Source.Contract

/-- Constant body reserves specialize the finite-sum loop bound to the exact
linear-loop formula, including all guards and back-edge jumps. -/
theorem sumBudget_const (control : Nat) (condition : Expr) (bodyBudget count : Nat) :
    sumBudget control condition (fun _ => bodyBudget) count =
      count * (guardCost control condition + bodyBudget + 1) +
        guardCost control condition := by
  ram_bound

/-- Reuse an independently proved bound on the summed body work without
reproving the loop's control-flow accounting. This can be passed to a contract
consequence rule or used as a continuation-reserve inequality. -/
theorem sumBudget_le_of_sum_le {control count work : Nat} {condition : Expr}
    {bodyBudget : Nat → Nat}
    (hwork : (∑ i ∈ Finset.range count, bodyBudget (i + 1)) ≤ work) :
    sumBudget control condition bodyBudget count ≤
      (count + 1) * guardCost control condition + work + count := by
  ram_bound

end Ram.Source.Contract
