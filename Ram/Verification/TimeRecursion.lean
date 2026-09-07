/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Time
import Ram.Verification.TotalRecursion

/-!
# Adding time bounds to functional recursion specifications

A function can first be verified through `TotalSpec`, then given an independently
proved execution-time bound. The resulting ordinary `Spec.Correct` reuses the
existing compiler-derived call budgets and modular call automation. Adding a
proposed budget to a specification does not itself prove that budget sufficient.
-/

namespace Ram.Source.Recursion.TotalSpec

variable {f : Func} {w control heapLimit : Nat} {Arg : Type} {program : Program}

/-- Add a proposed body budget to a functional specification. The executable
function and all functional and call-depth assertions remain unchanged. -/
def withBudget (spec : TotalSpec f w Arg) (budget : Arg → Nat) : Spec f w Arg where
  pre := spec.pre
  post := spec.post
  depth := spec.depth
  budget := budget

@[simp] theorem withBudget_toTotal (spec : TotalSpec f w Arg) (budget : Arg → Nat) :
    (spec.withBudget budget).toTotal = spec := rfl

/-- Recover a callable measured specification from separate total-correctness
and actual-time proofs of the same function body. -/
theorem Correct.with_timeBound {spec : TotalSpec f w Arg} {arg : Arg}
    {budget : Arg → Nat} (correct : spec.Correct program heapLimit arg)
    (cost : TimeBound control program heapLimit (spec.depth arg) f.body
      (spec.pre arg) (fun _ => budget arg)) :
    (spec.withBudget budget).Correct control program heapLimit arg :=
  TotalRelContract.with_timeBound correct cost

end Ram.Source.Recursion.TotalSpec
