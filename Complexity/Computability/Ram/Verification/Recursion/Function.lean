/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Function
import Complexity.Computability.Ram.Verification.Recursion.Total

/-!
# Recursive proofs through callable function contracts

`Ram.Source.Recursion.TotalSpec.verify_wellFounded_function` presents recursive
induction hypotheses as contracts on arguments, returned values and shared
effects. A single body-to-function adapter supplies this view of each smaller
invocation. Algorithmic proofs can then call the induction hypothesis without
opening the callee frame or reconstructing the call-return state.

The conclusion remains the original total body specification. The rule is a
direct application of well-founded total correctness, with no new execution
relation, termination assumption or time budget.
-/

namespace Ram.Source.Recursion.TotalSpec

variable {f : Func} {w heapLimit : Nat} {Arg : Type} {program : Program}

/-- Prove a body by well-founded recursion while using smaller functions only
through their argument/result contracts. The adapter is proved once from the
body specification; it may retain arbitrary shared-state effects. -/
theorem verify_wellFounded_function (spec : TotalSpec f w Arg) {r : Arg → Arg → Prop}
    (wf : WellFounded r)
    {P : Arg → List (Word w) → State w → Prop}
    {Q : Arg → List (Word w) → State w → Word w → State w → Prop}
    (adapt : ∀ arg, spec.Correct program heapLimit arg →
      FunctionContract program heapLimit (spec.depth arg) f (P arg) (Q arg))
    (body : ∀ arg,
      (∀ smaller, r smaller arg →
        FunctionContract program heapLimit (spec.depth smaller) f (P smaller) (Q smaller)) →
      ∀ entry, spec.pre arg entry →
        Verification.TotalWP program heapLimit (spec.depth arg) f.body
          (fun finish => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
            spec.post arg entry finish) entry) :
    ∀ arg, spec.Correct program heapLimit arg :=
  spec.verify_wellFounded wf fun arg ih =>
    body arg fun smaller decrease => adapt smaller (ih smaller decrease)

end Ram.Source.Recursion.TotalSpec
