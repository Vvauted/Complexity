/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation

/-!
# Reusing compiled function time bounds at the source observation

An existing `Ram.Source.FunctionTimeBound` on the actual lowered function bounds
the same invocation produced by measured source simulation. The bridge fixes
the word width, call capacity, heap boundary and caller state. It needs a source
cost observation and representable arguments, not another correctness theorem.
The bound itself supplies neither termination nor a proposed execution budget.

These lemmas do not construct a uniform `FunctionCostBound`. That interface
quantifies over all realized executions, whose unused arguments need not fit
the execution's word width. Its domain therefore cannot be silently restricted
to satisfy the representation premise of this fixed-width bridge.
-/

namespace Ram.LanguageCompiler.ExecutionCost

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit controlReg steps : Nat} {fn : Fin signatures.length}
variable {args finish : Env signatures[fn].params} {value : Value signatures[fn].result}
variable {execution : RealizedExec program w depth (program.body fn) args finish (.returned value)}
variable {P : List (Word w) → Source.State w → Prop}
variable {bound : List (Word w) → Source.State w → Nat}

/-- Apply an independent time bound to the actual lowered invocation witnessed
by this source cost. The enclosing function-body wrapper is included once;
the outer call's argument, frame and halt work is not part of this body bound. -/
theorem le_of_functionTimeBound (cost : ExecutionCost execution steps)
    (time : Source.FunctionTimeBound controlReg (lowerProgram program) heapLimit depth
      (lowerFunc program fn) P bound)
    (hw : 0 < w) (arguments : EnvFits w args) (entry : Source.State w)
    (hpre : P (envWords w args) entry) :
    steps + 2 ≤ bound (envWords w args) entry := by
  obtain ⟨target, measured⟩ :=
    cost.functionMeasuredExec controlReg hw arguments entry (heapLimit := heapLimit)
  exact time _ _ hpre _ _ _ measured

/-- Transport an ordinary source precondition and mathematical upper bound
through the encoded arguments of the same fixed-width invocation. Both
implications concern its actual caller state, not an assumed state-independent
implementation cost. -/
theorem le_of_functionTimeBound_of_le (cost : ExecutionCost execution steps)
    (time : Source.FunctionTimeBound controlReg (lowerProgram program) heapLimit depth
      (lowerFunc program fn) P bound)
    (hw : 0 < w) (arguments : EnvFits w args) (entry : Source.State w)
    {sourcePre : Env signatures[fn].params → Prop}
    {sourceBound : Env signatures[fn].params → Nat}
    (hpre : sourcePre args)
    (precondition : sourcePre args → P (envWords w args) entry)
    (budget : sourcePre args → bound (envWords w args) entry ≤ sourceBound args) :
    steps + 2 ≤ sourceBound args :=
  Nat.le_trans (cost.le_of_functionTimeBound time hw arguments entry (precondition hpre))
    (budget hpre)

end Ram.LanguageCompiler.ExecutionCost
