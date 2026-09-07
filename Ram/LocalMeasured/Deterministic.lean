/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalMeasured

/-!
# Determinism of measured source execution

Safety bounds restrict which executions can be admitted; they do not change
the executed program, its result, or its compiler-derived instruction count.
-/

namespace Ram.Source.LocalMeasuredExec

/-- Two completed executions of the same source program have the same exact
instruction count and final state, independently of their safety bounds. -/
theorem deterministic {control heapLimit heapLimit' depth depth' steps steps' : Nat}
    {program : Program} {stmt : Stmt} {s t u : State w}
    (ht : LocalMeasuredExec control program heapLimit depth stmt steps s t)
    (hu : LocalMeasuredExec control program heapLimit' depth' stmt steps' s u) :
    steps = steps' ∧ t = u := by
  induction ht generalizing heapLimit' depth' steps' u <;> cases hu <;> grind

end Ram.Source.LocalMeasuredExec
