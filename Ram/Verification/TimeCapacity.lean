/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Time

/-!
# Reusing time bounds across safety capacities

Heap and call-depth capacities restrict admitted executions but do not change
their actual instruction counts. A conditional `TimeBound` alone cannot be
enlarged: at an insufficient capacity it may hold vacuously. Once a safe total
contract supplies an execution at the original capacity, count determinism
transfers its bound to every completed execution at other capacities.

The conclusion is still conditional. It does not claim that execution is safe
or even possible at the new capacities; those facts remain separate.
-/

namespace Ram.Source.TimeBound

/-- Reuse a proved execution bound independently of heap and nesting capacity,
provided a total contract rules out vacuity at the original capacities. -/
theorem change_capacity {control heapLimit depth heapLimit' depth' : Nat}
    {program : Program} {stmt : Stmt} {P Q : State w → Prop}
    {bound : State w → Nat}
    (cost : TimeBound control program heapLimit depth stmt P bound)
    (total : TotalContract program heapLimit depth stmt P Q) :
    TimeBound control program heapLimit' depth' stmt P bound := by
  intro entry pre steps finish execution
  obtain ⟨other, safe, _⟩ := total entry pre
  obtain ⟨count, measured⟩ := safe.exists_localMeasured control
  exact (measured.deterministic execution).1 ▸ cost entry pre count other measured

end Ram.Source.TimeBound
