/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Amortized.Basic
import Complexity.Computability.Ram.Verification.Execution

/-!
# Amortized accounting after checked compilation

The complete machine execution includes the header read and halt. Its actual
transition count and the final source potential remain in one inequality;
local registers, heap and I/O are observed on that same halted machine state.
The potential is a source-state assertion, not an extra machine instruction.
-/

namespace Ram.Source.AmortizedContract

/-- Keep the final credit when exporting a total amortized contract to a full
checked machine run. The only additional charge is the two actual prologue
and halt transitions. Source-visible credit can be transported to machine
registers or heap using the accompanying `Observes` relation. -/
theorem compile_observed {w control heapLimit depth : Nat} {program : Program}
    {stmt : Stmt} {P : State w → Prop} {R : State w → State w → Prop}
    {potential charge : State w → Nat} {code : Code} {input : List (Word w)}
    (h : AmortizedContract control program heapLimit depth stmt P R potential charge)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ steps sourceFinal targetFinal,
      Ram.Exec code steps (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) targetFinal ∧
      targetFinal.status = .halted ∧ R (State.initial input) sourceFinal ∧
      State.Observes heapLimit control sourceFinal targetFinal ∧
      steps + potential sourceFinal ≤ charge (State.initial input) +
        potential (State.initial input) + 2 := by
  obtain ⟨bodySteps, sourceFinal, hx, hr, hb⟩ := h (State.initial input) hp
  obtain ⟨bodyFinal, _, hfull, hhalt, hobs⟩ :=
    LocalCompiler.compileChecked_runs_observed hcompile hcodefit hstackfit hx
  exact ⟨bodySteps + 2, sourceFinal, _, hfull, hhalt, hr, hobs, by omega⟩

end Ram.Source.AmortizedContract
