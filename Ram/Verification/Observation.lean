/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Refinement
import Ram.Observation

/-!
# Compiled observations for arbitrary mathematical models

A refinement may describe lists, finite functions, matrices, sets, automata,
or any other ordinary Lean model. To observe it after compilation, the only
model-specific proof is that its output representation respects the compiler's
existing `State.Observes` relation. The generic theorems below retain the actual
halted run, including the prologue and halt, with or without a separate time
bound. Compiler-private registers and stack memory are not equated to source
data.
-/

namespace Ram.Source

/-- Total correctness gives a halted machine execution with all declared
source-visible observations, without first supplying a time budget. -/
theorem TotalContract.compile_observed {w control heapLimit depth : Nat}
    {program : Program} {stmt : Stmt} {P Q : State w → Prop}
    {code : Code} {input : List (Word w)}
    (h : TotalContract program heapLimit depth stmt P Q)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal steps, Q sourceFinal ∧
      Ram.Exec code steps (Ram.State.initial (BitVec.ofNat w heapLimit :: input))
        targetFinal ∧ targetFinal.status = .halted ∧
      State.Observes heapLimit control sourceFinal targetFinal := by
  obtain ⟨sourceFinal, hx, hq⟩ := h (State.initial input) hp
  obtain ⟨steps, measured⟩ := hx.exists_localMeasured control
  obtain ⟨bodyFinish, _, execution, halted, observed⟩ :=
    LocalCompiler.compileChecked_runs_observed hcompile hcodefit hstackfit measured
  exact ⟨sourceFinal, _, steps + 2, hq, execution, halted, observed⟩

namespace Refines

variable {α β : Type*} {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
  {inputRep : α → State w → Prop} {outputRep : β → State w → Prop}
  {targetRep : β → Ram.State w → Prop} {f : α → β}

/-- Any represented mathematical result transfers to the same actual halted
execution. Clients supply a representation-observation lemma, not another
compiler simulation or a proof specialized to their mathematical datatype. -/
theorem compile_observed {code : Code} {input : List (Word w)}
    (h : Refines program heapLimit depth stmt inputRep outputRep f) (x : α)
    (transport : ∀ y source target, outputRep y source →
      State.Observes heapLimit control source target → targetRep y target)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : inputRep x (State.initial input)) :
    ∃ target steps,
      Ram.Exec code steps (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) target ∧
      target.status = .halted ∧ targetRep (f x) target := by
  obtain ⟨source, target, steps, represented, execution, halted, observed⟩ :=
    (h x).compile_observed hcompile hcodefit hstackfit hp
  exact ⟨target, steps, execution, halted, transport (f x) source target represented observed⟩

/-- A separately proved execution-time bound preserves exactly the same
mathematical output representation on the bounded halted target execution. -/
theorem compile_observed_with_timeBound {code : Code} {input : List (Word w)}
    {bound : State w → Nat}
    (h : Refines program heapLimit depth stmt inputRep outputRep f) (x : α)
    (cost : TimeBound control program heapLimit depth stmt (inputRep x) bound)
    (transport : ∀ y source target, outputRep y source →
      State.Observes heapLimit control source target → targetRep y target)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : inputRep x (State.initial input)) :
    ∃ target,
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) target ∧
      targetRep (f x) target := by
  obtain ⟨source, target, represented, execution, observed⟩ :=
    (h.with_timeBound x cost).compile_observed hcompile hcodefit hstackfit hp
  exact ⟨target, execution, transport (f x) source target represented observed⟩

end Refines
end Ram.Source
