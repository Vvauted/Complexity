/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Call.Space
import Complexity.Computability.Ram.Compiler.Local.Exact.Space
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic

/-!
# Two-region space bounds for the recursive compiler simulation

Induction follows the existing safe, exactly measured source execution. Each
constructor reuses its actual compiled transition count and target cut states.
Recursive calls use their own local frame size; the declared global local
bound gives the sufficient enclosing stack interval, separately from the actually permitted heap prefix.
-/

namespace Ram.LocalCompiler

/-- All actual accesses made by the compiled execution lie below its initial
SP plus the declared nesting envelope. Calls, guards and both operands of
stores are included; no call-simulation premise remains. -/
theorem simulate_measured_regions {control locals heapLimit depth steps : Nat}
    {program : Program} {main stmt : Stmt} {s s' : Source.State w}
    (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth stmt steps s s')
    (hwf : stmt.WellFormed locals) :
    SimulationRegions control locals heapLimit (rawLink control program main)
      (calleeLocals program) (entry control program main) depth stmt steps s s' := by
  induction hx generalizing locals with
  | skip => exact simulation_skip_regions
  | assign reads => exact simulation_assign_regions hwf reads
  | store addressReads valueReads destination =>
      exact simulation_store_regions hwf addressReads valueReads destination
  | seq _ _ first second => exact simulation_seq_regions (first hwf.1) (second hwf.2)
  | iteTrue reads condition _ body =>
      exact simulation_iteTrue_regions hwf.1 reads condition (body hwf.2.1)
  | iteFalse reads condition _ body =>
      exact simulation_iteFalse_regions hwf.1 reads condition (body hwf.2.2)
  | whileFalse reads condition => exact simulation_whileFalse_regions hwf.1 reads condition
  | whileTrue reads condition _ _ body rest =>
      exact simulation_whileTrue_regions hwf.1 reads condition (body hwf.2) (rest hwf)
  | read available => exact simulation_read_regions hwf available
  | write reads => exact simulation_write_regions hwf reads
  | call lookup arity resultCount frame arguments _ results body =>
      have hf := hvalid.2.2 _ (List.mem_of_getElem? lookup)
      have hcount : _ ≤ _ := frame
      rw [← arity] at hcount
      have call := fun hcaller : locals ≤ control =>
        simulate_call_regions hcaller hf.2.1 (calleeLocals_lookup lookup)
          hwf.1 hwf.2 arguments hcount resultCount hf.2.2.2 hf.1.2.2 results
          (rawLink_function lookup) hcodefit (body hf.1.2.1)
      exact ⟨fun hcaller => (call hcaller).1 hcaller,
        fun hcaller => (call hcaller).2 hcaller⟩

/-- Safe source executions admit one compiler-derived count with the same
uniform target-address bound, not a separately chosen cost annotation. -/
theorem simulate_safe_regions {control locals heapLimit depth : Nat}
    {program : Program} {main stmt : Stmt} {s s' : Source.State w}
    (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth stmt s s')
    (hwf : stmt.WellFormed locals) :
    ∃ steps, Source.LocalMeasuredExec control program heapLimit depth stmt steps s s' ∧
      SimulationRegions control locals heapLimit (rawLink control program main)
        (calleeLocals program) (entry control program main) depth stmt steps s s' := by
  obtain ⟨steps, hsteps⟩ := hx.exists_localMeasured control
  exact ⟨steps, hsteps, simulate_measured_regions hvalid hcodefit hsteps hwf⟩

end Ram.LocalCompiler
