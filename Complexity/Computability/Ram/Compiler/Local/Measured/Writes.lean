/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Call.Writes
import Complexity.Computability.Ram.Compiler.Local.Exact.Frame
import Complexity.Computability.Ram.Compiler.Local.Exact.Writes
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic

/-!
# Protected older frames for the complete recursive compiler

Induction on the existing exactly measured source execution proves that every
actual write lies in the source heap or at/above the target entry SP. Calls
use the callee's real frame size and target cut states; there is no remaining
assumption that recursive bodies preserve this write region.

The resulting simulation exposes the all-prefix saved-frame theorems from
`Complexity.Computability.Ram.Compiler.Local.Exact.Frame`. Step counts remain those of the existing compiler.
-/

namespace Ram.LocalCompiler

/-- All compiled statements, including recursive calls, protect every older
stack word from actual writes throughout their measured execution. -/
theorem simulate_measured_writes {control locals heapLimit depth steps : Nat}
    {program : Program} {main stmt : Stmt} {s s' : Source.State w}
    (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth stmt steps s s')
    (hwf : stmt.WellFormed locals) :
    SimulationWrites control locals heapLimit (rawLink control program main)
      (calleeLocals program) (entry control program main) depth stmt steps s s' := by
  induction hx generalizing locals with
  | skip => exact simulation_skip_writes
  | assign reads => exact simulation_assign_writes hwf reads
  | store addressReads valueReads destination =>
      exact simulation_store_writes hwf addressReads valueReads destination
  | seq _ _ first second => exact simulation_seq_writes (first hwf.1) (second hwf.2)
  | iteTrue reads condition _ body =>
      exact simulation_iteTrue_writes hwf.1 reads condition (body hwf.2.1)
  | iteFalse reads condition _ body =>
      exact simulation_iteFalse_writes hwf.1 reads condition (body hwf.2.2)
  | whileFalse reads condition => exact simulation_whileFalse_writes hwf.1 reads condition
  | whileTrue reads condition _ _ body rest =>
      exact simulation_whileTrue_writes hwf.1 reads condition (body hwf.2) (rest hwf)
  | read available => exact simulation_read_writes hwf available
  | write reads => exact simulation_write_writes hwf reads
  | call lookup arity frame arguments _ result body =>
      have hf := hvalid.2.2 _ (List.mem_of_getElem? lookup)
      have hcount : _ ≤ _ := frame
      rw [← arity] at hcount
      have call := fun hcaller : locals ≤ control =>
        simulate_call_writes hcaller hf.2.1 (calleeLocals_lookup lookup)
          hwf.1 hwf.2 arguments hcount hf.1.2.2 result (rawLink_function lookup)
          hcodefit (body hf.1.2.1)
      exact ⟨fun hcaller => (call hcaller).1 hcaller,
        fun hcaller => (call hcaller).2 hcaller⟩

/-- Safe source execution supplies one compiler-derived count and the full
recursive write-region proof for that same count. -/
theorem simulate_safe_writes {control locals heapLimit depth : Nat}
    {program : Program} {main stmt : Stmt} {s s' : Source.State w}
    (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hx : Source.SafeExec program heapLimit depth stmt s s')
    (hwf : stmt.WellFormed locals) :
    ∃ steps, Source.LocalMeasuredExec control program heapLimit depth stmt steps s s' ∧
      SimulationWrites control locals heapLimit (rawLink control program main)
        (calleeLocals program) (entry control program main) depth stmt steps s s' := by
  obtain ⟨steps, hsteps⟩ := hx.exists_localMeasured control
  exact ⟨steps, hsteps, simulate_measured_writes hvalid hcodefit hsteps hwf⟩

end Ram.LocalCompiler
