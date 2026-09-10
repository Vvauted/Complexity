/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Arena.Allocation
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Calling the actual arena allocator

Arguments initialize the allocator's local frame. Its returned descriptor and
shared state come from the same counted body execution; restoring caller locals
retains both initialized cells and the advanced cursor. The compiled runner
additionally counts argument passing, the call frame, return and final halt.
Session bootstrap and any input loading are separate operations.
-/

namespace Ram.Source.Arena

/-- Invoke the allocator using the existing function ABI. Its fresh interval
and cursor survive caller-local restoration, with a frame for every other cell. -/
theorem function_measured {program : Program} {control heapLimit depth length : Nat}
    {base value : Word w} (entry : State w)
    (cursor : entry.mem 0 = base) (positive : 0 < base.toNat)
    (capacity : base.toNat + length ≤ heapLimit) (fits : heapLimit < 2 ^ w) :
    ∃ finish, FunctionMeasuredExec control program heapLimit depth function
        [BitVec.ofNat w length, value] (14 * length + 14) entry
        [base, BitVec.ofNat w length] finish ∧
      finish.mem 0 = arrayAddr base length ∧
      ArrayAt heapLimit base (List.replicate length value) finish ∧
      (∀ address, address ≠ 0 →
        address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
        finish.mem address = entry.mem address) ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev := by
  have lengthFits : length < 2 ^ w := by omega
  have pre : Pre heapLimit base length value (entry.enter [BitVec.ofNat w length, value]) := by
    refine ⟨cursor, ?_, ?_, positive, capacity, fits⟩
    · simpa only [State.enter_regs, List.getElem?_cons_zero, Option.getD_some] using
        Word.ofNat_toNat_of_lt lengthFits
    · simp only [State.enter_regs, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
  obtain ⟨callee, executed, post⟩ := allocate_measured (control := control)
    (program := program) (depth := depth) pre
  have invocation := FunctionMeasuredExec.of_body (f := function)
    (by rfl : [BitVec.ofNat w length, value].length = function.params)
    (by decide : function.params ≤ function.locals) executed
    (by simp [function, Expr.ReadsBelow])
  have result : function.results.map callee.eval = [base, BitVec.ofNat w length] := by
    simp only [function, List.map_cons, List.map_nil, State.eval, Expr.eval,
      post.base_reg, post.length_reg, State.enter_regs, List.getElem?_cons_zero, Option.getD_some]
  refine ⟨entry.restore callee, ?_, post.cursor, post.array, ?_, post.input, post.output⟩
  · simpa only [result] using invocation
  · intro address nonzero outside
    exact post.frame address nonzero outside

/-- The full preloaded call counts its real ABI blocks and the final halt.
The separate session bootstrap is not silently repeated or charged here. -/
theorem function_callSteps (control length : Nat) :
    LocalCompiler.Function.callSteps control function (14 * length + 14) + 1 =
      14 * length + 69 := by
  simp [LocalCompiler.Function.callSteps_eq, function, Expr.compile]

/-- One fixed standalone allocator artifact, independent of width and arguments. -/
def code : Code :=
  LocalCompiler.rawLink 5 [function] (LocalCompiler.Function.trampoline 0 2 2)

/-- The ordinary checked compiler accepts the allocator's own function table.
This does not discharge the separate word, heap or stack capacity premises. -/
theorem function_compile :
    LocalCompiler.Function.compile 5 [function] 0 2 = some code := by
  apply LocalCompiler.compileChecked_some_iff.mpr
  exact ⟨by decide, rfl⟩

/-- The existing RAM runner actually returns the allocated descriptor and the
same reusable shared state. Word, code and stack capacities are explicit; no
proposed execution budget or host-created output array is supplied. -/
theorem function_runUntil {program : Program} {control heapLimit fn length : Nat}
    {base value : Word w} {code : Code} (entry : State w)
    (compiled : LocalCompiler.Function.compile control program fn 2 = some code)
    (lookup : program[fn]? = some function) (codeFits : code.length < 2 ^ w)
    (stackFits : heapLimit + ABI.frameSize control < 2 ^ w)
    (cursor : entry.mem 0 = base) (positive : 0 < base.toNat)
    (capacity : base.toNat + length ≤ heapLimit) :
    ∃ finish target,
      LocalCompiler.Function.runUntil control program fn 2 heapLimit
          [BitVec.ofNat w length, value] entry =
        some ⟨target, 14 * length + 69, .halted⟩ ∧
      LocalCompiler.Function.returnedValues 2 target = [base, BitVec.ofNat w length] ∧
      State.Observes heapLimit 0 finish target ∧
      finish.mem 0 = arrayAddr base length ∧
      ArrayAt heapLimit base (List.replicate length value) finish ∧
      (∀ address, address ≠ 0 →
        address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
        finish.mem address = entry.mem address) := by
  have fits : heapLimit < 2 ^ w := by omega
  obtain ⟨finish, invocation, metadata, initialized, frame, _, _⟩ :=
    function_measured (program := program) (control := control) (depth := 0)
      entry cursor positive capacity fits
  obtain ⟨target, returned, fields, observed⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured compiled lookup codeFits
      (by simpa using stackFits) invocation
  exact ⟨finish, target, by simpa only [function_callSteps] using returned,
    fields, observed, metadata, initialized, frame⟩

end Ram.Source.Arena
