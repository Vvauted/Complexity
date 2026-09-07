/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalProgram

/-!
# A small callee in a program with a large unrelated frame

The fixed main program reads a word into register 0, keeps 99 in register 1,
calls a one-local increment function into register 2, and writes all three
registers. The callee overwrites register 0: its restoration is observable in
the first output. Register 1 lies above the callee's local bound: its
preservation is observable in the second output.

A second, uncalled function has an arbitrary local bound. Enlarging that
function or the reserved-register boundary changes neither the executed
source program nor its 36 actual RAM transitions. The linked code includes
the uncalled function once, so its *static* size does grow. Counts below are
derived from the generated instruction lists and closed compiler simulation.
The increment is word arithmetic, including modular wraparound.
-/

namespace Ram.Examples.LocalCalls

def increment : Func where
  params := 1
  locals := 1
  body := .assign 0 (.bin .add (.var 0) (.const 1))
  result := .var 0

def unused (spareLocals : Nat) : Func where
  params := 0
  locals := spareLocals
  body := .skip
  result := .const 0

def program (spareLocals : Nat) : Program := [increment, unused spareLocals]

/-- Neither the input word nor either register bound occurs in this AST. -/
def main : Stmt :=
  .seq (.read 0)
    (.seq (.assign 1 (.const 99))
      (.seq (.call 2 0 [.var 0])
        (.seq (.write (.var 0)) (.seq (.write (.var 1)) (.write (.var 2))))))

def afterRead (n : Word w) : Source.State w :=
  { (Source.State.initial [n]).setReg 0 n with input := [] }

def beforeCall (n : Word w) : Source.State w :=
  (afterRead n).setReg 1 (BitVec.ofNat w 99)

def calleeFinish (n : Word w) : Source.State w :=
  let entered := (beforeCall n).enter ([Expr.var 0].map (beforeCall n).eval)
  entered.setReg 0 (entered.eval (.bin .add (.var 0) (.const 1)))

def afterCall (n : Word w) : Source.State w :=
  (beforeCall n).leave (calleeFinish n) 2 increment.result

def emit (r : Reg) (s : Source.State w) : Source.State w :=
  { s with outputRev := s.regs r :: s.outputRev }

def sourceFinal (n : Word w) : Source.State w :=
  emit 2 (emit 1 (emit 0 (afterCall n)))

/-- The callee actually changes its parameter; this is not a no-op call. -/
theorem calleeFinish_value (n : Word w) : (calleeFinish n).regs 0 = n + 1 := by
  simp [calleeFinish, beforeCall, afterRead, Source.State.enter, Source.State.eval,
    Source.State.setReg, Expr.eval, BinOp.eval]

theorem afterCall_registers (n : Word w) :
    (afterCall n).regs 0 = n ∧
    (afterCall n).regs 1 = BitVec.ofNat w 99 ∧
    (afterCall n).regs 2 = n + 1 := by
  simp [afterCall, Source.State.leave, Source.State.eval, increment, Expr.eval,
    calleeFinish_value, beforeCall, afterRead, Source.State.setReg]

theorem sourceFinal_registers (n : Word w) :
    (sourceFinal n).regs 0 = n ∧
    (sourceFinal n).regs 1 = BitVec.ofNat w 99 ∧
    (sourceFinal n).regs 2 = n + 1 := afterCall_registers n

@[simp] theorem sourceFinal_output (n : Word w) :
    (sourceFinal n).output = [n, BitVec.ofNat w 99, n + 1] := by
  obtain ⟨h0, h1, h2⟩ := afterCall_registers n
  change [(afterCall n).regs 2, (afterCall n).regs 1, (afterCall n).regs 0].reverse = _
  rw [h0, h1, h2]
  rfl

@[simp] theorem sourceFinal_input (n : Word w) : (sourceFinal n).input = [] := rfl

/-- The number comes from actual save/initialize/restore instruction lists,
the compiled assignment, and both control transfers. -/
theorem call_steps (control spareLocals : Nat) :
    (ABI.callPrefixLocals control increment.locals [.var 0] 0).length + 1 +
        LocalCompiler.stmtSize control (LocalCompiler.calleeLocals (program spareLocals))
          increment.body +
        (ABI.returnCodeLocals control increment.locals increment.result).length + 1 = 25 := by
  simp [ABI.callPrefixLocals_length_eq, ABI.returnCodeLocals_length,
    increment, LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile]

theorem call_measured (control spareLocals H : Nat) (n : Word w) :
    Source.LocalMeasuredExec control (program spareLocals) H 1
      (.call 2 0 [.var 0]) 25 (beforeCall n) (afterCall n) := by
  have hb : Source.LocalMeasuredExec control (program spareLocals) H 0
      increment.body
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals (program spareLocals))
        increment.body)
      ((beforeCall n).enter ([Expr.var 0].map (beforeCall n).eval)) (calleeFinish n) :=
    .assign ⟨trivial, trivial⟩
  have hc := Source.LocalMeasuredExec.call (dst := 2) (fn := 0)
    (show (program spareLocals)[0]? = some increment from rfl) rfl (by decide)
    (show ∀ arg ∈ [Expr.var 0], arg.ReadsBelow H (beforeCall n).regs (beforeCall n).mem
      from by simp [Expr.ReadsBelow]) hb
    (show increment.result.ReadsBelow H _ _ from trivial)
  simpa only [call_steps] using hc

/-- Source execution is constructed from ordinary read, assignment, call, and
write rules, not by evaluating a bounded machine runner. -/
theorem main_measured (control spareLocals H : Nat) (n : Word w) :
    Source.LocalMeasuredExec control (program spareLocals) H 1 main 34
      (Source.State.initial [n]) (sourceFinal n) := by
  have hr : Source.LocalMeasuredExec control (program spareLocals) H 1 (.read 0) 1
      (Source.State.initial [n]) (afterRead n) := .read rfl
  have ha : Source.LocalMeasuredExec control (program spareLocals) H 1
      (.assign 1 (.const 99)) 2 (afterRead n) (beforeCall n) := .assign trivial
  have hw (r : Reg) (s : Source.State w) :
      Source.LocalMeasuredExec control (program spareLocals) H 1
        (.write (.var r)) 2 s (emit r s) := .write trivial
  exact .seq hr (.seq ha (.seq (call_measured control spareLocals H n)
    (.seq (hw 0 _) (.seq (hw 1 _) (hw 2 _)))))

theorem valid {control spareLocals : Nat} (hcontrol : 3 ≤ control)
    (hspare : spareLocals ≤ control) :
    LocalCompiler.Valid control (program spareLocals) main := by
  have h0 : 0 < control := by omega
  have h1 : 1 < control := by omega
  have h2 : 2 < control := by omega
  simp [LocalCompiler.Valid, Compiler.Valid, main, program, increment, unused,
    Stmt.WellFormed, Func.WellFormed, Compiler.CallsValid, Expr.Bounded,
    h0, h1, h2, hspare]
  omega

/-- This code is fixed before the input word is supplied. -/
def code (control spareLocals : Nat) : Code :=
  LocalCompiler.rawLink control (program spareLocals) main

theorem compile_checked {control spareLocals : Nat} (hcontrol : 3 ≤ control)
    (hspare : spareLocals ≤ control) :
    LocalCompiler.compileChecked control (program spareLocals) main =
      some (code control spareLocals) :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid hcontrol hspare, rfl⟩

/-- Uncalled functions still occupy code memory, even though they contribute
no runtime frame work. The two quantities are deliberately kept separate. -/
theorem code_length (control spareLocals : Nat) :
    (code control spareLocals).length = 3 * spareLocals + 42 := by
  rw [code, LocalCompiler.rawLink_length]
  simp [main, program, increment, unused, LocalCompiler.funcSize,
    LocalCompiler.stmtSize, LocalCompiler.compileStmt, LocalCompiler.calleeLocals,
    ABI.callCodeLocals_length, ABI.callPrefixLocals_length_eq,
    ABI.returnCodeLocals_length, Expr.compile]
  omega

/-- Exact full execution for arbitrary word input and arbitrary unrelated
function size. The first input word is the ordinary counted ABI heap header.
Only the sufficient address-space conditions depend on the reserved bound. -/
theorem runs (control spareLocals H : Nat) (n : Word w)
    (hcontrol : 3 ≤ control) (hspare : spareLocals ≤ control)
    (hcodefit : 3 * spareLocals + 42 < 2 ^ w)
    (hstackfit : H + (control + 1) < 2 ^ w) :
    ∃ finish, Ram.Exec (code control spareLocals) 36
        (Ram.State.initial [BitVec.ofNat w H, n]) finish ∧
      finish.status = .halted ∧
      finish.output = [n, BitVec.ofNat w 99, n + 1] ∧ finish.input = [] := by
  have hfit : (code control spareLocals).length < 2 ^ w := by
    rw [code_length]
    exact hcodefit
  have hstack : H + 1 * ABI.frameSize control < 2 ^ w := by
    simpa only [ABI.frameSize, Nat.one_mul] using hstackfit
  obtain ⟨_, _, hx, halt, hout, hin⟩ :=
    LocalCompiler.compileChecked_runs_measured (compile_checked hcontrol hspare)
      hfit hstack (main_measured control spareLocals H n)
  exact ⟨_, hx, halt, by simpa using hout, by simpa using hin⟩

/-- In particular, reserving at least 200 registers because of an unrelated
function does not make the one-local call save or restore 200 registers. -/
theorem runs_with_large_unused (control H : Nat) (n : Word w)
    (hcontrol : 200 ≤ control) (hcodefit : 642 < 2 ^ w)
    (hstackfit : H + (control + 1) < 2 ^ w) :
    ∃ finish, Ram.Exec (code control 200) 36
        (Ram.State.initial [BitVec.ofNat w H, n]) finish ∧
      finish.status = .halted ∧
      finish.output = [n, BitVec.ofNat w 99, n + 1] ∧ finish.input = [] :=
  runs control 200 H n (by omega) hcontrol hcodefit hstackfit

end Ram.Examples.LocalCalls
