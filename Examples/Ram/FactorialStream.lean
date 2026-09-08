/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Program.Basic
import Complexity.Computability.Ram.Time.Basic
import Complexity.Tactic.Ram.Basic
import Examples.Ram.Factorial

/-!
# An optional stream driver for factorial

This program reads one word, calls the independently defined factorial function,
and writes its result. It reuses that function's correctness and time theorems
without changing its declaration or requiring a second implementation.

The whole-program execution includes the input header, input/output instructions,
call overhead and halt. Its result is factorial modulo the word range; an exact
natural-number result additionally requires that factorial fits in one word.
The linear time bound uses the numeric input, not its binary encoding length.
-/

namespace Ram.Examples.FactorialStream

open Factorial

/-- An optional stream adapter around the independently defined function. -/
def named : Named.Bundle :=
  let n : Reg := 0
  let answer : Reg := 1
  let factorial := functions.functionIndex.factorial
  functions.withMain 2 (ram% {
    read n;
    answer := call factorial(n);
    write answer;
  })

def main : Stmt := named.main

theorem main_expands : main =
    .seq (.read 0) (.seq (.call 1 self [.var 0]) (.write (.var 1))) := rfl

def afterRead (w k : Nat) : Source.State w :=
  { (Source.State.initial [BitVec.ofNat w k]).setReg 0 (BitVec.ofNat w k)
    with input := [] }

def sourceFinal (w k : Nat) : Source.State w :=
  { (afterRead w k).setReg 1 (value w k) with outputRev := [value w k] }

/-- The actual input/call/output program uses the callable mathematical model
without an instruction budget. The word result retains its modular meaning. -/
theorem main_total (H k : Nat) (hk : k < 2 ^ w) :
    Source.TotalContract program H (k + 1) main
      (fun s : Source.State w => s = Source.State.initial [BitVec.ofNat w k])
      (fun t => t = sourceFinal w k) := by
  apply Source.Verification.verify_total
  intro s hs
  subst s
  rw [main_expands, Source.Verification.TotalWP.seq_iff, Source.Verification.TotalWP.read_iff]
  change Source.Verification.TotalWP program H (k + 1)
    (.seq (.call 1 self [.var 0]) (.write (.var 1))) _ (afterRead w k)
  ram_total_apply (call_refines H (k + 1) (afterRead w k) k)
  · simp [afterRead, hk]
  · ram_total_vc [sourceFinal, value]

/-- Verify the complete input/call/output workflow using only the recursive
contract and WP rules. No measured-execution constructor is used here. -/
theorem main_contract (H k : Nat) (hk : k < 2 ^ w) :
    Source.Contract 2 program H (k + 1) main
      (fun s : Source.State w => s = Source.State.initial [BitVec.ofNat w k])
      (fun t => t = sourceFinal w k) (fun _ => 37 * k + 35) := by
  apply Source.Verification.verify
  intro s hs
  subst s
  rw [main_expands, Source.Verification.WP.seq_iff, Source.Verification.WP.read_iff]
  refine ⟨by change 1 ≤ 37 * k + 35; omega, ?_⟩
  change Source.Verification.WP 2 program H (k + 1)
    (.seq (.call 1 self [.var 0]) (.write (.var 1))) _ (afterRead w k) (37 * k + 35 - 1)
  rw [Source.Verification.WP.seq_iff]
  apply (recursive_contract H k).wp_call
    (show program[self]? = some factorial from rfl) rfl (by decide)
  · simp [Expr.ReadsBelow]
  · exact ⟨hk, by simp [Source.State.enter, afterRead, Source.State.eval, Expr.eval]⟩
  · exact Nat.le_refl _
  · rw [initial_call_budget]
    omega
  · intro callee hcallee remaining hremaining
    change callee = ((afterRead w k).enter _).setReg 1 (value w k) at hcallee
    subst callee
    change Source.Verification.WP 2 program H (k + 1) (.write (.var 1)) _
      ((afterRead w k).leave (((afterRead w k).enter _).setReg 1 (value w k)) 1 (.var 1)) remaining
    rw [leave_answer]
    have hremaining' : 2 ≤ remaining := by
      rw [initial_call_budget] at hremaining
      omega
    ram_vc [sourceFinal, afterRead, hremaining']

/-- The complete source program consumes one input and emits one result. -/
theorem main_measured (H k : Nat) (hk : k < 2 ^ w) :
    Source.LocalMeasuredExec 2 program H (k + 1) main (37 * k + 35)
      (Source.State.initial [BitVec.ofNat w k]) (sourceFinal w k) := by
  have hread : Source.LocalMeasuredExec 2 program H (k + 1) (.read 0) 1
      (Source.State.initial [BitVec.ofNat w k]) (afterRead w k) := .read rfl
  have hcall := call_measured H k (afterRead w k) hk (by
    simp [afterRead, Source.State.setReg])
  have hwrite : Source.LocalMeasuredExec 2 program H (k + 1) (.write (.var 1)) 2
      ((afterRead w k).setReg 1 (value w k)) (sourceFinal w k) := by
    simpa only [Source.State.eval, Expr.eval, Source.State.setReg_same] using
      (Source.LocalMeasuredExec.write (control := 2) (program := program) (heapLimit := H)
        (d := k + 1) (s := (afterRead w k).setReg 1 (value w k))
        (value := .var 1) trivial)
  have hcount : 1 + (37 * k + 32 + 2) = 37 * k + 35 := by omega
  simpa only [hcount] using Source.LocalMeasuredExec.seq hread (.seq hcall hwrite)

theorem valid : LocalCompiler.Valid 2 program main := by decide

/-- One fixed finite instruction list is used for every runtime input. -/
def code : Code := LocalCompiler.rawLink 2 program main

theorem compile_checked : LocalCompiler.compileChecked 2 program main = some code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩

/-- The user-facing named entry point emits exactly the verified local-frame
executable used by the full execution and complexity theorems below. -/
theorem named_compiles : named.compile = some code := compile_checked

/-- The code contains one recursive function body, not `k` unrolled copies. -/
theorem code_length : code.length = 60 := rfl

/-- The independent contract proof compiles to the same halted executable
and whole-program budget as the exact trace proof below. -/
theorem runs_via_contract (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w) :
    ∃ finish, Ram.TerminatesWithin code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.output = [value w k] ∧ finish.input = [] := by
  obtain ⟨sourceFinish, targetFinish, hs, hx, ho, hi⟩ :=
    (main_contract H k hk).compile compile_checked
      (by simpa only [code_length] using hcodefit) hstackfit rfl
  subst sourceFinish
  exact ⟨targetFinish, by simpa only [Nat.add_assoc] using hx, ho, hi⟩

/-- Exact whole-program execution, including argument evaluation, individual
frame saves/restores, return jumps, the stack-header read, and the final halt.
The input starts with the ABI stack header `H`, followed by the user's `k`.
There are no heap reads in this program, so any nonnegative boundary works. -/
theorem runs (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧ finish.output = [value w k] ∧ finish.input = [] := by
  have hfit : code.length < 2 ^ w := by simpa only [code_length] using hcodefit
  obtain ⟨bodyFinish, _, hfull, hhalt, hout, hin⟩ :=
    LocalCompiler.compileChecked_runs_measured compile_checked hfit hstackfit (main_measured H k hk)
  refine ⟨_, ?_, hhalt, hout, hin⟩
  simpa only [Nat.add_assoc] using hfull

/-- The emitted word decodes to exactly factorial modulo `2^w`, for every
legal input, including inputs whose factorial does not fit in one word. -/
theorem runs_mod_factorial (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧
      finish.output.map BitVec.toNat = [factorialNat k % 2 ^ w] ∧ finish.input = [] := by
  obtain ⟨finish, hx, halt, hout, hin⟩ := runs H k hk hcodefit hstackfit
  exact ⟨finish, hx, halt, by rw [hout]; simp [value_toNat], hin⟩

/-- If the mathematical factorial fits as well, the same execution returns
that exact natural number, without a modular reduction in its specification. -/
theorem runs_factorial_of_lt (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w)
    (hresult : factorialNat k < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧
      finish.output.map BitVec.toNat = [factorialNat k] ∧ finish.input = [] := by
  obtain ⟨finish, hx, halt, hout, hin⟩ := runs_mod_factorial H k hk hcodefit hstackfit
  exact ⟨finish, hx, halt, by simpa only [Nat.mod_eq_of_lt hresult] using hout, hin⟩

/-- External input representation: an empty-heap stack header, then the input
number as one unsigned word. Encoding is not an extra machine instruction. -/
def encode (w k : Nat) : List (Word w) := [BitVec.ofNat w 0, BitVec.ofNat w k]

/-- Space for the fixed code and all simultaneously live recursive frames.
This also ensures that the input number itself has an exact word encoding. -/
def admissible (w k : Nat) : Prop := 60 < 2 ^ w ∧ (k + 1) * 3 < 2 ^ w

def post (w k : Nat) (finish : Ram.State w) : Prop :=
  finish.output = [value w k] ∧ finish.input = []

/-- A uniform bound for the same code at every admissible input and width,
with the ordinary terminating RAM execution judgment as its meaning. -/
theorem uniform_time :
    UniformTimeBound code encode admissible id post (fun k => 37 * k + 37) := by
  intro w k hadmissible
  have hk : k < 2 ^ w := by
    have hspace := hadmissible.2
    omega
  obtain ⟨finish, hx, halt, hout, hin⟩ :=
    runs 0 k hk hadmissible.1 (by simpa using hadmissible.2)
  exact ⟨finish, ⟨37 * k + 37, Nat.le_refl _, hx, halt⟩, hout, hin⟩

/-- Linear time in the *numeric value* `k`, uniformly over admissible widths.
This is not linear time in the binary encoding length of `k` (nor in the
number of input words, which is constant for this particular interface). -/
theorem uniform_linear : UniformBigO code encode admissible id post id :=
  uniform_time.linear

end Ram.Examples.FactorialStream
