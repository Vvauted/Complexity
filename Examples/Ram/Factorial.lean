/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Program.Basic
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Computability.Ram.Source.State
import Complexity.Computability.Ram.Time.Basic
import Complexity.Computability.Ram.Verification.Call
import Complexity.Computability.Ram.Verification.Recursion.Basic
import Complexity.Computability.Ram.Verification.Recursion.Time
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Tactic.Ram.Basic
import Complexity.Tactic.Ram.Total
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Ordinary recursive factorial, with exact whole-program machine time

The source and linked code below are fixed, independently of the input and word
width. Function names are resolved by `ram_program%`, and the default local-frame
compiler saves and restores the callee's declared locals on every invocation.
`factorialNat` is a compatibility alias for mathlib's `Nat.factorial`, only
the mathematical specification: it never appears in a runtime instruction.

The result is factorial modulo the word range; intermediate multiplication is
allowed to wrap. Only the input, return addresses, and live stack must fit.
-/

namespace Ram.Examples.Factorial

/-- Both function names and local register names are resolved automatically.
The source does not maintain a numeric function table or a `self` index. -/
ram_def named := ram_program% {
  fn factorial(n) locals (answer) {
    if n {
      answer := call factorial(n - 1);
      answer := n * answer;
    } else {
      answer := 1;
    }
    return answer;
  }
  main locals (n, answer) {
    read n;
    answer := call factorial(n);
    write answer;
  }
}

def program : Program := named.program
def main : Stmt := named.main

/-- Inspect the resolved declaration for the semantic proof below. -/
def factorial : Func := named.program[named.functionIndex.factorial]'(by decide)

/-- This resolved index is used only in proofs, never in the named source. -/
def self : Nat := named.functionIndex.factorial

theorem program_expands : program = [factorial] := rfl

theorem main_expands : main =
    .seq (.read 0) (.seq (.call 1 self [.var 0]) (.write (.var 1))) := rfl

theorem factorial_expands : factorial =
    { params := 1, locals := 2
      body := .ite (.var 0)
        (.seq (.call 1 self [.bin .sub (.var 0) (.const 1)])
          (.assign 1 (.bin .mul (.var 0) (.var 1))))
        (.assign 1 (.const 1))
      result := .var 1 } := rfl

/-- The standard mathematical factorial, not a machine operation. -/
abbrev factorialNat : Nat → Nat := Nat.factorial

def value (w k : Nat) : Word w := BitVec.ofNat w (factorialNat k)

theorem value_toNat (w k : Nat) :
    (value w k).toNat = factorialNat k % 2 ^ w := BitVec.toNat_ofNat _ _

theorem value_succ (w k : Nat) :
    value w (k + 1) = BitVec.ofNat w (k + 1) * value w k := by
  simp only [value, factorialNat, Nat.factorial_succ, BitVec.ofNat_mul]

private theorem set_answer_twice (s : Source.State w) (a b : Word w) :
    (s.setReg 1 a).setReg 1 b = s.setReg 1 b :=
  Source.State.setReg_setReg s 1 a b

/-- The callee's local registers are genuinely discarded on return. In
particular, the caller's original `n` survives its recursive call. -/
theorem leave_answer (s : Source.State w) (args : List (Word w)) (answer : Word w) :
    s.leave ((s.enter args).setReg 1 answer) 1 (.var 1) = s.setReg 1 answer :=
  Source.State.leave_enter_setReg s args 1 1 answer

private theorem encoded_pred (w k : Nat) :
    BitVec.ofNat w (k + 1) - BitVec.ofNat w 1 = BitVec.ofNat w k := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

/-- Length calculation on the actual generated setup and return instruction
lists. This includes all individual saves, restores, and jumps. -/
theorem recursive_call_steps (bodySteps : Nat) :
    (ABI.callPrefixLocals 2 2 [.bin .sub (.var 0) (.const 1)] 0).length + 1 + bodySteps +
      (ABI.returnCodeLocals 2 2 (.var 1)).length + 1 = bodySteps + 30 := by
  change 16 + 1 + bodySteps + 12 + 1 = bodySteps + 30
  omega

theorem initial_call_steps (bodySteps : Nat) :
    (ABI.callPrefixLocals 2 2 [.var 0] 0).length + 1 + bodySteps +
      (ABI.returnCodeLocals 2 2 (.var 1)).length + 1 = bodySteps + 28 := by
  change 14 + 1 + bodySteps + 12 + 1 = bodySteps + 28
  omega

/-- Functional recursion is specified without an instruction budget. -/
def totalSpec (w : Nat) : Source.Recursion.TotalSpec factorial w Nat where
  pre k s := k < 2 ^ w ∧ s.regs named.localReg.factorial.n = BitVec.ofNat w k
  post k entry finish := finish = entry.setReg named.localReg.factorial.answer (value w k)
  depth k := k

/-- The ghost argument records the mathematical input. Neither its proposed
time bound nor the mathematical factorial is part of the runtime program. -/
def recursionSpec (w : Nat) : Source.Recursion.Spec factorial w Nat :=
  (totalSpec w).withBudget (fun k => 37 * k + 4)

/-- Simplify recursive invocation budgets using the generated-code length
calculation above, so continuation proofs need not expand ABI internals. -/
theorem recursive_call_budget (w k : Nat) :
    (recursionSpec w).callBudget 2 [.bin .sub (.var 0) (.const 1)] k = 37 * k + 34 := by
  change (ABI.callPrefixLocals 2 2 [.bin .sub (.var 0) (.const 1)] 0).length + 1 +
    (37 * k + 4) + (ABI.returnCodeLocals 2 2 (.var 1)).length + 1 = 37 * k + 34
  simpa only [Nat.add_assoc] using recursive_call_steps (37 * k + 4)

theorem initial_call_budget (w k : Nat) :
    (recursionSpec w).callBudget 2 [.var 0] k = 37 * k + 32 := by
  change (ABI.callPrefixLocals 2 2 [.var 0] 0).length + 1 + (37 * k + 4) +
    (ABI.returnCodeLocals 2 2 (.var 1)).length + 1 = 37 * k + 32
  simpa only [Nat.add_assoc] using initial_call_steps (37 * k + 4)

private theorem predecessor_pre (k : Nat) (s : Source.State w)
    (hs : (totalSpec w).pre (k + 1) s) :
    (totalSpec w).pre k (s.enter ([.bin .sub (.var 0) (.const 1)].map s.eval)) := by
  have hpred : s.eval (.bin .sub (.var 0) (.const 1)) = BitVec.ofNat w k := by
    change s.regs 0 - BitVec.ofNat w 1 = BitVec.ofNat w k
    rw [hs.2, encoded_pred]
  exact ⟨by have hk := hs.1; omega, by simp [Source.State.enter_regs, hpred]⟩

/-- Prove factorial using ordinary well-founded recursion and mathlib's
factorial equation. No time bound or measured execution enters this proof. -/
theorem recursive_total (H : Nat) :
    ∀ k, (totalSpec w).Correct program H k := by
  apply Source.Recursion.TotalSpec.verify_wellFounded _ Nat.lt_wfRel.wf
  intro k ih s hs
  obtain ⟨hk, hn⟩ := hs
  cases k with
  | zero =>
      ram_total_vc [totalSpec, factorial_expands, hn, value, factorialNat, Nat.factorial_zero]
  | succ k =>
      have hnonzero : s.eval (.var 0) ≠ 0 := by
        intro hz
        have hnat := congrArg BitVec.toNat hz
        change (s.regs 0).toNat = 0 at hnat
        rw [hn, Word.ofNat_toNat_of_lt hk] at hnat
        omega
      change Source.Verification.TotalWP program H (k + 1) factorial.body _ s
      simp only [totalSpec]
      rw [factorial_expands, Source.Verification.TotalWP.ite_iff]
      refine ⟨trivial, ?_⟩
      rw [if_neg hnonzero, Source.Verification.TotalWP.seq_iff]
      apply (ih k (Nat.lt_succ_self k)).wp_call
        (show program[self]? = some factorial from rfl) rfl (by decide)
      · simp [Expr.ReadsBelow]
      · exact predecessor_pre k s ⟨hk, hn⟩
      · exact Nat.le_refl _
      · intro callee hcallee
        change callee = (s.enter _).setReg 1 (value w k) at hcallee
        subst callee
        change Source.Verification.TotalWP program H (k + 1)
          (.assign 1 (.bin .mul (.var 0) (.var 1))) _
          (s.leave ((s.enter _).setReg 1 (value w k)) 1 (.var 1))
        rw [Source.State.leave_enter_setReg]
        ram_total_vc [totalSpec, factorial_expands, hn, value_succ]
        funext r
        by_cases hr : r = 1 <;> simp [hr]

/-- The independent time proof composes generated call/assignment lengths.
The mathematical recurrence is `T (k + 1) = T k + 37`; functional recursion
only supplies the callable termination assertion needed by sequence composition. -/
theorem recursive_timeBound (H : Nat) :
    ∀ k, Source.TimeBound 2 program H k factorial.body ((totalSpec w).pre k)
      (fun _ => 37 * k + 4) := by
  intro k
  induction k with
  | zero =>
      have yes : Source.TimeBound 2 program H 0
          (.seq (.call 1 self [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.bin .mul (.var 0) (.var 1))))
          (fun s : Source.State w => (totalSpec w).pre 0 s ∧ s.eval (.var 0) ≠ 0)
          (fun _ => 0) := by
        intro s hs steps t hx
        exact False.elim (hs.2 hs.1.2)
      have branches := Source.TimeBound.ite yes
        (Source.TimeBound.assign (value := .const 1) (dst := 1))
      apply branches.mono_budget
      intro s hs
      change 2 + (if s.eval (.var 0) = 0 then 2 else 0 + 1) ≤ 4
      split <;> omega
  | succ k ih =>
      let P : Source.State w → Prop :=
        fun s => (totalSpec w).pre (k + 1) s ∧ s.eval (.var 0) ≠ 0
      have callable : Source.TotalContract program H (k + 1)
          (.call 1 self [.bin .sub (.var 0) (.const 1)]) P (fun _ => True) := by
        intro s hs
        apply (recursive_total H k).wp_call
          (show program[self]? = some factorial from rfl) rfl (by decide)
        · simp [Expr.ReadsBelow]
        · exact predecessor_pre k s hs.1
        · exact Nat.le_refl _
        · intro callee post
          trivial
      have callCost : Source.TimeBound 2 program H (k + 1)
          (.call 1 self [.bin .sub (.var 0) (.const 1)]) P (fun _ => 37 * k + 34) := by
        apply (Source.TimeBound.call (P := P)
          (show program[self]? = some factorial from rfl)
          (fun s hs => predecessor_pre k s hs.1) ih).mono_budget
        intro s hs
        change 16 + 1 + (37 * k + 4) + 12 + 1 ≤ 37 * k + 34
        omega
      have yes : Source.TimeBound 2 program H (k + 1)
          (.seq (.call 1 self [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.bin .mul (.var 0) (.var 1)))) P (fun _ => 37 * k + 38) := by
        apply Source.TimeBound.seq callable callCost Source.TimeBound.assign
        intro s hs middle hm
        change 37 * k + 34 + 4 ≤ 37 * k + 38
        omega
      have branches := Source.TimeBound.ite yes
        (Source.TimeBound.assign (value := .const 1) (dst := 1))
      apply branches.mono_budget
      intro s hs
      change 2 + (if s.eval (.var 0) = 0 then 2 else (37 * k + 38) + 1) ≤
        37 * (k + 1) + 4
      split <;> omega

/-- A separate contract proof, independent of `body_measured` below. Ordinary
WP rules handle branching, sequencing and assignment; the induction hypothesis
is invoked through the reusable recursive-call continuation rule. -/
theorem recursive_contract (H : Nat) :
    ∀ k, (recursionSpec w).Correct 2 program H k :=
  fun k => (recursive_total H k).with_timeBound (recursive_timeBound H k)

/-- The call implements ordinary `Nat.factorial` through its word encoding.
The captured caller is only a representation ghost: all other registers,
memory and I/O are preserved, while factorial itself is allowed to wrap. -/
theorem call_refines (H depth : Nat) (caller : Source.State w) :
    Source.Refines program H depth (.call 1 self [.var 0])
      (fun k s => s = caller ∧ k < 2 ^ w ∧ k + 1 ≤ depth ∧ s.regs 0 = BitVec.ofNat w k)
      (fun result t => t = caller.setReg 1 (BitVec.ofNat w result)) Nat.factorial := by
  apply Source.Refines.call (spec := totalSpec w) id (recursive_total H)
    (show program[self]? = some factorial from rfl) rfl (by decide)
  · intro k s hs
    simp [Expr.ReadsBelow]
  · intro k s hs
    exact ⟨hs.2.1, by
      simpa [Source.State.enter_regs, Source.State.eval, Expr.eval] using hs.2.2.2⟩
  · intro k s hs
    exact hs.2.2.1
  · intro k s hs callee post
    change callee = (s.enter _).setReg 1 (value w k) at post
    subst callee
    change s.leave ((s.enter _).setReg 1 (value w k)) 1 (.var 1) =
      caller.setReg 1 (value w k)
    rw [Source.State.leave_enter_setReg, hs.1]

/-- The recursive contract exposes the complete body-state postcondition,
not merely the final return value. Its proof does not use the exact trace. -/
theorem body_contract (H k : Nat) :
    Source.RelContract 2 program H k factorial.body
      (fun s : Source.State w => k < 2 ^ w ∧ s.regs 0 = BitVec.ofNat w k)
      (fun entry finish => finish = entry.setReg 1 (value w k))
      (fun _ => 37 * k + 4) := by
  intro s hs
  obtain ⟨steps, t, hx, ⟨_, hp⟩, hb⟩ := recursive_contract H k s hs
  exact ⟨steps, t, hx, hp, hb⟩

/-- Every input in range terminates. The exact endpoint preserves the entire
caller state except its answer register, not just the final numeric result. -/
theorem body_measured (H k : Nat) (s : Source.State w)
    (hk : k < 2 ^ w) (hn : s.regs 0 = BitVec.ofNat w k) :
    Source.LocalMeasuredExec 2 program H k factorial.body (37 * k + 4)
      s (s.setReg 1 (value w k)) := by
  induction k generalizing s with
  | zero =>
      have hzero : s.eval (.var 0) = 0 := hn
      exact .iteFalse (c := .var 0) trivial hzero
        (.assign (value := .const 1) trivial)
  | succ k ih =>
      have hpred : s.eval (.bin .sub (.var 0) (.const 1)) = BitVec.ofNat w k := by
        change s.regs 0 - BitVec.ofNat w 1 = BitVec.ofNat w k
        rw [hn, encoded_pred]
      have hcallee := ih (s.enter [BitVec.ofNat w k]) (by omega) (by
        simp [Source.State.enter])
      have harguments :
          ∀ arg ∈ [Expr.bin .sub (.var 0) (.const 1)],
            arg.ReadsBelow H s.regs s.mem := by
        simp [Expr.ReadsBelow]
      have hbody : Source.LocalMeasuredExec 2 program H k factorial.body (37 * k + 4)
          (s.enter ([.bin .sub (.var 0) (.const 1)].map s.eval))
          ((s.enter [BitVec.ofNat w k]).setReg 1 (value w k)) := by
        simpa only [List.map_cons, List.map_nil, hpred] using hcallee
      have hcall := Source.LocalMeasuredExec.call (dst := 1) (fn := self)
        (show program[self]? = some factorial from rfl) rfl (by decide)
        harguments hbody (show factorial.result.ReadsBelow H _ _ from trivial)
      have hcall' : Source.LocalMeasuredExec 2 program H (k + 1)
          (.call 1 self [.bin .sub (.var 0) (.const 1)]) (37 * k + 34)
          s (s.setReg 1 (value w k)) := by
        simp only [show factorial.result = .var 1 from rfl,
          show factorial.locals = 2 from rfl, recursive_call_steps, leave_answer] at hcall
        simpa only [Nat.add_assoc] using hcall
      have hmul : (s.setReg 1 (value w k)).eval (.bin .mul (.var 0) (.var 1)) =
          value w (k + 1) := by
        simp only [Source.State.eval, Expr.eval, BinOp.eval_mul,
          Source.State.setReg_ne _ _ _ _ (by decide : (0 : Reg) ≠ 1),
          Source.State.setReg_same, hn, value_succ]
      have hassign : Source.LocalMeasuredExec 2 program H (k + 1)
          (.assign 1 (.bin .mul (.var 0) (.var 1))) 4
          (s.setReg 1 (value w k)) (s.setReg 1 (value w (k + 1))) := by
        have h := Source.LocalMeasuredExec.assign (control := 2) (program := program)
          (heapLimit := H) (d := k + 1) (s := s.setReg 1 (value w k))
          (dst := 1) (value := .bin .mul (.var 0) (.var 1)) ⟨trivial, trivial⟩
        simpa only [hmul, set_answer_twice,
          show LocalCompiler.stmtSize 2 (LocalCompiler.calleeLocals program)
              (.assign 1 (.bin .mul (.var 0) (.var 1))) = 4
            from rfl] using h
      have hnonzero : s.eval (.var 0) ≠ 0 := by
        change s.regs 0 ≠ 0
        intro hz
        have hnat := congrArg BitVec.toNat hz
        rw [hn, Word.ofNat_toNat_of_lt hk] at hnat
        change k + 1 = 0 at hnat
        omega
      have h := Source.LocalMeasuredExec.iteTrue (c := .var 0) (no := .assign 1 (.const 1))
        trivial hnonzero (.seq hcall' hassign)
      have hcount : 1 + 1 + (37 * k + 34 + 4) + 1 = 37 * (k + 1) + 4 := by omega
      simpa only [show (Expr.compile (.var 0) (ABI.scratch 2)).length = 1 from rfl,
        hcount] using h

/-- The public call restores every caller local other than its destination. -/
theorem call_measured (H k : Nat) (s : Source.State w)
    (hk : k < 2 ^ w) (hn : s.regs 0 = BitVec.ofNat w k) :
    Source.LocalMeasuredExec 2 program H (k + 1) (.call 1 self [.var 0])
      (37 * k + 32) s (s.setReg 1 (value w k)) := by
  have hbody := body_measured H k (s.enter ([.var 0].map s.eval)) hk (by
    simpa [Source.State.enter, Source.State.eval, Expr.eval] using hn)
  have hcall := Source.LocalMeasuredExec.call (dst := 1) (fn := self)
    (show program[self]? = some factorial from rfl) rfl (by decide)
    (show ∀ arg ∈ [Expr.var 0], arg.ReadsBelow H s.regs s.mem from by
      simp [Expr.ReadsBelow]) hbody
    (show factorial.result.ReadsBelow H _ _ from trivial)
  simp only [show factorial.result = .var 1 from rfl,
    show factorial.locals = 2 from rfl, initial_call_steps, leave_answer] at hcall
  simpa only [Nat.add_assoc] using hcall

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

end Ram.Examples.Factorial
