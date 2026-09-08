/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Computability.Ram.Source.State
import Complexity.Computability.Ram.Source.Function.Time
import Complexity.Computability.Ram.Verification.Call
import Complexity.Computability.Ram.Verification.Function
import Complexity.Computability.Ram.Verification.Recursion.Basic
import Complexity.Computability.Ram.Verification.Recursion.Function
import Complexity.Computability.Ram.Verification.Recursion.Time
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Tactic.Ram.Total
import Mathlib.Data.Nat.Factorial.Basic

/-!
# A standalone recursive factorial function

The function is declared once with `ram_functions%`, independently of the input
and word width. Its correctness theorem returns a word and preserves arbitrary
caller state; it requires neither a stream driver nor a proposed time budget.
Separate time theorems measure the same recursive body and its actual calls.

The default local-frame compiler saves and restores the callee's declared locals
on every invocation. `factorialNat` names mathlib's `Nat.factorial` as the
mathematical specification: it never appears in a runtime instruction.
The result is factorial modulo the word range, so multiplication may wrap.
Exact natural-number results require the stated no-overflow premise.

`Examples.Ram.FactorialFunction` exposes function-value equations, and
`Examples.Ram.FunctionRun` runs this function directly. The optional input/output
adapter and its whole-program time proofs are in `Examples.Ram.FactorialStream`.
-/

namespace Ram.Examples.Factorial

/-- Both function names and local register names are resolved automatically.
The source does not maintain a numeric function table or a `self` index. -/
ram_def functions := ram_functions% {
  fn factorial(n) locals (answer) {
    if n {
      answer := call factorial(n - 1);
      answer := n * answer;
    } else {
      answer := 1;
    }
    return answer;
  }
}

def program : Program := functions.program

/-- Inspect the resolved declaration for the semantic proof below. -/
def factorial : Func := functions.function.factorial

/-- This resolved index is used only in proofs, never in the named source. -/
def self : Nat := functions.functionIndex.factorial

theorem program_expands : program = [factorial] := rfl

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
  pre k s := k < 2 ^ w ∧ s.regs functions.localReg.factorial.n = BitVec.ofNat w k
  post k entry finish := finish = entry.setReg functions.localReg.factorial.answer (value w k)
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

/-- Translate the body specification to arguments and the actual returned
value once, for both recursive hypotheses and external callers. -/
private theorem function_contract_of_body {H k : Nat}
    (correct : (totalSpec w).Correct program H k) :
    Source.FunctionContract program H k factorial
      (fun args _ => k < 2 ^ w ∧ args = functions.arguments.factorial (BitVec.ofNat w k))
      (fun _ entry result finish => result = value w k ∧ finish = entry) := by
  apply Source.FunctionContract.of_body correct
  · rintro args entry ⟨_, rfl⟩
    exact functions.arguments_length.factorial _
  · decide
  · rintro args entry ⟨hk, rfl⟩
    exact ⟨hk, rfl⟩
  · rintro args entry ⟨_, rfl⟩ callee result
    change callee = (entry.enter _).setReg functions.localReg.factorial.answer (value w k)
      at result
    subst callee
    exact ⟨rfl, rfl⟩

/-- Prove factorial using ordinary well-founded recursion and mathlib's
factorial equation. Recursive hypotheses describe function arguments and
returned values, not callee frames. No time bound enters this proof. -/
theorem recursive_total (H : Nat) :
    ∀ k, (totalSpec w).Correct program H k := by
  apply (totalSpec w).verify_wellFounded_function Nat.lt_wfRel.wf
    (fun _ => function_contract_of_body)
  intro k ih s hs
  obtain ⟨hk, hn⟩ := hs
  cases k with
  | zero =>
      ram_total_vc [totalSpec, factorial, functions.body_eq.factorial,
        functions.result_eq.factorial, hn, value, factorialNat, Nat.factorial_zero]
  | succ k =>
      have hnonzero : s.eval (.var functions.localReg.factorial.n) ≠ 0 := by
        intro hz
        have hnat := congrArg BitVec.toNat hz
        change (s.regs functions.localReg.factorial.n).toNat = 0 at hnat
        rw [hn, Word.ofNat_toNat_of_lt hk] at hnat
        omega
      change Source.Verification.TotalWP program H (k + 1)
        functions.function.factorial.body _ s
      simp only [totalSpec]
      rw [functions.body_eq.factorial, Source.Verification.TotalWP.ite_iff]
      refine ⟨trivial, ?_⟩
      rw [if_neg hnonzero, Source.Verification.TotalWP.seq_iff]
      ram_total_apply (ih k (Nat.lt_succ_self k))
      · exact functions.function_lookup.factorial
      · simp [Expr.ReadsBelow]
      · refine ⟨by omega, ?_⟩
        simp [functions.arguments.factorial, Source.State.eval, Expr.eval, hn, encoded_pred]
      · exact Nat.le_refl _
      · rintro result finish ⟨rfl, rfl⟩ _
        ram_total_vc [totalSpec, factorial, functions.result_eq.factorial, hn, value_succ]
        funext r
        by_cases hr : r = functions.localReg.factorial.answer <;> simp [hr]

/-- The independently callable function returns factorial and preserves all
caller state. Arguments and the result are explicit; no stream adapter or
destination register occurs in this specification. -/
theorem function_contract (H k : Nat) (hk : k < 2 ^ w) :
    Source.FunctionContract program H k factorial
      (fun args _ => args = functions.arguments.factorial (BitVec.ofNat w k))
      (fun _ entry result finish => result = value w k ∧ finish = entry) := by
  exact (function_contract_of_body (recursive_total H k)).consequence
    (fun _ _ args => ⟨hk, args⟩) (fun _ _ _ _ _ result => result)

/-- Apply factorial directly to a word argument, without a `main` or I/O. -/
theorem function_runs (H k : Nat) (hk : k < 2 ^ w) (entry : Source.State w) :
    Source.FunctionExec program H k factorial
      (functions.arguments.factorial (BitVec.ofNat w k)) entry (value w k) entry := by
  obtain ⟨result, finish, execution, rfl, rfl⟩ :=
    function_contract H k hk _ entry rfl
  exact execution

/-- Any completed invocation has the mathematical factorial as its returned
natural number when that result fits. This is a property of the implementation,
not the definition of its return value. -/
theorem function_result {H depth k : Nat} {entry finish : Source.State w} {result : Word w}
    (hk : k < 2 ^ w) (hresult : Nat.factorial k < 2 ^ w)
    (execution : Source.FunctionExec program H depth factorial
      (functions.arguments.factorial (BitVec.ofNat w k)) entry result finish) :
    result.toNat = Nat.factorial k ∧ finish = entry := by
  obtain ⟨rfl, rfl⟩ := execution.deterministic (function_runs H k hk entry)
  exact ⟨Word.ofNat_toNat_of_lt hresult, rfl⟩

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

/-- The function-body time bound is independent of its result specification.
The enclosing call's argument and frame costs are accounted for separately. -/
theorem function_timeBound (H k : Nat) (hk : k < 2 ^ w) :
    Source.FunctionTimeBound 2 program H k factorial
      (fun args _ => args = functions.arguments.factorial (BitVec.ofNat w k))
      (fun _ _ => 37 * k + 4) := by
  apply Source.FunctionTimeBound.of_body (recursive_timeBound H k)
  · rintro args entry rfl
    exact ⟨hk, rfl⟩
  · intros
    exact Nat.le_refl _

/-- Combine independently proved behavior and time for the recursive body. -/
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
  intro k
  apply Source.Verification.verify_total
  rintro s ⟨rfl, hk, hd, hn⟩
  ram_total_apply (function_contract H k hk)
  · exact functions.function_lookup.factorial
  · intro expr hexpr
    simp only [List.mem_singleton] at hexpr
    subst expr
    trivial
  · simpa [functions.arguments.factorial, Source.State.eval, Expr.eval] using hn
  · exact hd
  · rintro result finish ⟨rfl, rfl⟩ _
    rfl

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

end Ram.Examples.Factorial
