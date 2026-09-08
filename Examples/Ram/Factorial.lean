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
import Complexity.Computability.Ram.Verification.Recursion.Time
import Complexity.Computability.Ram.Verification.Time.Exact
import Complexity.Tactic.Ram.Budget
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
        (.seq (.call [1] self [.bin .sub (.var 0) (.const 1)])
          (.assign 1 (.bin .mul (.var 0) (.var 1))))
        (.assign 1 (.const 1))
      results := [.var 1] } := rfl

/-- The standard mathematical factorial, not a machine operation. -/
abbrev factorialNat : Nat → Nat := Nat.factorial

def value (w k : Nat) : Word w := BitVec.ofNat w (factorialNat k)

theorem value_toNat (w k : Nat) :
    (value w k).toNat = factorialNat k % 2 ^ w := BitVec.toNat_ofNat _ _

theorem value_succ (w k : Nat) :
    value w (k + 1) = BitVec.ofNat w (k + 1) * value w k := by
  simp only [value, factorialNat, Nat.factorial_succ, BitVec.ofNat_mul]

/-- The callee's local registers are genuinely discarded on return. In
particular, the caller's original `n` survives its recursive call. -/
theorem leave_answer (s : Source.State w) (args : List (Word w)) (answer : Word w) :
    s.leave ((s.enter args).setReg 1 answer) [1] [.var 1] = s.setReg 1 answer :=
  Source.State.leave_enter_setReg s args 1 1 answer

private theorem encoded_pred (w k : Nat) :
    BitVec.ofNat w (k + 1) - BitVec.ofNat w 1 = BitVec.ofNat w k := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

/-- The independently callable function returns factorial and preserves all
caller state. Ordinary natural-number induction supplies the recursive call's
argument/result contract; generated parameter binding and return equations
handle local state. No stream adapter or time bound enters this proof. -/
theorem function_contract (H k : Nat) (hk : k < 2 ^ w) :
    Source.FunctionContract program H k factorial
      (fun args _ => args = functions.arguments.factorial (BitVec.ofNat w k))
      (fun _ entry result finish => result = [value w k] ∧ finish = entry) := by
  revert hk
  induction k with
  | zero =>
      intro _
      ram_total_vc args entry rfl [factorial, functions.body_eq.factorial,
        functions.result_eq.factorial, value, factorialNat, Nat.factorial_zero]
  | succ k ih =>
      intro hk
      have hnonzero : BitVec.ofNat w (k + 1) ≠ BitVec.ofNat w 0 := by
        intro hz
        have hnat := congrArg BitVec.toNat hz
        rw [Word.ofNat_toNat_of_lt hk, BitVec.toNat_ofNat, Nat.zero_mod] at hnat
        omega
      ram_total_vc args entry rfl [factorial, functions.body_eq.factorial,
        functions.result_eq.factorial]
      rw [if_neg hnonzero]
      ram_total_apply (ih (by omega)) [functions.function_lookup.factorial,
        encoded_pred, value_succ]

/-- Apply factorial directly to a word argument, without a `main` or I/O. -/
theorem function_runs (H k : Nat) (hk : k < 2 ^ w) (entry : Source.State w) :
    Source.FunctionExec program H k factorial
      (functions.arguments.factorial (BitVec.ofNat w k)) entry [value w k] entry := by
  obtain ⟨result, finish, execution, rfl, rfl⟩ :=
    function_contract H k hk _ entry rfl
  exact execution

/-- Any completed invocation has the mathematical factorial as its returned
natural number when that result fits. This is a property of the implementation,
not the definition of its return value. -/
theorem function_result {H depth k : Nat} {entry finish : Source.State w} {result : Word w}
    (hk : k < 2 ^ w) (hresult : Nat.factorial k < 2 ^ w)
    (execution : Source.FunctionExec program H depth factorial
      (functions.arguments.factorial (BitVec.ofNat w k)) entry [result] finish) :
    result.toNat = Nat.factorial k ∧ finish = entry := by
  obtain ⟨returned, rfl⟩ := execution.deterministic (function_runs H k hk entry)
  have result_eq : result = value w k := List.cons.inj returned |>.1
  subst result
  exact ⟨Word.ofNat_toNat_of_lt hresult, rfl⟩

/-- Length calculation on the actual generated setup and return instruction
lists. This includes all individual saves, restores, and jumps. -/
theorem recursive_call_steps (bodySteps : Nat) :
    (ABI.callPrefixLocals 2 2 [.bin .sub (.var 0) (.const 1)] 0).length + 1 + bodySteps +
      (ABI.returnCodeResultsLocals 2 2 [.var 1]).length + 1 = bodySteps + 30 := by
  change 16 + 1 + bodySteps + 12 + 1 = bodySteps + 30
  omega

theorem initial_call_steps (bodySteps : Nat) :
    (ABI.callPrefixLocals 2 2 [.var 0] 0).length + 1 + bodySteps +
      (ABI.returnCodeResultsLocals 2 2 [.var 1]).length + 1 = bodySteps + 28 := by
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
    (37 * k + 4) + (ABI.returnCodeResultsLocals 2 2 [.var 1]).length + 1 = 37 * k + 34
  simpa only [Nat.add_assoc] using recursive_call_steps (37 * k + 4)

theorem initial_call_budget (w k : Nat) :
    (recursionSpec w).callBudget 2 [.var 0] k = 37 * k + 32 := by
  change (ABI.callPrefixLocals 2 2 [.var 0] 0).length + 1 + (37 * k + 4) +
    (ABI.returnCodeResultsLocals 2 2 [.var 1]).length + 1 = 37 * k + 32
  simpa only [Nat.add_assoc] using initial_call_steps (37 * k + 4)

private theorem predecessor_pre (k : Nat) (s : Source.State w)
    (hs : (totalSpec w).pre (k + 1) s) :
    (totalSpec w).pre k (s.enter ([.bin .sub (.var 0) (.const 1)].map s.eval)) := by
  have hpred : s.eval (.bin .sub (.var 0) (.const 1)) = BitVec.ofNat w k := by
    change s.regs 0 - BitVec.ofNat w 1 = BitVec.ofNat w k
    rw [hs.2, encoded_pred]
  exact ⟨by have hk := hs.1; omega, by simp [Source.State.enter_regs, hpred]⟩

/-- Recover the full body-state specification for clients that inspect local
effects. This unfolds one body step and reuses the callable factorial theorem;
the stronger local endpoint is proved explicitly, not inferred from return-state
restoration or from a time bound. -/
theorem recursive_total (H : Nat) :
    ∀ k, (totalSpec w).Correct program H k := by
  intro k s hs
  change Source.Verification.TotalWP program H k factorial.body
    (fun finish => (∀ result ∈ factorial.results,
        result.ReadsBelow H finish.regs finish.mem) ∧
      (totalSpec w).post k s finish) s
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
      ram_total_apply (function_contract H k (by omega))
      · exact functions.function_lookup.factorial
      · rfl
      · simp [Expr.ReadsBelow]
      · simp [functions.arguments.factorial, Source.State.eval, Expr.eval, hn, encoded_pred]
      · exact Nat.le_refl _
      · rintro result finish ⟨rfl, rfl⟩ _
        ram_total_vc [totalSpec, factorial, functions.result_eq.factorial, hn, value_succ]
        funext r
        by_cases hr : r = functions.localReg.factorial.answer <;> simp [hr]

/-- A single mathematical induction proves the exact recurrence
`T (k + 1) = T k + 37`. Public cost rules handle the measured branches,
recursive call and straight-line continuation; no callee state is reconstructed. -/
theorem recursive_timeExact (H : Nat) :
    ∀ k, Source.TimeExact 2 program H k factorial.body ((totalSpec w).pre k)
      (fun _ => 37 * k + 4) := by
  intro k
  induction k with
  | zero =>
      change Source.TimeExact 2 program H 0 functions.function.factorial.body _ _
      rw [functions.body_eq.factorial]
      apply Source.TimeExact.congr_cost
      · apply Source.TimeExact.ite_of_eq_zero
        · intro s hs
          exact hs.2
        · exact Source.TimeExact.of_isStraightLine trivial
      · intro s hs
        ram_bound
  | succ k ih =>
      change Source.TimeExact 2 program H (k + 1) functions.function.factorial.body _ _
      rw [functions.body_eq.factorial]
      apply Source.TimeExact.congr_cost
      · apply Source.TimeExact.ite_of_ne_zero
        · intro s hs zero
          have decoded := congrArg BitVec.toNat zero
          change (s.regs functions.localReg.factorial.n).toNat = 0 at decoded
          rw [hs.2, Word.ofNat_toNat_of_lt hs.1] at decoded
          omega
        · apply Source.TimeExact.seq_const
          · exact Source.TimeExact.call
              (show program[self]? = some factorial from rfl) (predecessor_pre k) ih
          · exact Source.TimeExact.of_isStraightLine trivial
      · intro s hs
        ram_bound [factorial, functions.result_eq.factorial, functions.locals_eq.factorial]

/-- The independent upper bound follows from the exact cost equation, without
another recursive proof or a proposed budget in the functional specification. -/
theorem recursive_timeBound (H : Nat) :
    ∀ k, Source.TimeBound 2 program H k factorial.body ((totalSpec w).pre k)
      (fun _ => 37 * k + 4) :=
  fun k => (recursive_timeExact H k).timeBound

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
    Source.Refines program H depth (.call [1] self [.var 0])
      (fun k s => s = caller ∧ k < 2 ^ w ∧ k + 1 ≤ depth ∧ s.regs 0 = BitVec.ofNat w k)
      (fun result t => t = caller.setReg 1 (BitVec.ofNat w result)) Nat.factorial := by
  intro k
  apply Source.Verification.verify_total
  rintro s ⟨rfl, hk, hd, hn⟩
  ram_total_apply (function_contract H k hk)
  · exact functions.function_lookup.factorial
  · rfl
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
  obtain ⟨finish, execution, _, post⟩ := recursive_total H k s ⟨hk, hn⟩
  change finish = s.setReg 1 (value w k) at post
  subst finish
  exact execution.measured_of_timeExact (recursive_timeExact H k) ⟨hk, hn⟩

/-- The public call restores every caller local other than its destination. -/
theorem call_measured (H k : Nat) (s : Source.State w)
    (hk : k < 2 ^ w) (hn : s.regs 0 = BitVec.ofNat w k) :
    Source.LocalMeasuredExec 2 program H (k + 1) (.call [1] self [.var 0])
      (37 * k + 32) s (s.setReg 1 (value w k)) := by
  obtain ⟨finish, execution, post⟩ :=
    call_refines H (k + 1) s k s ⟨rfl, hk, Nat.le_refl _, hn⟩
  change finish = s.setReg 1 (value w k) at post
  subst finish
  have cost : Source.TimeExact 2 program H (k + 1) (.call [1] self [.var 0])
      (fun current => current = s) (fun _ => 37 * k + 32) := by
    apply Source.TimeExact.congr_cost
    · apply Source.TimeExact.call (show program[self]? = some factorial from rfl)
        (body := recursive_timeExact H k)
      rintro current rfl
      exact ⟨hk, by simpa [Source.State.enter, Source.State.eval, Expr.eval] using hn⟩
    · intro current hcurrent
      ram_bound [factorial, functions.result_eq.factorial, functions.locals_eq.factorial]
  exact execution.measured_of_timeExact cost rfl

end Ram.Examples.Factorial
