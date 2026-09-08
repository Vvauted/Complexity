/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Tactic.Ram.Total

/-!
# Composing functions with local bindings

The function `squaredNorm` calls `square` twice and keeps both returned values
in lexical locals. Neither function needs a `main` program, input/output
streams or a hand-written register table. Their correctness proofs use the
same source declarations and the reusable contract for `square`.

The result equation observes the implementation through `Ram.Func.eval`.
Arithmetic is machine-word arithmetic: the natural-number corollary encodes
the sum of squares modulo the word range, without claiming that overflow is
absent. These are semantic observations, not a second executable algorithm.

The independent cost proof reads the lengths of the two compiled calls: each
invocation of `square` takes 23 transitions, including its multiplication in
the return expression and its calling-convention code. Thus `squaredNorm` has
body time 46. Its own final addition and enclosing call/return are outside
`Ram.Func.bodyTime`; they must be charged when this function is called.
-/

namespace Ram.Examples.LocalBindings

/-- Local slots are inferred from parameters and lexical value bindings. -/
ram_def functions := ram_functions% {
  fn square(x) {
    return x * x;
  }
  fn squaredNorm(x, y) {
    let sx ← call square(x);
    let sy ← call square(y);
    return sx + sy;
  }
}

/-- Squaring returns a word and leaves all caller state unchanged. -/
theorem square_contract (heapLimit : Nat) (x : Word w) :
    Source.FunctionContract functions.program heapLimit 0 functions.function.square
      (fun args _ => args = functions.arguments.square x)
      (fun _ entry value finish => value = x * x ∧ finish = entry) := by
  ram_total_vc args entry rfl [functions.body_eq.square, functions.result_eq.square]

/-- The two calls compose through their returned values. Their private local
frames do not appear in the continuation proof, and no separate specification
of intermediate local-variable states is needed. -/
theorem squaredNorm_contract (heapLimit : Nat) (x y : Word w) :
    Source.FunctionContract functions.program heapLimit 1 functions.function.squaredNorm
      (fun args _ => args = functions.arguments.squaredNorm x y)
      (fun _ entry value finish => value = x * x + y * y ∧ finish = entry) := by
  ram_total_vc args entry rfl [functions.body_eq.squaredNorm, functions.result_eq.squaredNorm]
  ram_total_apply (square_contract heapLimit x) [functions.function_lookup.square]
  ram_total_apply (square_contract heapLimit y) [functions.function_lookup.square]

/-- The program's semantic value is the sum of squares, independently of
the caller's registers, memory and streams. The equation includes termination. -/
theorem squaredNorm_eval (heapLimit : Nat) (x y : Word w) (entry : Source.State w) :
    functions.eval.squaredNorm x y heapLimit entry = Part.some (x * x + y * y, entry) := by
  obtain ⟨value, finish, equation, rfl, rfl⟩ :=
    (squaredNorm_contract heapLimit x y).eval_spec
      (args := functions.arguments.squaredNorm x y) (entry := entry) rfl
  exact equation

/-- For encoded natural arguments the result is the encoded mathematical
sum of squares; encoding retains the word model's modular arithmetic. -/
theorem squaredNorm_eval_ofNat (heapLimit x y : Nat) (entry : Source.State w) :
    functions.eval.squaredNorm (BitVec.ofNat w x) (BitVec.ofNat w y) heapLimit entry =
        Part.some (BitVec.ofNat w (x * x + y * y), entry) := by
  simpa only [BitVec.ofNat_add, BitVec.ofNat_mul] using
    squaredNorm_eval heapLimit (BitVec.ofNat w x) (BitVec.ofNat w y) entry

private theorem square_call_steps {control heapLimit depth steps dst arg : Nat}
    {entry finish : Source.State w}
    (execution : Source.LocalMeasuredExec control functions.program heapLimit depth
      (.call dst functions.functionIndex.square [.var arg]) steps entry finish) :
    steps = 23 := by
  cases execution with
  | «call» lookup _ _ _ body _ =>
      have found : _ = functions.function.square :=
        Option.some.inj (lookup.symm.trans functions.function_lookup.square)
      cases found
      rw [functions.body_eq.square] at body
      cases body
      simp only [ABI.callLocals_steps_eq]
      change 1 + 0 + 3 + 7 * 1 + 1 + 11 = 23
      decide

/-- Every completed body execution has the same count, obtained by adding
the actual generated call blocks. No result specification enters this proof. -/
theorem squaredNorm_body_steps {control heapLimit depth steps : Nat}
    {entry finish : Source.State w}
    (execution : Source.LocalMeasuredExec control functions.program heapLimit depth
      functions.function.squaredNorm.body steps entry finish) :
    steps = 46 := by
  rw [functions.body_eq.squaredNorm] at execution
  cases execution with
  | seq first second => rw [square_call_steps first, square_call_steps second]

/-- The exact count yields an independent conditional bound on invocations.
Termination is supplied separately by `squaredNorm_contract`. -/
theorem squaredNorm_timeBound (control heapLimit depth : Nat)
    (P : List (Word w) → Source.State w → Prop) :
    Source.FunctionTimeBound control functions.program heapLimit depth
      functions.function.squaredNorm P (fun _ _ => 46) := by
  intro args entry _ steps value finish invocation
  obtain ⟨_, _, callee, body, _, _, _⟩ := invocation
  exact Nat.le_of_eq (squaredNorm_body_steps body)

/-- Functional correctness supplies the invocation; the separate count proof
identifies its cost without replaying the value computation. -/
theorem squaredNorm_measured (heapLimit : Nat) (x y : Word w) (entry : Source.State w) :
    Source.FunctionMeasuredExec functions.registers functions.program heapLimit 1
      functions.function.squaredNorm (functions.arguments.squaredNorm x y) 46
      entry (x * x + y * y) entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    squaredNorm_contract heapLimit x y (functions.arguments.squaredNorm x y) entry rfl
  obtain ⟨steps, measured⟩ := execution.exists_measured functions.registers
  have count : steps = 46 := by
    obtain ⟨_, _, callee, body, _, _, _⟩ := measured
    exact squaredNorm_body_steps body
  exact count ▸ measured

/-- Body time is a property of the same invocation as `squaredNorm_eval`,
not a supplied annotation. Each of its two completed calls takes 23 steps. -/
theorem squaredNorm_bodyTime (heapLimit : Nat) (x y : Word w) (entry : Source.State w) :
    functions.bodyTime.squaredNorm x y heapLimit entry = Part.some 46 :=
  (squaredNorm_measured heapLimit x y entry).bodyTime_eq_some

end Ram.Examples.LocalBindings
