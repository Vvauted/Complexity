/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Named.Declaration

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
  apply Source.FunctionContract.of_wp
  · rintro args entry rfl
    exact functions.arguments_length.square x
  · decide
  · rintro args entry rfl
    rw [functions.body_eq.square, Source.Verification.TotalWP.skip_iff]
    exact ⟨by simp [functions.result_eq.square, Expr.ReadsBelow], rfl, rfl⟩

/-- The two calls compose through their returned values. Their private local
frames do not appear in the continuation proof, and no separate specification
of intermediate local-variable states is needed. -/
theorem squaredNorm_contract (heapLimit : Nat) (x y : Word w) :
    Source.FunctionContract functions.program heapLimit 1 functions.function.squaredNorm
      (fun args _ => args = functions.arguments.squaredNorm x y)
      (fun _ entry value finish => value = x * x + y * y ∧ finish = entry) := by
  apply Source.FunctionContract.of_wp
  · rintro args entry rfl
    exact functions.arguments_length.squaredNorm x y
  · decide
  · rintro args entry rfl
    rw [functions.body_eq.squaredNorm, Source.Verification.TotalWP.seq_iff]
    apply (square_contract heapLimit x).wp_call
    · exact functions.function_lookup.square
    · simp [Expr.ReadsBelow]
    · rfl
    · decide
    · rintro value finish ⟨rfl, rfl⟩ _
      apply (square_contract heapLimit y).wp_call
      · exact functions.function_lookup.square
      · simp [Expr.ReadsBelow]
      · rfl
      · decide
      · rintro value finish ⟨rfl, rfl⟩ _
        exact ⟨by simp [functions.result_eq.squaredNorm, Expr.ReadsBelow], rfl, rfl⟩

/-- The program's semantic value is the sum of squares, independently of
the caller's registers, memory and streams. The equation includes termination. -/
theorem squaredNorm_eval (heapLimit : Nat) (x y : Word w) (entry : Source.State w) :
    functions.function.squaredNorm.eval functions.program heapLimit
      (functions.arguments.squaredNorm x y) entry = Part.some (x * x + y * y, entry) := by
  obtain ⟨value, finish, equation, rfl, rfl⟩ :=
    (squaredNorm_contract heapLimit x y).eval_spec
      (args := functions.arguments.squaredNorm x y) (entry := entry) rfl
  exact equation

/-- For encoded natural arguments the result is the encoded mathematical
sum of squares; encoding retains the word model's modular arithmetic. -/
theorem squaredNorm_eval_ofNat (heapLimit x y : Nat) (entry : Source.State w) :
    functions.function.squaredNorm.eval functions.program heapLimit
      (functions.arguments.squaredNorm (BitVec.ofNat w x) (BitVec.ofNat w y)) entry =
        Part.some (BitVec.ofNat w (x * x + y * y), entry) := by
  simpa only [BitVec.ofNat_add, BitVec.ofNat_mul] using
    squaredNorm_eval heapLimit (BitVec.ofNat w x) (BitVec.ofNat w y) entry

end Ram.Examples.LocalBindings
