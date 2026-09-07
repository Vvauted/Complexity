/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.ExprCompile

/-!
# The same arithmetic program is executed and proved

This program reads two words, compiles a source multiplication expression,
writes its result, and halts. The theorem counts the entire run, including input,
output, and halt. No operation-specific cost annotation is present in the source.
-/

namespace Ram.Examples

def productExpr : Expr := .bin .mul (.var 0) (.var 1)

def multiply : Code :=
  [.read 0, .read 1] ++ productExpr.compile 2 ++ [.write 2, .halt]

/-- The instruction count is calculated from compiled code, not assumed by a
source-level multiplication specification. -/
theorem multiply_length : multiply.length = 7 := rfl

/-- The executable runner and the machine relation agree on the complete
program, and its observable output is the specified machine-word product. -/
theorem multiply_exec (x y : Word w) :
    ∃ t, Exec multiply multiply.length (State.initial [x, y]) t ∧
      t.status = .halted ∧ t.output = [x * y] := by
  let inputState := execInstr (.read 1) (execInstr (.read 0) (State.initial [x, y]))
  let resultState := execBlock (productExpr.compile 2) inputState
  let finalState := execInstr .halt (execInstr (.write 2) resultState)
  have hrun : runExact multiply multiply.length (State.initial [x, y]) =
      some finalState := rfl
  refine ⟨finalState, runExact_iff.mp hrun, rfl, ?_⟩
  have hvalue := (Expr.compile_correct (e := productExpr) (dst := 2)
    (by decide) inputState).value
  have hout : resultState.outputRev = [] :=
    (Expr.compile_correct (e := productExpr) (dst := 2) (by decide) inputState).output
  change (resultState.regs 2 :: resultState.outputRev).reverse = [x * y]
  rw [hout, hvalue]
  rfl

/-- Successful termination is part of the certificate, not an implication
conditioned on an execution that might never exist. -/
theorem multiply_terminates (x y : Word w) :
    ∃ t, TerminatesWithin multiply multiply.length (State.initial [x, y]) t ∧
      t.output = [x * y] := by
  obtain ⟨t, he, ht, ho⟩ := multiply_exec x y
  exact ⟨t, ⟨_, Nat.le_refl _, he, ht⟩, ho⟩

/-- The same complete program computes mathematical multiplication modulo the
word range for arbitrary input words. -/
theorem multiply_modular (x y : Word w) :
    ∃ t, TerminatesWithin multiply multiply.length (State.initial [x, y]) t ∧
      t.output.map BitVec.toNat = [(x.toNat * y.toNat) % 2 ^ w] := by
  obtain ⟨t, he, ho⟩ := multiply_terminates x y
  refine ⟨t, he, ?_⟩
  simp only [ho, List.map_cons, List.map_nil, BitVec.toNat_mul]

/-- When the inputs and product fit, the result is the exact mathematical
product. The width is arbitrary and the compiled program is unchanged. -/
theorem multiply_exact {a b w : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hab : a * b < 2 ^ w) :
    ∃ t, TerminatesWithin multiply multiply.length
      (State.initial [BitVec.ofNat w a, BitVec.ofNat w b]) t ∧
      t.output.map BitVec.toNat = [a * b] := by
  obtain ⟨t, he, ho⟩ := multiply_modular (BitVec.ofNat w a) (BitVec.ofNat w b)
  refine ⟨t, he, ?_⟩
  simpa only [Word.ofNat_toNat_of_lt ha, Word.ofNat_toNat_of_lt hb,
    Nat.mod_eq_of_lt hab] using ho

end Ram.Examples
