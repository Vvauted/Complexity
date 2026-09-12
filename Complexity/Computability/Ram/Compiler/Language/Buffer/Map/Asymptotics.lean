/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Execution
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic bounds for the compiled allocating map

The size-only bound exported by the actual map execution is linear when its
selected source callback has a uniform instruction bound. The coefficient
includes allocation, callback entry, traversal and the outer invocation; it is
independent of the input length and word width. Admissibility and capacity are
still obligations of the execution theorem, not consequences of this numerical
asymptotic statement.
-/

namespace Ram.LanguageCompiler.BufferMap

open Complexity.Language

/-- A uniform callback bound makes the proved invocation budget linear in the
input length. Clients need not unfold the compiler's traversal coefficients. -/
theorem isBigO_linearInvocationBound {inputKind outputKind : CellTy}
    {signatures : List Signature} (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (perElement : Nat) :
    Asymptotics.IsBigO Filter.atTop
      (fun length => (linearInvocationBound sourceProgram fn same perElement length : ℝ))
      (fun length : Nat => (length : ℝ)) := by
  let mapped := Buffer.Map.program sourceProgram fn same
  let coefficient := perElement + 14 +
    callCost mapped (Buffer.Map.calleeEntry inputKind outputKind fn) 0 + 36
  let fixed := LocalCompiler.Function.callSteps (programControl mapped)
    (lowerFunc mapped (Buffer.Map.entry inputKind outputKind signatures)) 53 + 1
  apply Asymptotics.IsBigO.of_bound ((coefficient + fixed : Nat) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with length positive
  have setup : fixed ≤ length * fixed := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right fixed positive
  have bound : linearInvocationBound sourceProgram fn same perElement length ≤
      (coefficient + fixed) * length := by
    change length * coefficient + fixed ≤ (coefficient + fixed) * length
    calc
      length * coefficient + fixed ≤ length * coefficient + length * fixed :=
        Nat.add_le_add_left setup _
      _ = (coefficient + fixed) * length := by rw [← Nat.mul_add, Nat.mul_comm]
  simpa only [Real.norm_natCast, ← Nat.cast_mul] using
    (Nat.cast_le.mpr bound :
      (linearInvocationBound sourceProgram fn same perElement length : ℝ) ≤
        (((coefficient + fixed) * length : Nat) : ℝ))

end Ram.LanguageCompiler.BufferMap
