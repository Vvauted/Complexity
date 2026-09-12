/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Function
import Complexity.Data.List.Fold
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Numerical and asymptotic bounds for compiled linked-list folding

Callback charges are ordinary list sums evaluated at the accumulator before
each element. The same invocation envelope separates those charges from linear
traversal overhead and fixed outer call work. A uniform callback budget yields
a size-only affine envelope, including for an empty input.

These are numerical consequences of the existing execution bound, not another
cost semantics or a termination argument. Word ranges, represented inputs and
actual arena capacity remain obligations of the execution theorem. A callback
bound need hold only along the mathematical prefixes actually visited.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- Callback charges form an ordinary list sum at the fold's actual prefixes;
no extra visit trace or host execution is introduced. -/
theorem accumulated_eq_sum_mapIdx (step : α → CellValue kind → α)
    (charge : α → CellValue kind → Nat) (initial : α)
    (values : _root_.List (CellValue kind)) :
    accumulated step charge initial values =
      (values.mapIdx (fun index head => charge ((values.take index).foldl step initial) head)).sum := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      rw [_root_.List.sum_mapIdx_foldl_take_cons, accumulated, ih]

/-- A constant callback budget contributes exactly one charge per element,
independently of the accumulator trajectory. -/
theorem accumulated_const (step : α → CellValue kind → α) (perElement : Nat)
    (initial : α) (values : _root_.List (CellValue kind)) :
    accumulated step (fun _ _ => perElement) initial values = values.length * perElement := by
  induction values generalizing initial with
  | nil => simp only [accumulated, _root_.List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      simp only [accumulated, _root_.List.length_cons, ih, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Only visited prefixes need satisfy the per-element envelope; unrelated
accumulators and values impose no restriction on the callback's bound. -/
theorem accumulated_le_const (step : α → CellValue kind → α)
    (charge : α → CellValue kind → Nat) (perElement : Nat) (initial : α)
    (values : _root_.List (CellValue kind))
    (bounded : Complexity.Language.List.Fold.Admissible step
      (fun accumulator head => charge accumulator head ≤ perElement) initial values) :
    accumulated step charge initial values ≤ values.length * perElement := by
  induction values generalizing initial with
  | nil => simp only [accumulated, _root_.List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      obtain ⟨headBound, tailBound⟩ :=
        (Complexity.Language.List.Fold.admissible_cons step _ initial head tail).mp bounded
      change charge initial head + accumulated step charge (step initial head) tail ≤
        (tail.length + 1) * perElement
      calc
        _ ≤ perElement + tail.length * perElement := Nat.add_le_add headBound (ih _ tailBound)
        _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- A size-only affine envelope for the callable fold body with a uniform
callback budget. It includes body initialization, leaving the enclosing call
and halt to the caller. Its coefficients belong to the actual linked program. -/
def linearFunctionBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (perElement length : Nat) : Nat :=
  let folded := Complexity.Language.List.Fold.program sourceProgram fn same
  length * (perElement + callCost folded
    (Complexity.Language.List.Fold.calleeEntry accTy kind fn) 0 + 2 * fieldCount accTy + 45) +
      (2 * fieldCount accTy + 23)

/-- A constant callback budget specializes the existing callable-body envelope
without another traversal proof or a new instruction-cost model. -/
theorem functionBound_const (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (perElement : Nat) (initial : α)
    (values : _root_.List (CellValue kind)) :
    functionBound sourceProgram fn same step (fun _ _ => perElement) initial values =
      linearFunctionBound sourceProgram fn same perElement values.length := by
  simp only [functionBound, remainingCost_eq_sum, accumulated_const,
    linearFunctionBound, Nat.mul_add]
  omega

/-- The complete invocation budget is an ordinary sum of accumulator-dependent
callback bounds, linear traversal work and fixed outer call/return/halt work. -/
theorem invocationBound_eq_sum (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (initial : α) (values : _root_.List (CellValue kind)) :
    invocationBound sourceProgram fn same step bound initial values =
      (values.mapIdx (fun index head => bound ((values.take index).foldl step initial) head)).sum +
        values.length *
          (callCost (Complexity.Language.List.Fold.program sourceProgram fn same)
            (Complexity.Language.List.Fold.calleeEntry accTy kind fn) 0 +
              2 * fieldCount accTy + 45) +
        LocalCompiler.Function.callSteps
          (programControl (Complexity.Language.List.Fold.program sourceProgram fn same))
          (lowerFunc (Complexity.Language.List.Fold.program sourceProgram fn same)
            (Complexity.Language.List.Fold.entry accTy kind signatures))
          (2 * fieldCount accTy + 23) + 1 := by
  simp only [invocationBound, remainingCost_eq_sum, accumulated_eq_sum_mapIdx,
    LocalCompiler.Function.callSteps_eq]
  omega

/-- A size-only affine envelope for a uniformly bounded callback. Its remaining
coefficients come from the selected source implementation and actual compiler. -/
def linearInvocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (perElement length : Nat) : Nat :=
  let folded := Complexity.Language.List.Fold.program sourceProgram fn same
  length * (perElement + callCost folded
    (Complexity.Language.List.Fold.calleeEntry accTy kind fn) 0 + 2 * fieldCount accTy + 45) +
      LocalCompiler.Function.callSteps (programControl folded)
        (lowerFunc folded (Complexity.Language.List.Fold.entry accTy kind signatures))
        (2 * fieldCount accTy + 23) + 1

/-- A constant callback budget specializes the complete invocation envelope
exactly, without another traversal proof or a price for native `List.foldl`. -/
theorem invocationBound_const (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (perElement : Nat) (initial : α)
    (values : _root_.List (CellValue kind)) :
    invocationBound sourceProgram fn same step (fun _ _ => perElement) initial values =
      linearInvocationBound sourceProgram fn same perElement values.length := by
  rw [invocationBound_eq_sum,
    ← accumulated_eq_sum_mapIdx step (fun _ _ => perElement) initial values, accumulated_const]
  simp only [linearInvocationBound, Nat.mul_add]
  omega

/-- A callback whose bound varies with its accumulator inherits the same
size-only envelope whenever the bound fits at every actually visited prefix. -/
theorem invocationBound_le_linear (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (perElement : Nat) (initial : α) (values : _root_.List (CellValue kind))
    (bounded : Complexity.Language.List.Fold.Admissible step
      (fun accumulator head => bound accumulator head ≤ perElement) initial values) :
    invocationBound sourceProgram fn same step bound initial values ≤
      linearInvocationBound sourceProgram fn same perElement values.length := by
  have charges := accumulated_le_const step bound perElement initial values bounded
  rw [invocationBound_eq_sum, ← accumulated_eq_sum_mapIdx]
  simp only [linearInvocationBound, Nat.mul_add]
  omega

/-- The proved size-only invocation envelope is `O(length)`. Mathlib supplies
constant multiplication, negligible fixed overhead and addition; clients need
not open the compiler coefficients to use this asymptotic bound. -/
theorem isBigO_linearInvocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (perElement : Nat) :
    Asymptotics.IsBigO Filter.atTop
      (fun length => (linearInvocationBound sourceProgram fn same perElement length : ℝ))
      (fun length : Nat => (length : ℝ)) := by
  let folded := Complexity.Language.List.Fold.program sourceProgram fn same
  let coefficient := perElement + callCost folded
    (Complexity.Language.List.Fold.calleeEntry accTy kind fn) 0 + 2 * fieldCount accTy + 45
  let fixed := LocalCompiler.Function.callSteps (programControl folded)
    (lowerFunc folded (Complexity.Language.List.Fold.entry accTy kind signatures))
    (2 * fieldCount accTy + 23) + 1
  have linear := Asymptotics.isBigO_const_mul_self (coefficient : ℝ)
    (fun length : Nat => (length : ℝ)) Filter.atTop
  have overhead : Asymptotics.IsBigO Filter.atTop (fun _ : Nat => (fixed : ℝ))
      (fun length : Nat => (length : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (fixed : ℝ)).isBigO.natCast_atTop
  simpa only [linearInvocationBound, coefficient, fixed, folded, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, mul_comm, add_assoc] using linear.add overhead

end Ram.LanguageCompiler.List.Fold
