/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Scalar
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Mathlib.Tactic.SplitIfs

/-!
# Source implementations of native integer operations

The same `source_program` declaration generates each native mathematical
observation and its independently interpreted source body. Integer values use
`Representation.int`: a negative pair `(true, n)` means `-(n + 1)`.

There is no `Int` primitive or arbitrary native callback. Negation, comparison
and addition below consist of existing natural arithmetic, comparisons,
branches and product operations. The source correctness theorems require no
time budget or selected RAM width. Realization of every executed natural
intermediate and the costs of the actual lowered instructions remain separate
backend obligations; this module does not assert constant-time bignum arithmetic.
-/

namespace Complexity.Language.Scalar.Int

open Representation (intEquiv)

source_program (pure) Implementation where
  def negate (value : Bool × Nat) : Bool × Nat := do
    if value.1 then
      return (false, value.2 + 1)
    else
      if value.2 == 0 then
        return (false, 0)
      else
        return (true, value.2 - 1)

  def less (left : Bool × Nat) (right : Bool × Nat) : Bool := do
    if left.1 then
      if right.1 then
        return right.2 < left.2
      else
        return true
    else
      if right.1 then
        return false
      else
        return left.2 < right.2

  def add (left : Bool × Nat) (right : Bool × Nat) : Bool × Nat := do
    if left.1 then
      if right.1 then
        return (true, left.2 + right.2 + 1)
      else
        if right.2 ≤ left.2 then
          return (true, left.2 - right.2)
        else
          return (false, right.2 - left.2 - 1)
    else
      if right.1 then
        if left.2 ≤ right.2 then
          return (true, right.2 - left.2)
        else
          return (false, left.2 - right.2 - 1)
      else
        return (false, left.2 + right.2)

/-- The real source negation agrees with native integer negation after decoding. -/
theorem negate_decode (value : Bool × Nat) :
    intEquiv.symm (Implementation.negate value) = -intEquiv.symm value := by
  rcases value with ⟨sign, magnitude⟩
  cases sign <;>
    simp [Implementation.negate, Id.run, Id.instMonad, Representation.intEquiv,
      Int.negSucc_eq] <;>
    (try split_ifs) <;>
    simp_all (config := { failIfUnchanged := false }) [Representation.intEquiv, Int.negSucc_eq] <;>
    omega

/-- The real comparison uses reversed magnitudes precisely in the negative case. -/
theorem less_decode (left right : Bool × Nat) :
    Implementation.less left right = decide (intEquiv.symm left < intEquiv.symm right) := by
  rcases left with ⟨leftSign, leftMagnitude⟩
  rcases right with ⟨rightSign, rightMagnitude⟩
  cases leftSign <;> cases rightSign <;>
    simp [Implementation.less, Id.run, Id.instMonad, Representation.intEquiv,
      Int.negSucc_eq] <;> omega

/-- The sign branches implement exact integer addition, including cancellation. -/
theorem add_decode (left right : Bool × Nat) :
    intEquiv.symm (Implementation.add left right) =
      intEquiv.symm left + intEquiv.symm right := by
  rcases left with ⟨leftSign, leftMagnitude⟩
  rcases right with ⟨rightSign, rightMagnitude⟩
  cases leftSign <;> cases rightSign <;>
    simp [Implementation.add, Id.run, Id.instMonad, Representation.intEquiv,
      Int.negSucc_eq] <;>
    (try split_ifs) <;>
    simp_all (config := { failIfUnchanged := false }) [Representation.intEquiv, Int.negSucc_eq] <;>
    omega

/-- Native integers can be used directly in the mathematical specification. -/
theorem negate_correct (a : Int) :
    Implementation.negate (intEquiv a) = intEquiv (-a) := by
  apply intEquiv.symm.injective
  simpa using negate_decode (intEquiv a)

theorem less_correct (a b : Int) :
    Implementation.less (intEquiv a) (intEquiv b) = decide (a < b) := by
  simpa using less_decode (intEquiv a) (intEquiv b)

theorem add_correct (a b : Int) :
    Implementation.add (intEquiv a) (intEquiv b) = intEquiv (a + b) := by
  apply intEquiv.symm.injective
  simpa using add_decode (intEquiv a) (intEquiv b)

/-- A sufficient range for the result's natural field. This is a mathematical
consequence of the actual source function, not a RAM execution certificate. -/
theorem negate_range (value : Bool × Nat) {capacity : Nat}
    (room : value.2 + 1 < capacity) :
    (Implementation.negate value).2 < capacity := by
  rcases value with ⟨sign, magnitude⟩
  cases sign <;>
    simp [Implementation.negate, Id.run, Id.instMonad] <;>
    (try split_ifs) <;> simp_all (config := { failIfUnchanged := false }) <;> omega

/-- The offset used for two negative arguments is included in the sufficient
result range. Intermediate representability is still checked by the backend. -/
theorem add_range (left right : Bool × Nat) {capacity : Nat}
    (room : left.2 + right.2 + 1 < capacity) :
    (Implementation.add left right).2 < capacity := by
  rcases left with ⟨leftSign, leftMagnitude⟩
  rcases right with ⟨rightSign, rightMagnitude⟩
  cases leftSign <;> cases rightSign <;>
    simp [Implementation.add, Id.run, Id.instMonad] <;>
    (try split_ifs) <;> simp_all (config := { failIfUnchanged := false }) <;> omega

/-- Total source correctness reuses the generated correspondence for the same
negation implementation; its integer interpretation is independent of costs. -/
theorem negate_total (a : Int) :
    Implementation.negate_contract
      (fun value heap => Representation.int.Rel a value heap)
      (fun _ heap result finish => Representation.int.Rel (-a) result finish ∧ finish = heap) := by
  apply (Implementation.negate_total_iff _ _).mpr
  intro value heap represented
  refine ⟨Implementation.negate value, heap,
    congrFun (Implementation.negate_action_eq_pure value) heap, ?_, rfl⟩
  apply (Representation.int_rel_iff_decode _ _ _).mpr
  rw [negate_decode, (Representation.int_rel_iff_decode _ _ _).mp represented]

/-- Comparison returns the native integer ordering for the actually represented inputs. -/
theorem less_total (a b : Int) :
    Implementation.less_contract
      (fun left right heap =>
        Representation.int.Rel a left heap ∧ Representation.int.Rel b right heap)
      (fun _ _ heap result finish => result = decide (a < b) ∧ finish = heap) := by
  apply (Implementation.less_total_iff _ _).mpr
  intro left right heap represented
  refine ⟨Implementation.less left right, heap,
    congrFun (Implementation.less_action_eq_pure left right) heap, ?_, rfl⟩
  rw [less_decode, (Representation.int_rel_iff_decode _ _ _).mp represented.1,
    (Representation.int_rel_iff_decode _ _ _).mp represented.2]

/-- Exact native addition specifies the same executed source program and final heap. -/
theorem add_total (a b : Int) :
    Implementation.add_contract
      (fun left right heap =>
        Representation.int.Rel a left heap ∧ Representation.int.Rel b right heap)
      (fun _ _ heap result finish =>
        Representation.int.Rel (a + b) result finish ∧ finish = heap) := by
  apply (Implementation.add_total_iff _ _).mpr
  intro left right heap represented
  refine ⟨Implementation.add left right, heap,
    congrFun (Implementation.add_action_eq_pure left right) heap, ?_, rfl⟩
  apply (Representation.int_rel_iff_decode _ _ _).mpr
  rw [add_decode, (Representation.int_rel_iff_decode _ _ _).mp represented.1,
    (Representation.int_rel_iff_decode _ _ _).mp represented.2]

end Complexity.Language.Scalar.Int
