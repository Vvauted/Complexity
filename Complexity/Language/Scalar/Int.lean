/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Scalar
import Complexity.Language.Syntax.Core
import Complexity.Language.Eval.Verification
import Complexity.Language.Buffer.Copy
import Complexity.Language.RepresentedFunction
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

/-!
# Source implementations of native integer operations

The same `source_program` declaration generates each native mathematical
observation and its independently interpreted source body. Integer values use
`Representation.int`: a negative pair `(true, n)` means `-(n + 1)`.

There is no `Int` primitive or arbitrary native callback. Negation, comparison,
addition and multiplication consist of existing natural arithmetic, comparisons,
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

  def mul (left : Bool × Nat) (right : Bool × Nat) : Bool × Nat := do
    if left.1 then
      if right.1 then
        return (false, (left.2 + 1) * (right.2 + 1))
      else
        if right.2 == 0 then
          return (false, 0)
        else
          return (true, (left.2 + 1) * right.2 - 1)
    else
      if right.1 then
        if left.2 == 0 then
          return (false, 0)
        else
          return (true, left.2 * (right.2 + 1) - 1)
      else
        return (false, left.2 * right.2)

/-- The same natural multiplication computes the product of the represented
integers, with an explicit zero branch in each mixed-sign case. -/
theorem mul_decode (left right : Bool × Nat) :
    intEquiv.symm (Implementation.mul left right) =
      intEquiv.symm left * intEquiv.symm right := by
  rcases left with ⟨leftSign, leftMagnitude⟩
  rcases right with ⟨rightSign, rightMagnitude⟩
  cases leftSign <;> cases rightSign <;>
    simp [Implementation.mul, Id.run, Id.instMonad, Representation.intEquiv,
      Int.negSucc_eq] <;>
    (try split_ifs) <;>
    simp_all (config := { failIfUnchanged := false })
  · have positive : 1 ≤ leftMagnitude * (rightMagnitude + 1) :=
      Nat.mul_pos (Nat.pos_of_ne_zero ‹_›) (by omega)
    rw [Int.ofNat_sub positive]
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    ring
  · have positive : 1 ≤ (leftMagnitude + 1) * rightMagnitude :=
      Nat.mul_pos (by omega) (Nat.pos_of_ne_zero ‹_›)
    rw [Int.ofNat_sub positive]
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    ring
  · ring

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

/-- Negation observes the same source action on any represented integer. -/
theorem negate_eval (a : Int) (value : Bool × Nat) (heap : Heap)
    (observed : Representation.int.Rel a value heap) :
    Implementation.negate_action value heap =
      Part.some (.ok (intEquiv.toEmbedding (-a)), heap) := by
  change intEquiv a = value at observed
  subst value
  rw [Implementation.negate_action_eq_pure, negate_correct]
  rfl

/-- Addition observes the original source body, including both sign branches. -/
theorem add_eval (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    Implementation.add_action left right heap =
      Part.some (.ok (intEquiv.toEmbedding (a + b)), heap) := by
  change intEquiv a = left at first
  change intEquiv b = right at second
  subst left right
  rw [Implementation.add_action_eq_pure, add_correct]
  rfl

/-- Signed comparison is an actual source call with a Boolean observation. -/
theorem less_eval (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    Implementation.less_action left right heap = Part.some (.ok (decide (a < b)), heap) := by
  change intEquiv a = left at first
  change intEquiv b = right at second
  subst left right
  rw [Implementation.less_action_eq_pure, less_correct]
  rfl

/-- Negation does not change any existing heap observation. -/
theorem negate_eval_exists_preserving (a : Int) (value : Bool × Nat) (heap : Heap)
    (observed : Representation.int.Rel a value heap) :
    ∃ returned finish, Implementation.negate_action value heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (-a) returned finish ∧ heap.ShapeExtends finish ∧
      Buffer.PreservesContents heap finish :=
  ⟨_, heap, negate_eval a value heap observed, rfl, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- Addition preserves old arrays as well as heap shape. -/
theorem add_eval_exists_preserving (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.add_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (a + b) returned finish ∧ heap.ShapeExtends finish ∧
      Buffer.PreservesContents heap finish :=
  ⟨_, heap, add_eval a b left right heap first second, rfl, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- Comparison preserves old arrays as well as heap shape. -/
theorem less_eval_exists_preserving (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.less_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel (decide (a < b)) returned finish ∧ heap.ShapeExtends finish ∧
      Buffer.PreservesContents heap finish :=
  ⟨_, heap, less_eval a b left right heap first second, rfl, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- The ordinary negation call retains its actual result and final heap. -/
theorem negate_eval_exists (a : Int) (value : Bool × Nat) (heap : Heap)
    (observed : Representation.int.Rel a value heap) :
    ∃ returned finish, Implementation.negate_action value heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (-a) returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, executed, related, shape, _⟩ :=
    negate_eval_exists_preserving a value heap observed
  exact ⟨returned, finish, executed, related, shape⟩

/-- The ordinary addition call retains its actual result and final heap. -/
theorem add_eval_exists (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.add_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (a + b) returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, executed, related, shape, _⟩ :=
    add_eval_exists_preserving a b left right heap first second
  exact ⟨returned, finish, executed, related, shape⟩

/-- The ordinary comparison call retains its actual result and final heap. -/
theorem less_eval_exists (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.less_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.bool.Rel (decide (a < b)) returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, executed, related, shape, _⟩ :=
    less_eval_exists_preserving a b left right heap first second
  exact ⟨returned, finish, executed, related, shape⟩

/-- Native negation refines the same encoded source entry. -/
theorem negate_refines : RepresentedFunction.Refines Implementation.program Implementation.negateId
    (FunctionRepresentation.ofResult (ArgumentRepresentation.single Representation.int)
      (fun _ => Representation.int)) (fun _ => True) (fun a : Int => -a) := by
  intro a _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  refine ⟨intEquiv (-a), heap, ?_, rfl⟩
  rw [Implementation.negate_observe]
  exact negate_eval a args.head heap observed

/-- Native addition refines the same encoded source entry. -/
theorem add_refines : RepresentedFunction.Refines Implementation.program Implementation.addId
    (FunctionRepresentation.ofResult
      (ArgumentRepresentation.cons Representation.int
        (ArgumentRepresentation.single Representation.int))
      (fun _ => Representation.int)) (fun _ => True) (fun a : Int × Int => a.1 + a.2) := by
  intro a _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  refine ⟨intEquiv (a.1 + a.2), heap, ?_, rfl⟩
  rw [Implementation.add_observe]
  exact add_eval a.1 a.2 args.head args.tail.head heap observed.1 observed.2

/-- Native comparison refines the same encoded source entry. -/
theorem less_refines : RepresentedFunction.Refines Implementation.program Implementation.lessId
    (FunctionRepresentation.ofResult
      (ArgumentRepresentation.cons Representation.int
        (ArgumentRepresentation.single Representation.int))
      (fun _ => Representation.bool)) (fun _ => True) (fun a : Int × Int => decide (a.1 < a.2)) := by
  intro a _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  refine ⟨decide (a.1 < a.2), heap, ?_, rfl⟩
  rw [Implementation.less_observe]
  exact less_eval a.1 a.2 args.head args.tail.head heap observed.1 observed.2

/-- Multiplication agrees with native integer multiplication. -/
theorem mul_correct (a b : Int) :
    Implementation.mul (intEquiv a) (intEquiv b) = intEquiv (a * b) := by
  apply intEquiv.symm.injective
  simpa using mul_decode (intEquiv a) (intEquiv b)

/-- Multiplication has the stated integer result and leaves its actual heap unchanged. -/
theorem mul_total (a b : Int) :
    Implementation.mul_contract
      (fun left right heap =>
        Representation.int.Rel a left heap ∧ Representation.int.Rel b right heap)
      (fun _ _ heap result finish =>
        Representation.int.Rel (a * b) result finish ∧ finish = heap) := by
  apply (Implementation.mul_total_iff _ _).mpr
  intro left right heap represented
  refine ⟨Implementation.mul left right, heap,
    congrFun (Implementation.mul_action_eq_pure left right) heap, ?_, rfl⟩
  apply (Representation.int_rel_iff_decode _ _ _).mpr
  rw [mul_decode, (Representation.int_rel_iff_decode _ _ _).mp represented.1,
    (Representation.int_rel_iff_decode _ _ _).mp represented.2]

/-- Multiplication observes the original source action on represented integers. -/
theorem mul_eval (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    Implementation.mul_action left right heap =
      Part.some (.ok (intEquiv.toEmbedding (a * b)), heap) := by
  change intEquiv a = left at first
  change intEquiv b = right at second
  subst left right
  rw [Implementation.mul_action_eq_pure, mul_correct]
  rfl

/-- Multiplication preserves all existing array contents and heap shape. -/
theorem mul_eval_exists_preserving (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.mul_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (a * b) returned finish ∧ heap.ShapeExtends finish ∧
      Buffer.PreservesContents heap finish :=
  ⟨_, heap, mul_eval a b left right heap first second, rfl, Heap.ShapeExtends.refl heap,
    fun {_} _ _ contents => contents⟩

/-- Multiplication retains the actual result and final heap. -/
theorem mul_eval_exists (a b : Int) (left right : Bool × Nat) (heap : Heap)
    (first : Representation.int.Rel a left heap)
    (second : Representation.int.Rel b right heap) :
    ∃ returned finish, Implementation.mul_action left right heap = Part.some (.ok returned, finish) ∧
      Representation.int.Rel (a * b) returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, executed, related, shape, _⟩ :=
    mul_eval_exists_preserving a b left right heap first second
  exact ⟨returned, finish, executed, related, shape⟩

/-- Multiplication refines the same encoded source entry. -/
theorem mul_refines : RepresentedFunction.Refines Implementation.program Implementation.mulId
    (FunctionRepresentation.ofResult
      (ArgumentRepresentation.cons Representation.int
        (ArgumentRepresentation.single Representation.int))
      (fun _ => Representation.int)) (fun _ => True) (fun a : Int × Int => a.1 * a.2) := by
  intro a _
  apply FunctionTotal.iff_eval.mpr
  intro args heap observed
  refine ⟨intEquiv (a.1 * a.2), heap, ?_, rfl⟩
  rw [Implementation.mul_observe]
  exact mul_eval a.1 a.2 args.head args.tail.head heap observed.1 observed.2

end Complexity.Language.Scalar.Int
