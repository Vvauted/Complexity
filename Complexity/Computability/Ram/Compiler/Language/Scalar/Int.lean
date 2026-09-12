/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Scalar.Int
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiling the source integer operations

The imported operations retain their actual boolean/natural-pair source
signatures. Native `Int` is their mathematical view, not a new source primitive.
The sign bit uses one real word field; the natural field of a negative input
stores its absolute value minus one.

The range proofs cover every executed intermediate of those source bodies.
Negation may increment its natural field, and addition of two negative values
materializes the sum of their fields plus one. A positive word width is also
required for booleans. These are bounded-word implementations of mathematical
integer operations, not constant-time arbitrary-precision arithmetic.

Uniform body budgets below are inferred from existing proved compiler cost
rules before any input is introduced. No second interpreter or instruction
price table is added. Source correctness remains separate from these ranges
and instruction bounds.
-/

namespace Ram.LanguageCompiler.Scalar.Int

open Complexity.Language
open Complexity.Language.Scalar.Int

/-- The source negation's increment and both real representation fields fit.
The implementation makes no nested source call. -/
theorem negate_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Implementation.program w 0 Implementation.negateId
      (fun args _ => args.head.2 + 1 < 2 ^ w) := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (value)
  all_goals (try split_ifs) <;> omega

/-- Signed comparison only needs its input fields and boolean result to fit. -/
theorem less_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Implementation.program w 0 Implementation.lessId
      (fun args _ => args.head.2 < 2 ^ w ∧ args.tail.head.2 < 2 ^ w) := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (left right)
  all_goals (try split_ifs) <;> omega

/-- The uniform range includes the actual double-negative intermediate, not
only the possibly much smaller final integer after cancellation. -/
theorem add_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Implementation.program w 0 Implementation.addId
      (fun args _ => args.head.2 + args.tail.head.2 + 1 < 2 ^ w) := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (left right)
  all_goals (try split_ifs) <;> omega

/-- Infer one input-independent certificate for the actual negation body. -/
def negateBodyCost : { bound : Nat //
    ∀ (value : Bool × Nat) (heap : Heap),
      StmtCostBound Implementation.program Implementation.negateBody
        ⟨Env.cons (τ := .prod .bool .nat) value Env.empty, heap⟩ bound } := ⟨_, by
  intro value heap
  ram_source_cost_step⟩

/-- Infer one input-independent certificate for the actual comparison body. -/
def lessBodyCost : { bound : Nat //
    ∀ (left right : Bool × Nat) (heap : Heap),
      StmtCostBound Implementation.program Implementation.lessBody
        ⟨Env.cons (τ := .prod .bool .nat) left
          (Env.cons (τ := .prod .bool .nat) right Env.empty), heap⟩ bound } := ⟨_, by
  intro left right heap
  ram_source_cost_step⟩

/-- Infer one input-independent certificate for all actual addition branches. -/
def addBodyCost : { bound : Nat //
    ∀ (left right : Bool × Nat) (heap : Heap),
      StmtCostBound Implementation.program Implementation.addBody
        ⟨Env.cons (τ := .prod .bool .nat) left
          (Env.cons (τ := .prod .bool .nat) right Env.empty), heap⟩ bound } := ⟨_, by
  intro left right heap
  ram_source_cost_step⟩

/-- The existing function rule adds its return-flag initialization once. -/
theorem negate_costBound :
    FunctionCostBound Implementation.program Implementation.negateId (fun _ _ => True)
      (fun _ _ => negateBodyCost.val + 2) := by
  ram_source_cost_intro (value)
  intro heap _
  exact negateBodyCost.property value heap

theorem less_costBound :
    FunctionCostBound Implementation.program Implementation.lessId (fun _ _ => True)
      (fun _ _ => lessBodyCost.val + 2) := by
  ram_source_cost_intro (left right)
  intro heap _
  exact lessBodyCost.property left right heap

theorem add_costBound :
    FunctionCostBound Implementation.program Implementation.addId (fun _ _ => True)
      (fun _ _ => addBodyCost.val + 2) := by
  ram_source_cost_intro (left right)
  intro heap _
  exact addBodyCost.property left right heap

/-- These concrete source bodies neither mutate nor allocate source heap data. -/
theorem program_noHeapWrites : ∀ fn, NoHeapWrites (Implementation.program.body fn) := by
  intro fn
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) fn
  · change NoHeapWrites Implementation.negateBody
    simp [Implementation.negateBody, NoHeapWrites]
  · change NoHeapWrites Implementation.lessBody
    simp [Implementation.lessBody, NoHeapWrites]
  · change NoHeapWrites Implementation.addBody
    simp [Implementation.addBody, NoHeapWrites]

/-- The actual outer calling convention and final halt augment the inferred
body bound; this definition is not a separate operation-price table. -/
def negateSteps : Nat :=
  LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.negateId) (negateBodyCost.val + 2) + 1

def lessSteps : Nat :=
  LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.lessId) (lessBodyCost.val + 2) + 1

def addSteps : Nat :=
  LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.addId) (addBodyCost.val + 2) + 1

/-- A real halted negation invocation returns the native integer result with
the independently inferred instruction bound. Input loading is outside this
preloaded-call boundary; code and one frame must fit the selected RAM width. -/
theorem negate_execute_le {w heapLimit : Nat} (a : Int)
    (initialHeap : Heap) (entry : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity Implementation.program Implementation.negateId w 0 heapLimit)
    (memory : HeapRep placement heapLimit initialHeap entry)
    (room : (Representation.intEquiv a).2 + 1 < 2 ^ w) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.negateId
        heapLimit placement
        (Env.cons (τ := .prod .bool .nat) (Representation.intEquiv a) Env.empty)
        initialHeap entry,
      Representation.int.Rel (-a) outcome.value outcome.heap ∧
      outcome.heap = initialHeap ∧
      Source.State.Observes heapLimit 0 entry outcome.result.state ∧
      outcome.result.steps ≤ negateSteps := by
  let args : Env [.prod .bool .nat] := Env.cons (Representation.intEquiv a) Env.empty
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive)
  have magnitudeFits : (Representation.intEquiv a).2 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ 1) room
  have arguments : EnvFits w args := by
    refine EnvFits.cons (τ := .prod .bool .nat) (EnvFits.empty w)
      (Representation.intEquiv a) ?_
    change (if (Representation.intEquiv a).1 then 1 else 0) < 2 ^ w ∧
      (Representation.intEquiv a).2 < 2 ^ w
    refine ⟨?_, magnitudeFits⟩
    split <;> omega
  let launch : FunctionLaunch Implementation.program Implementation.negateId
      0 heapLimit placement args initialHeap entry := ⟨capacity, arguments, memory⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (negate_realizable capacity.positive).execute_le
      (Complexity.Language.Scalar.Int.negate_total a) negate_costBound launch room rfl trivial
  exact ⟨outcome, property.1, property.2,
    outcome.observes_of_noHeapWrites program_noHeapWrites, bounded⟩

/-- Native signed comparison is observed from the same actual halted runner.
Its two natural fields, boolean encoding, code and one frame must fit. -/
theorem less_execute_le {w heapLimit : Nat} (a b : Int)
    (initialHeap : Heap) (entry : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity Implementation.program Implementation.lessId w 0 heapLimit)
    (memory : HeapRep placement heapLimit initialHeap entry)
    (leftFits : (Representation.intEquiv a).2 < 2 ^ w)
    (rightFits : (Representation.intEquiv b).2 < 2 ^ w) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.lessId
        heapLimit placement
        (Env.cons (τ := .prod .bool .nat) (Representation.intEquiv a)
          (Env.cons (τ := .prod .bool .nat) (Representation.intEquiv b) Env.empty))
        initialHeap entry,
      outcome.value = decide (a < b) ∧
      outcome.heap = initialHeap ∧
      Source.State.Observes heapLimit 0 entry outcome.result.state ∧
      outcome.result.steps ≤ lessSteps := by
  let args : Env [.prod .bool .nat, .prod .bool .nat] :=
    Env.cons (Representation.intEquiv a) (Env.cons (Representation.intEquiv b) Env.empty)
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive)
  have arguments : EnvFits w args := by
    refine EnvFits.cons (τ := .prod .bool .nat)
      (EnvFits.cons (τ := .prod .bool .nat) (EnvFits.empty w)
        (Representation.intEquiv b) ?_) (Representation.intEquiv a) ?_
    all_goals simp only [ValueFits]
    all_goals (try split_ifs) <;> constructor <;> omega
  let launch : FunctionLaunch Implementation.program Implementation.lessId
      0 heapLimit placement args initialHeap entry := ⟨capacity, arguments, memory⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (less_realizable capacity.positive).execute_le
      (Complexity.Language.Scalar.Int.less_total a b) less_costBound launch
      ⟨leftFits, rightFits⟩ ⟨rfl, rfl⟩ trivial
  exact ⟨outcome, property.1, property.2,
    outcome.observes_of_noHeapWrites program_noHeapWrites, bounded⟩

/-- Native integer addition, source correctness and the instruction bound
describe one actual halted invocation. The intermediate sum-plus-one range is
explicit even when the final mathematical sum cancels to a smaller number. -/
theorem add_execute_le {w heapLimit : Nat} (a b : Int)
    (initialHeap : Heap) (entry : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity Implementation.program Implementation.addId w 0 heapLimit)
    (memory : HeapRep placement heapLimit initialHeap entry)
    (room : (Representation.intEquiv a).2 + (Representation.intEquiv b).2 + 1 < 2 ^ w) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.addId
        heapLimit placement
        (Env.cons (τ := .prod .bool .nat) (Representation.intEquiv a)
          (Env.cons (τ := .prod .bool .nat) (Representation.intEquiv b) Env.empty))
        initialHeap entry,
      Representation.int.Rel (a + b) outcome.value outcome.heap ∧
      outcome.heap = initialHeap ∧
      Source.State.Observes heapLimit 0 entry outcome.result.state ∧
      outcome.result.steps ≤ addSteps := by
  let args : Env [.prod .bool .nat, .prod .bool .nat] :=
    Env.cons (Representation.intEquiv a) (Env.cons (Representation.intEquiv b) Env.empty)
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive)
  have sumFits : (Representation.intEquiv a).2 + (Representation.intEquiv b).2 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ 1) room
  have leftFits : (Representation.intEquiv a).2 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) sumFits
  have rightFits : (Representation.intEquiv b).2 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) sumFits
  have arguments : EnvFits w args := by
    refine EnvFits.cons (τ := .prod .bool .nat)
      (EnvFits.cons (τ := .prod .bool .nat) (EnvFits.empty w)
        (Representation.intEquiv b) ?_) (Representation.intEquiv a) ?_
    · change (if (Representation.intEquiv b).1 then 1 else 0) < 2 ^ w ∧
        (Representation.intEquiv b).2 < 2 ^ w
      refine ⟨?_, rightFits⟩
      split <;> omega
    · change (if (Representation.intEquiv a).1 then 1 else 0) < 2 ^ w ∧
        (Representation.intEquiv a).2 < 2 ^ w
      refine ⟨?_, leftFits⟩
      split <;> omega
  let launch : FunctionLaunch Implementation.program Implementation.addId
      0 heapLimit placement args initialHeap entry := ⟨capacity, arguments, memory⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (add_realizable capacity.positive).execute_le
      (Complexity.Language.Scalar.Int.add_total a b) add_costBound launch room ⟨rfl, rfl⟩ trivial
  exact ⟨outcome, property.1, property.2,
    outcome.observes_of_noHeapWrites program_noHeapWrites, bounded⟩

end Ram.LanguageCompiler.Scalar.Int
