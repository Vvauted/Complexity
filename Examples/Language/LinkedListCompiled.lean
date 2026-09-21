/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.LinkedList
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Range.Tactic
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Scalar
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Native
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Linking.Tactic

/-!
# Resource proofs for named linked-list programs

The callback is the same ordinary source declaration used by the mathematical
list program. Its finite-word and instruction proofs are reused by the shared
fold interfaces; no second callback implementation or register proof is needed.
The range condition remains separate from mathematical correctness.
The final theorem compiles the actual `Native.Source.sumFrom` caller, including
its imported fold call and its own outer invocation, return and halt.

The allocating finite-range consumer reuses its generated entry and single-round
correspondence with inferred component budgets. Structural composition infers
the enclosing function's bound; arena readiness and capacity remain separate.
-/

namespace Complexity.Language.Examples.LinkedList

open Ram.LanguageCompiler

/-- The actual intermediate addition fits whenever its mathematical sum fits.
The generated ordinary-argument interface hides the argument environment. -/
theorem add_realizable {w : Nat} :
    FunctionRealizable Reducer.program w 0 Reducer.addId
      (Reducer.add_onArgs fun accumulator head _ => accumulator + head < 2 ^ w) := by
  ram_source_realize (accumulator head)
  all_goals omega

/-- The existing structural rule counts addition, return and body initialization. -/
theorem add_costBound :
    FunctionCostBound Reducer.program Reducer.addId (fun _ _ => True) (fun _ _ => 10) := by
  ram_source_cost (accumulator head)

/-- The ordinary callback range proof supplies the linked fold's zero-growth
resource contract, with actual inputs related to mathematical accumulator values. -/
theorem add_fold_resources_at_depth (w heapLimit depth : Nat) :
    Ram.LanguageCompiler.List.Fold.CalleeResources (kind := .nat) Reducer.program Reducer.addId rfl
      Representation.nat (fun accumulator head => accumulator + head < 2 ^ w)
      w heapLimit depth (fun _ _ => 0) := by
  apply Ram.LanguageCompiler.List.Fold.CalleeResources.of_functionRealizable
    (add_realizable.mono_depth (Nat.zero_le depth))
  intro accumulator actual head heap allowed related
  change accumulator = actual at related
  subst actual
  exact allowed

/-- The standalone fold uses the callback's zero-depth specialization. -/
theorem add_fold_resources (w heapLimit : Nat) :
    Ram.LanguageCompiler.List.Fold.CalleeResources (kind := .nat) Reducer.program Reducer.addId rfl
      Representation.nat (fun accumulator head => accumulator + head < 2 ^ w)
      w heapLimit 0 (fun _ _ => 0) :=
  add_fold_resources_at_depth w heapLimit 0

/-- The same original callback bound transfers without repricing the callback
or proving its source behavior again. Outer calls are charged by the fold. -/
theorem add_fold_costBound_at_depth (w heapLimit depth : Nat) :
    Ram.LanguageCompiler.List.Fold.CalleeCostBound (kind := .nat) Reducer.program Reducer.addId rfl
      Representation.nat (fun accumulator head => accumulator + head < 2 ^ w)
      w heapLimit depth (fun _ _ => 10) := by
  apply Ram.LanguageCompiler.List.Fold.CalleeCostBound.of_functionCostBound
    (add_realizable.mono_depth (Nat.zero_le depth)) add_costBound
  · intro accumulator actual head heap allowed related
    change accumulator = actual at related
    subst actual
    exact allowed
  · intros
    trivial
  · intros
    exact Nat.le_refl _

/-- The standalone fold's callback bound is unchanged by its depth specialization. -/
theorem add_fold_costBound (w heapLimit : Nat) :
    Ram.LanguageCompiler.List.Fold.CalleeCostBound (kind := .nat) Reducer.program Reducer.addId rfl
      Representation.nat (fun accumulator head => accumulator + head < 2 ^ w)
      w heapLimit 0 (fun _ _ => 10) :=
  add_fold_costBound_at_depth w heapLimit 0

/-- The same source addition contract is reused by folds with a finite-word domain. -/
theorem add_fold_contract (w : Nat) :
    List.Fold.Contract (kind := .nat) (accTy := .nat)
      Reducer.program Reducer.addId rfl Representation.nat
      Nat.add (fun accumulator head => accumulator + head < 2 ^ w) :=
  List.Fold.Contract.of_pure_eval (source := Reducer.program) (fn := Reducer.addId)
    (kind := .nat) (accTy := .nat) (same := rfl) (step := Nat.add)
    (domain := fun accumulator head => accumulator + head < 2 ^ w)
    (Function.Embedding.refl Nat)
    (fun accumulator head _ => Native.Operations.fold0.callback_pure accumulator head trivial)

/-- A bound on the final natural sum bounds every intermediate accumulator.
Only ordinary list algebra is used; this is not another traversal proof. -/
theorem sum_admissible {w : Nat} (initial : Nat) (values : List Nat)
    (fits : initial + values.sum < 2 ^ w) :
    List.Fold.Admissible (kind := .nat) Nat.add
      (fun accumulator head => accumulator + head < 2 ^ w) initial values := by
  intro processed head suffix partition
  have processedSum : processed.foldl Nat.add initial = initial + processed.sum :=
    sumFrom_eq processed initial
  change processed.foldl Nat.add initial + head < 2 ^ w
  rw [processedSum]
  have parts : values.sum = processed.sum + (head + suffix.sum) := by
    simp only [partition, List.sum_append, List.sum_cons]
  omega

/-- A final natural-sum bound also bounds the initial accumulator and each head. -/
theorem sum_ranges {w : Nat} (initial : Nat) (values : List Nat)
    (fits : initial + values.sum < 2 ^ w) :
    initial < 2 ^ w ∧ ∀ head ∈ values, head < 2 ^ w := by
  refine ⟨Nat.lt_of_le_of_lt (Nat.le_add_right initial values.sum) fits, ?_⟩
  intro head member
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
  simp only [List.sum_append, List.sum_cons] at fits
  exact Nat.lt_of_le_of_lt
    ((Nat.le_add_right head after.sum).trans
      ((Nat.le_add_left _ before.sum).trans (Nat.le_add_left _ initial))) fits

private theorem fold_total (values : List Nat) :
    FunctionTotal Native.Operations.fold0.program Native.Operations.fold0.foldId
      (List.Fold.onArgs fun _ root heap =>
        NodeRef.Contents heap root values)
      (List.Fold.onArgs fun initial _ heap value finish =>
        value = initial + values.sum ∧ finish = heap) := by
  apply List.Fold.total_of_eval_eq
  intro initial root heap observed
  have summed : values.foldl Reducer.add initial = initial + values.sum :=
    sumFrom_eq values initial
  simpa only [summed] using
    Native.Operations.fold0.fold_eq initial values root heap observed

private theorem fold_realizable {w : Nat} (positive : 0 < w) (values : List Nat) :
    FunctionRealizable Native.Operations.fold0.program w 1 Native.Operations.fold0.foldId
      (List.Fold.onArgs fun initial root heap =>
        NodeRef.Contents heap root values ∧ initial + values.sum < 2 ^ w) := by
  refine Ram.LanguageCompiler.List.Fold.Native.realizable_of_resources
    (kind := .nat) (accTy := .nat)
    (step := Nat.add) (add_fold_contract w) (add_fold_resources w 0)
    ?_ positive ?_
  · intro fn
    cases Fin.fin_one_eq_zero fn
    trivial
  · rintro initial root heap ⟨observed, fits⟩
    have ranges := sum_ranges initial values fits
    exact ⟨initial, values, rfl, observed, sum_admissible initial values fits, ranges.1, ranges.2⟩

private theorem fold_costBound {w : Nat} (positive : 0 < w) (values : List Nat) :
    FunctionCostBound Native.Operations.fold0.program Native.Operations.fold0.foldId
      (List.Fold.onArgs fun initial root heap =>
        NodeRef.Contents heap root values ∧ initial + values.sum < 2 ^ w)
      (List.Fold.onArgs fun initial _ _ =>
        Ram.LanguageCompiler.List.Fold.functionBound (kind := .nat) (accTy := .nat)
          Reducer.program Reducer.addId rfl Nat.add (fun _ _ => 10) initial values) := by
  refine Ram.LanguageCompiler.List.Fold.Native.costBound (kind := .nat) (accTy := .nat)
    (step := Nat.add) (add_fold_contract w) (add_fold_resources w 0)
    (add_fold_costBound w 0) positive ?_
  rintro initial root heap ⟨observed, fits⟩
  have ranges := sum_ranges initial values fits
  exact ⟨initial, values, rfl, observed, sum_admissible initial values fits,
    ranges.1, ranges.2, Nat.le_refl _⟩

/-- The generated native correspondence supplies the actual caller's ordinary
sum and exact unchanged heap, independently of ranges and instruction budgets. -/
theorem sumFrom_total (values : List Nat) :
    FunctionTotal Native.Source.program Native.Source.sumFromId
      (fun args heap => NodeRef.Contents heap args.head values)
      (fun args heap value finish => value = args.tail.head + values.sum ∧ finish = heap) := by
  apply (Native.Source.sumFrom_total_iff
    (fun root _ heap => NodeRef.Contents heap root values)
    (fun _ initial heap value finish => value = initial + values.sum ∧ finish = heap)).mpr
  intro root initial heap observed
  refine ⟨initial + values.sum, heap, ?_, rfl, rfl⟩
  simpa only [sumFrom_eq] using Native.sumFrom_action_eq_native values initial root heap observed

/-- The real caller adds one call level above fold and its callback. A single
ordinary final-sum bound supplies the ranges along the entire computation. -/
theorem sumFrom_realizable {w : Nat} (positive : 0 < w) (values : List Nat) :
    FunctionRealizable Native.Source.program w 2 Native.Source.sumFromId
      (Native.Source.sumFrom_onArgs fun root initial heap =>
        NodeRef.Contents heap root values ∧ initial + values.sum < 2 ^ w) := by
  ram_source_realize (root initial)
  rename_i heap input
  rcases input with ⟨observed, fits⟩
  ram_source_call using (fold_realizable positive values), (fold_total values)
    via Native.Source.imports.Native.Operations.fold0.embedding
  all_goals
    first
    | assumption
    | exact ⟨observed, fits⟩
    | exact ValueFits.option_node positive root
    | exact ⟨by omega, ValueFits.option_node positive root⟩
    | omega

/-- The caller pays for its actual imported fold invocation, return and body
initialization. The callback and linked traversal retain their original costs. -/
def sumFromBodyBound (initial : Nat) (values : List Nat) : Nat :=
  callCost Native.Source.program
    (Native.Source.imports.Native.Operations.fold0.map.toFun Native.Operations.fold0.foldId)
    (Ram.LanguageCompiler.List.Fold.functionBound (kind := .nat) (accTy := .nat)
      Reducer.program Reducer.addId rfl Nat.add (fun _ _ => 10) initial values) + 6

/-- Structural call composition counts the actual native wrapper, rather than
publishing only the independently runnable library fold's bound. -/
theorem sumFrom_costBound {w : Nat} (positive : 0 < w) (values : List Nat) :
    FunctionCostBound Native.Source.program Native.Source.sumFromId
      (Native.Source.sumFrom_onArgs fun root initial heap =>
        NodeRef.Contents heap root values ∧ initial + values.sum < 2 ^ w)
      (fun args _ => sumFromBodyBound args.tail.head values) := by
  ram_source_cost (root initial) using (fold_costBound positive values)
    via Native.Source.imports.Native.Operations.fold0.embedding
  all_goals
    first
    | assumption
    | (unfold sumFromBodyBound; exact Nat.le_refl _)

/-- Full invocation cost for the actual wrapper, with its own outer call and
final halt added exactly once. -/
def sumFromInvocationBound (initial : Nat) (values : List Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Native.Source.program)
    (lowerFunc Native.Source.program Native.Source.sumFromId)
    (sumFromBodyBound initial values) + 1

/-- The generated native wrapper halts on the RAM backend with the ordinary
sum and the identical represented source heap. Its bound covers both internal
call levels and its outer invocation; the launch supplies real code and stack
capacity for the combined native source program. -/
theorem sumFrom_execute {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (root : Option (NodeRef .nat)) (initial : Nat) (values : List Nat) {heap : Heap}
    (observed : NodeRef.Contents heap root values) (fits : initial + values.sum < 2 ^ w)
    {entry : Ram.Source.State w}
    (launch : FunctionLaunch Native.program Native.sumFromId 2 heapLimit placement
      (Native.Source.sumFrom_args root initial) heap entry) :
    ∃ outcome : FunctionExecution Native.program Native.sumFromId heapLimit placement
        (Native.Source.sumFrom_args root initial) heap entry,
      outcome.value = initial + values.sum ∧ outcome.heap = heap ∧
      outcome.bodySteps ≤ sumFromBodyBound initial values ∧
      outcome.result.steps ≤ sumFromInvocationBound initial values := by
  obtain ⟨outcome, result, bounded⟩ :=
    (sumFrom_realizable launch.positive values).execute_le (sumFrom_total values)
      (sumFrom_costBound launch.positive values) launch ⟨observed, fits⟩ observed ⟨observed, fits⟩
  exact ⟨outcome, result.1, result.2, outcome.bodySteps_le bounded, bounded⟩

namespace NativeRange

/-- A uniform bound for both the running and stopped paths of the actual range
guard, inferred from its source instructions. -/
def prependRangeGuardCost : { bound : Nat // ∀ w heapLimit depth initial,
    StmtArenaCostBound RangeNative.Source.program w heapLimit (depth + 1)
      RangeNative.Source.prependRange_loop1.Guard initial bound } := by
  ram_source_arena_cost

/-- The whole range body includes its linked cons call and cursor update.
The shared cons certificate supplies the allocating operation's cost. -/
def prependRangeBodyCost : { bound : Nat // ∀ w heapLimit depth initial,
    StmtArenaCostBound RangeNative.Source.program w heapLimit (depth + 1)
      RangeNative.Source.prependRange_loop1.Body initial bound } := by
  ram_source_arena_cost [(Ram.LanguageCompiler.List.Cons.arenaCostBound .nat _ _ _)
    via RangeNative.Source.imports.RangeNative.Operations.consNat.embedding]

/-- The existing source round contracts compose inferred uniform bounds into a
linear bound for this same allocating loop. The running condition uses the
named completion view, not a private lexical position. No second traversal,
register proof or hand-written potential inequality is needed. Readiness and
capacity remain separate, as does the enclosing function's wrapper cost. -/
theorem prependRange_loop_costBound
    (w heapLimit depth count head : Nat) (tail : List Nat)
    (rawTail : Option (NodeRef .nat)) (initialHeap : Heap)
    (index : Nat) (state : List Nat × List Nat × Nat × Nat)
    (locals : RangeNative.Source.prependRange_loop1.Locals) (heap : Heap)
    (related : RangeNative.Source.prependRange_loop1.stateRel
      count head rawTail initialHeap index state locals heap)
    (running : RangeNative.Source.prependRange_loop1.pending locals = none)
    (inputObserved : (Representation.list .nat).Rel tail rawTail initialHeap) :
    StmtArenaCostBound RangeNative.Source.program w heapLimit (depth + 1)
      RangeNative.Source.prependRange_loop1.Code
      ⟨RangeNative.Source.prependRange_loop1.View.symm locals, heap⟩
      (StmtCostBound.whileLinearBound prependRangeGuardCost.val prependRangeBodyCost.val
        (count - index)) := by
  ram_source_range_arena_cost using related, running facts [inputObserved]
    costs (prependRangeGuardCost.property w heapLimit depth),
      (prependRangeBodyCost.property w heapLimit depth)

/-- Infer the unchanged source body's bound around its range certificate.
The numeric witness depends only on the count; the generated entry proof uses
the existing input observation without a hand-built local-state relation. -/
def prependRangeCost (count : Nat) : { bound : Nat //
    ∀ w heapLimit depth head (tail : List Nat) (rawTail : Option (NodeRef .nat)) (heap : Heap),
      (Representation.list .nat).Rel tail rawTail heap →
      StmtArenaCostBound RangeNative.Source.program w heapLimit (depth + 1)
        (RangeNative.Source.program.body RangeNative.Source.prependRangeId)
        ⟨RangeNative.Source.prependRange_args count head rawTail, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth head tail rawTail heap observed
  ram_source_arena_cost
  ram_source_range_arena_cost entry facts [observed] costs
    (prependRangeGuardCost.property w heapLimit depth),
    (prependRangeBodyCost.property w heapLimit depth)⟩

/-- The callable function adds its actual two-instruction initialization once. -/
def prependRangeBodyBound (count : Nat) : Nat := (prependRangeCost count).val + 2

/-- A count-only bound on the same callable implementation, under its original
heap-indexed List observation. This does not assert capacity or realizability. -/
theorem prependRange_costBound (w heapLimit depth count : Nat) :
    FunctionArenaCostBound RangeNative.Source.program
      (RangeNative.Source.program.body RangeNative.Source.prependRangeId)
      (fun input : Nat × List Nat × Option (NodeRef .nat) =>
        RangeNative.Source.prependRange_args count input.1 input.2.2)
      (fun input heap => (Representation.list .nat).Rel input.2.1 input.2.2 heap)
      w heapLimit (depth + 1) (fun _ => prependRangeBodyBound count) := by
  apply FunctionArenaCostBound.of_stmt
  rintro ⟨head, tail, rawTail⟩ heap observed
  exact (prependRangeCost count).property w heapLimit depth head tail rawTail heap observed

/-- All count-dependent work is the existing round envelope; the enclosing
source control and function initialization contribute only a fixed term. -/
theorem prependRangeBodyBound_eq (count : Nat) :
    prependRangeBodyBound count =
      (prependRangeGuardCost.val + prependRangeBodyCost.val + 10) * count +
        prependRangeBodyBound 0 := by
  simp only [prependRangeBodyBound, prependRangeCost, StmtCostBound.whileLinearBound,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.mul_zero]
  omega

end NativeRange

end Complexity.Language.Examples.LinkedList
