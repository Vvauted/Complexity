/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.TraversalComposition
import Examples.Language.TraversalCompiled

/-!
# Compiling two effectful traversal calls

The same source declaration calls the existing traversal twice. Its first
callee's proved frame preserves the second input in the actual intermediate
heap. Realization and cost reuse the existing callee contracts; neither proof
reopens the array loop or supplies a register-level adapter.

The final runner theorem retains both mapped arrays, observations outside both
borrowed views, and their common represented final heap. The views may be
disjoint slices of one object. Word ranges, preloaded memory and space for the
three active call frames remain explicit, independently of the instruction
bound.
-/

namespace Complexity.Language.Examples.Traversal

open Ram.LanguageCompiler

/-- Two nested call levels account for the pair calling a traversal which calls
its increment helper. The first traversal's frame supplies the second input;
all actual increment ranges are inherited from the existing callee proofs. -/
theorem boundedMapPair_realizable {w : Nat} (hw : 0 < w)
    (leftContents rightContents : Array Nat)
    (leftIncrementsFit : ∀ j (hj : j < leftContents.size), leftContents[j] + 1 < 2 ^ w)
    (rightIncrementsFit : ∀ j (hj : j < rightContents.size), rightContents[j] + 1 < 2 ^ w) :
    FunctionRealizable Implementation.program w 2 Implementation.boundedMapPairId
      (fun args heap => args.head.Contents heap leftContents ∧
        args.tail.head.Contents heap rightContents ∧ args.head.Disjoint args.tail.head ∧
        args.head.length < 2 ^ w ∧ args.tail.head.length < 2 ^ w ∧
        args.tail.tail.head < 2 ^ w) := by
  ram_source_realize (xs ys limit)
  rename_i heap input
  rcases input with
    ⟨observedLeft, observedRight, separated, leftLengthFits, rightLengthFits, limitFits⟩
  ram_source_call using (boundedMap_realizable hw leftContents leftIncrementsFit),
    (boundedMap_total_frame leftContents)
  all_goals
    try
      first
      | assumption
      | exact ⟨leftLengthFits, limitFits⟩
      | exact ⟨observedLeft, leftLengthFits, limitFits⟩
      | omega
  obtain ⟨_, frameLeft⟩ := ‹xs.Contents _ _ ∧ xs.PreservesOutside heap _›
  have rightAfter := frameLeft ys rightContents separated observedRight
  ram_source_call using (boundedMap_realizable hw rightContents rightIncrementsFit),
    (boundedMap_total_frame rightContents)
  all_goals
    first
    | assumption
    | exact ⟨rightLengthFits, limitFits⟩
    | exact ⟨rightAfter, rightLengthFits, limitFits⟩
    | trivial

/-- Each call uses its existing traversal-body bound and the actual generated
call overhead. The remaining instructions are the two normal sequence guards,
Unit return and enclosing function-body initialization. -/
def boundedMapPairBodyBound (leftSize rightSize : Nat) : Nat :=
  callCost Implementation.program Implementation.boundedMapId
      ((callCost Implementation.program Implementation.incrementId 10 + 47) * leftSize + 29) +
    callCost Implementation.program Implementation.boundedMapId
      ((callCost Implementation.program Implementation.incrementId 10 + 47) * rightSize + 29) + 8

/-- The source frame is reused only to justify the second callee's input at the
actual intermediate heap. Existing traversal bounds count both effectful calls;
no array-correctness or loop-cost argument is repeated. -/
theorem boundedMapPair_costBound (leftContents rightContents : Array Nat) :
    FunctionCostBound Implementation.program Implementation.boundedMapPairId
      (fun args heap => args.head.Contents heap leftContents ∧
        args.tail.head.Contents heap rightContents ∧ args.head.Disjoint args.tail.head)
      (fun _ _ => boundedMapPairBodyBound leftContents.size rightContents.size) := by
  ram_source_cost (xs ys limit)
  · rename_i heap input
    rcases input with ⟨observedLeft, observedRight, separated⟩
    ram_source_call using (boundedMap_costBound leftContents), (boundedMap_total_frame leftContents)
    obtain ⟨_, frameLeft⟩ := ‹xs.Contents _ _ ∧ xs.PreservesOutside heap _›
    have rightAfter := frameLeft ys rightContents separated observedRight
    ram_source_call using (boundedMap_costBound rightContents), (boundedMap_total_frame rightContents)
  · ram_source_cost_step
    simp only [boundedMapPairBodyBound]
    omega

/-- The actual compiled pair invocation returns both mapped arrays and the
outside-both frame in one represented final heap. Its independent instruction
bound includes both calls, while stack capacity allows pair/traversal/helper. -/
theorem boundedMapPair_runUntil_le {w heapLimit : Nat} (hw : 0 < w)
    (placement : Nat → Ram.Word w) (xs ys : Buffer .nat) (limit : Nat)
    (sourceHeap : Heap) (leftContents rightContents : Array Nat)
    (observedLeft : xs.Contents sourceHeap leftContents)
    (observedRight : ys.Contents sourceHeap rightContents) (separated : xs.Disjoint ys)
    (leftLengthFits : xs.length < 2 ^ w) (rightLengthFits : ys.length < 2 ^ w)
    (limitFits : limit < 2 ^ w)
    (leftIncrementsFit : ∀ j (hj : j < leftContents.size), leftContents[j] + 1 < 2 ^ w)
    (rightIncrementsFit : ∀ j (hj : j < rightContents.size), rightContents[j] + 1 < 2 ^ w)
    (entry : Ram.Source.State w) (represented : HeapRep placement heapLimit sourceHeap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.boundedMapPairId).length < 2 ^ w)
    (stackCapacity :
      heapLimit + 3 * Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w) :
    ∃ (finalHeap : Heap) (targetFinish : Ram.Source.State w)
        (bodySteps : Nat) (target : Ram.State w),
      Implementation.boundedMapPair xs ys limit sourceHeap = Part.some (.ok (), finalHeap) ∧
      xs.Contents finalHeap (leftContents.map fun x => min (x + 1) limit) ∧
      ys.Contents finalHeap (rightContents.map fun x => min (x + 1) limit) ∧
      (∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
        xs.Disjoint other → ys.Disjoint other →
          other.Contents sourceHeap contents → other.Contents finalHeap contents) ∧
      Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 2
        (lowerFunc Implementation.program Implementation.boundedMapPairId)
        (envWords placement (Env.cons (τ := .buffer .nat) xs
          (Env.cons (τ := .buffer .nat) ys (Env.cons (τ := .nat) limit Env.empty))))
        entry [] targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.boundedMapPairId.val 5 heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .buffer .nat) ys (Env.cons (τ := .nat) limit Env.empty)))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.boundedMapPairId) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 0 target = [] ∧
      Ram.Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc Implementation.program Implementation.boundedMapPairId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .buffer .nat) ys (Env.cons (τ := .nat) limit Env.empty)))) entry =
        Part.some bodySteps ∧
      bodySteps ≤ boundedMapPairBodyBound leftContents.size rightContents.size ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapPairId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapPairId)
          (boundedMapPairBodyBound leftContents.size rightContents.size) + 1 := by
  let args : Env [.buffer .nat, .buffer .nat, .nat] :=
    Env.cons (τ := .buffer .nat) xs
      (Env.cons (τ := .buffer .nat) ys (Env.cons (τ := .nat) limit Env.empty))
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using
      And.intro leftLengthFits (And.intro rightLengthFits limitFits)
  obtain ⟨value, finalHeap, targetFinish, bodySteps, target, sourceEval, property, invocation,
      representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩ :=
    (boundedMapPair_realizable hw leftContents rightContents leftIncrementsFit rightIncrementsFit).runUntil_le
      (boundedMapPair_total leftContents rightContents)
      (boundedMapPair_costBound leftContents rightContents) hw args sourceHeap arguments
      ⟨observedLeft, observedRight, separated, leftLengthFits, rightLengthFits, limitFits⟩
      ⟨observedLeft, observedRight, separated⟩ ⟨observedLeft, observedRight, separated⟩
      entry represented codeCapacity stackCapacity
  cases value
  simp only [valueWords_unit] at invocation values
  exact ⟨finalHeap, targetFinish, bodySteps, target, sourceEval,
    property.1, property.2.1, property.2.2, invocation, representedFinal,
    run, values, targetObserved, time, bodyBound, invocationBound⟩

end Complexity.Language.Examples.Traversal
