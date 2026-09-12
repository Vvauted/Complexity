/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Imports
import Examples.Language.TraversalCompositionCompiled
import Complexity.Computability.Ram.Compiler.Language.Linking.Tactic

/-!
# Compiling effectful calls into an imported traversal library

The existing import client calls the library traversal twice. Each selected
library contract is transported through the generated source embedding. The
first call's actual frame establishes the second call's input; neither loop,
array-correctness argument nor register-level lowering is proved again.

The client has the same emitted call structure as the original two-buffer
composition. Its bound reuses that existing numerical expression and the proved
preservation of callee overhead under embedding. The final theorem concerns the
client's actual invocation in the combined program, with two mapped buffers,
the outside-both frame and one represented final heap. Code and three-frame
stack capacity refer to this combined program, not the smaller library table.
-/

namespace Complexity.Language.Examples.Imports

open Ram.LanguageCompiler

/-- The existing source correctness proof supplies both array results and the
outside-both frame, without reopening either imported traversal. -/
theorem boundedMapPair_total (leftContents rightContents : Array Nat) :
    FunctionTotal Implementation.program Implementation.boundedMapPairId
      (fun args heap => args.head.Contents heap leftContents ∧
        args.tail.head.Contents heap rightContents ∧ args.head.Disjoint args.tail.head)
      (fun args initial _ finish =>
        args.head.Contents finish
          (leftContents.map fun x => min (x + 1) args.tail.tail.head) ∧
        args.tail.head.Contents finish
          (rightContents.map fun x => min (x + 1) args.tail.tail.head) ∧
        ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
          args.head.Disjoint other → args.tail.head.Disjoint other →
            other.Contents initial contents → other.Contents finish contents) := by
  apply (Implementation.boundedMapPair_total_iff
    (fun xs ys _ heap => xs.Contents heap leftContents ∧
      ys.Contents heap rightContents ∧ xs.Disjoint ys)
    (fun xs ys limit initial _ finish =>
      xs.Contents finish (leftContents.map fun x => min (x + 1) limit) ∧
      ys.Contents finish (rightContents.map fun x => min (x + 1) limit) ∧
      ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
        xs.Disjoint other → ys.Disjoint other →
          other.Contents initial contents → other.Contents finish contents)).mpr
  rintro xs ys limit heap ⟨observedLeft, observedRight, separated⟩
  obtain ⟨finish, executed, mappedLeft, mappedRight, frame⟩ :=
    boundedMapPair_eval xs ys limit observedLeft observedRight separated
  exact ⟨(), finish, executed, mappedLeft, mappedRight, frame⟩

/-- The client, imported traversal and increment helper need two nested call
levels. The original value ranges and actual intermediate-heap frame are retained. -/
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
  ram_source_call using (Traversal.boundedMap_realizable hw leftContents leftIncrementsFit),
    (Traversal.boundedMap_total_frame leftContents)
    via Implementation.imports.Traversal.Implementation.embedding
  all_goals
    try
      first
      | assumption
      | exact ⟨leftLengthFits, limitFits⟩
      | exact ⟨observedLeft, leftLengthFits, limitFits⟩
      | omega
  obtain ⟨_, frameLeft⟩ := ‹xs.Contents _ _ ∧ xs.PreservesOutside heap _›
  have rightAfter := frameLeft ys rightContents separated observedRight
  ram_source_call using (Traversal.boundedMap_realizable hw rightContents rightIncrementsFit),
    (Traversal.boundedMap_total_frame rightContents)
    via Implementation.imports.Traversal.Implementation.embedding
  all_goals
    first
    | assumption
    | exact ⟨rightLengthFits, limitFits⟩
    | exact ⟨rightAfter, rightLengthFits, limitFits⟩
    | trivial

/-- The imported callees retain their actual instruction bounds and frame
overhead. The client's unchanged call structure therefore admits the original
pair bound, while the first call's frame supplies the second call's current input. -/
theorem boundedMapPair_costBound (leftContents rightContents : Array Nat) :
    FunctionCostBound Implementation.program Implementation.boundedMapPairId
      (fun args heap => args.head.Contents heap leftContents ∧
        args.tail.head.Contents heap rightContents ∧ args.head.Disjoint args.tail.head)
      (fun _ _ => Traversal.boundedMapPairBodyBound leftContents.size rightContents.size) := by
  ram_source_cost (xs ys limit)
  · rename_i heap input
    rcases input with ⟨observedLeft, observedRight, separated⟩
    ram_source_call using (Traversal.boundedMap_costBound leftContents),
      (Traversal.boundedMap_total_frame leftContents)
      via Implementation.imports.Traversal.Implementation.embedding
    obtain ⟨_, frameLeft⟩ := ‹xs.Contents _ _ ∧ xs.PreservesOutside heap _›
    have rightAfter := frameLeft ys rightContents separated observedRight
    ram_source_call using (Traversal.boundedMap_costBound rightContents),
      (Traversal.boundedMap_total_frame rightContents)
      via Implementation.imports.Traversal.Implementation.embedding
  · ram_source_cost_step
    simp only [Traversal.boundedMapPairBodyBound,
      callCost_embeds Implementation.imports.Traversal.Implementation.embedding]
    omega

/-- The imported client's invocation budget includes its own outer call and
final halt, reusing the library pair's inferred body budget. -/
def boundedMapPairInvocationBound (leftSize rightSize : Nat) : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.boundedMapPairId)
    (Traversal.boundedMapPairBodyBound leftSize rightSize) + 1

/-- The imported client returns both ordinary mapped arrays in one typed actual
execution, preserving observations outside both borrowed views. The launch keeps
the combined program's original code/stack capacities and argument ranges. -/
theorem boundedMapPair_execute {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (xs ys : Buffer .nat) (limit : Nat) (leftContents rightContents : Array Nat) {heap : Heap}
    (observedLeft : xs.Contents heap leftContents)
    (observedRight : ys.Contents heap rightContents) (separated : xs.Disjoint ys)
    (leftIncrementsFit : ∀ j (hj : j < leftContents.size), leftContents[j] + 1 < 2 ^ w)
    (rightIncrementsFit : ∀ j (hj : j < rightContents.size), rightContents[j] + 1 < 2 ^ w)
    {entry : Ram.Source.State w}
    (launch : FunctionLaunch Implementation.program Implementation.boundedMapPairId 2 heapLimit
      placement (Implementation.boundedMapPair_args xs ys limit) heap entry) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.boundedMapPairId heapLimit
        placement (Implementation.boundedMapPair_args xs ys limit) heap entry,
      xs.Contents outcome.heap (leftContents.map fun x => min (x + 1) limit) ∧
      ys.Contents outcome.heap (rightContents.map fun x => min (x + 1) limit) ∧
      (∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
        xs.Disjoint other → ys.Disjoint other →
          other.Contents heap contents → other.Contents outcome.heap contents) ∧
      outcome.result.steps ≤ boundedMapPairInvocationBound leftContents.size rightContents.size := by
  have arguments : EnvFits (Γ := [.buffer .nat, .buffer .nat, .nat]) w
      (Implementation.boundedMapPair_args xs ys limit) := launch.arguments
  have leftLengthFits : xs.length < 2 ^ w := arguments .here
  have rightLengthFits : ys.length < 2 ^ w := arguments (.there .here)
  have limitFits : limit < 2 ^ w := arguments (.there (.there .here))
  obtain ⟨outcome, property, bounded⟩ :=
    (boundedMapPair_realizable launch.positive leftContents rightContents
      leftIncrementsFit rightIncrementsFit).execute_le
      (boundedMapPair_total leftContents rightContents)
      (boundedMapPair_costBound leftContents rightContents) launch
      ⟨observedLeft, observedRight, separated, leftLengthFits, rightLengthFits, limitFits⟩
      ⟨observedLeft, observedRight, separated⟩ ⟨observedLeft, observedRight, separated⟩
  exact ⟨outcome, property.1, property.2.1, property.2.2, bounded⟩

/-- The actual imported-traversal client halts with both mapped arrays and the
outside-both frame in one represented final heap. The independent instruction
bound covers both calls; capacity allows the client, traversal and helper frames. -/
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
      bodySteps ≤ Traversal.boundedMapPairBodyBound leftContents.size rightContents.size ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapPairId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapPairId)
          (Traversal.boundedMapPairBodyBound leftContents.size rightContents.size) + 1 := by
  let args : Env [.buffer .nat, .buffer .nat, .nat] :=
    Env.cons (τ := .buffer .nat) xs
      (Env.cons (τ := .buffer .nat) ys (Env.cons (τ := .nat) limit Env.empty))
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using
      And.intro leftLengthFits (And.intro rightLengthFits limitFits)
  obtain ⟨value, finalHeap, targetFinish, bodySteps, target, sourceEval, property, invocation,
      representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩ :=
    (boundedMapPair_realizable hw leftContents rightContents leftIncrementsFit
      rightIncrementsFit).runUntil_le
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

end Complexity.Language.Examples.Imports
