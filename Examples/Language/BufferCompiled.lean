/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Buffer
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiling the borrowed-buffer consumer

The existing `clipHead` source program reads, calls its branching helper, writes,
slices and returns a real borrowed view. Its source correctness proof is reused
unchanged. Realization adds the actual scalar and descriptor ranges; the backend
uses the shared heap representation, including overlapping aliases.

Independent cost composition counts the same operations and actual helper call.
The final theorem retains the changed source heap, its represented target state,
the two returned descriptor fields and the halted invocation's measured count.
Neither a register proof nor an instruction-price annotation is supplied here.
-/

namespace Complexity.Language.Examples.BorrowedBuffer

open Ram.LanguageCompiler

/-- The helper needs representable inputs and one Boolean guard, but no nested call. -/
theorem clamp_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Implementation.program w 0 Implementation.clampId
      (fun args _ => args.head < 2 ^ w ∧ args.tail.head < 2 ^ w) := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (x limit)
  all_goals omega

/-- Only the read cell, limit and actual view length need source range facts.
The current contents justify access; aliases are not required to be disjoint. -/
theorem clipHead_realizable {w : Nat} (hw : 0 < w) (contents : Array Nat)
    (nonempty : 0 < contents.size) :
    FunctionRealizable Implementation.program w 1 Implementation.clipHeadId
      (fun args heap => args.head.Contents heap contents ∧ args.head.length < 2 ^ w ∧
        contents[0] < 2 ^ w ∧ args.tail.head < 2 ^ w) := by
  ram_source_realize (xs limit) using (clamp_realizable hw), clamp_total
  all_goals
    rcases ‹xs.Contents _ contents ∧ xs.length < 2 ^ w ∧
      contents[0] < 2 ^ w ∧ limit < 2 ^ w› with
      ⟨observed, lengthFits, headFits, limitFits⟩
    first
    | omega
    | exact ⟨contents[0], observed.read nonempty, headFits⟩
    | rcases ‹_ = min _ _ ∧ _ = _› with ⟨_, rfl⟩
      exact (observed.write_exists nonempty _).imp (fun _ written => written.1)

/-- The bound is derived by the shared primitive, branch and return cost rules. -/
theorem clamp_costBound :
    FunctionCostBound Implementation.program Implementation.clampId (fun _ _ => True)
      (fun _ _ => 13) := by
  ram_source_cost (x limit)
  all_goals omega

/-- Read, helper call, write, length, slice and return are all charged by the
shared lowering rules. This conditional cost proof does not repeat correctness. -/
theorem clipHead_costBound :
    FunctionCostBound Implementation.program Implementation.clipHeadId (fun _ _ => True)
      (fun _ _ => callCost Implementation.program Implementation.clampId 13 + 28) := by
  ram_source_cost (xs limit) using clamp_costBound
  all_goals omega

/-- The same compiled invocation returns the actual descriptor and represents
the source program's updated contents. The read value's range follows from the
input heap representation; no additional cell-range or no-alias premise is imposed.
The independent body bound includes internal calls, and the complete bound adds
the outer call and halt once. -/
theorem clipHead_runUntil_le {w heapLimit : Nat} (hw : 0 < w)
    (placement : Nat → Ram.Word w) (xs : Buffer .nat) (limit : Nat)
    (sourceHeap : Heap) (contents : Array Nat) (nonempty : 0 < contents.size)
    (observed : xs.Contents sourceHeap contents)
    (lengthFits : xs.length < 2 ^ w) (limitFits : limit < 2 ^ w)
    (entry : Ram.Source.State w) (represented : HeapRep placement heapLimit sourceHeap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.clipHeadId).length < 2 ^ w)
    (stackCapacity :
      heapLimit + 2 * Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w) :
    ∃ (finalHeap : Heap) (targetFinish : Ram.Source.State w)
        (bodySteps : Nat) (target : Ram.State w),
      Implementation.clipHead xs limit sourceHeap = Part.some (.ok xs, finalHeap) ∧
      xs.Contents finalHeap (contents.set 0 (min (getElem contents 0 nonempty) limit) nonempty) ∧
      Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 1
        (lowerFunc Implementation.program Implementation.clipHeadId)
        (envWords placement (Env.cons (τ := .buffer .nat) xs
          (Env.cons (τ := .nat) limit Env.empty))) entry
        (valueWords placement (τ := .buffer .nat) xs) targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.clipHeadId.val 3 heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.clipHeadId) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 2 target =
        valueWords placement (τ := .buffer .nat) xs ∧
      Ram.Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc Implementation.program Implementation.clipHeadId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry = Part.some bodySteps ∧
      bodySteps ≤ callCost Implementation.program Implementation.clampId 13 + 28 ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.clipHeadId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.clipHeadId)
          (callCost Implementation.program Implementation.clampId 13 + 28) + 1 := by
  let args : Env [.buffer .nat, .nat] :=
    Env.cons (τ := .buffer .nat) xs (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using
      And.intro lengthFits limitFits
  have headFits : getElem contents 0 nonempty < 2 ^ w :=
    (represented.read (observed.read nonempty)).2.2
  obtain ⟨view, finalHeap, targetFinish, bodySteps, target, sourceEval, property, invocation,
      representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩ :=
    (clipHead_realizable hw contents nonempty).runUntil_le
      (clipHead_total contents nonempty) clipHead_costBound hw args sourceHeap arguments
      ⟨observed, lengthFits, headFits, limitFits⟩ observed trivial entry represented
      codeCapacity stackCapacity
  have sameView : (view : Buffer .nat) = xs := property.1
  subst view
  exact ⟨finalHeap, targetFinish, bodySteps, target, sourceEval, property.2, invocation,
    representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩

end Complexity.Language.Examples.BorrowedBuffer
