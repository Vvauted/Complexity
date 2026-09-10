/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Traversal
import Complexity.Control.Part.StateT
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound.Locals
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiling the named mutable traversal

The source traversal and its ordinary array-map correctness theorem are reused
unchanged. Realization checks the actual intermediate increments and call
nesting; independent cost rules count the same helper, branches and stores.
The compiler supplies register transport and the connection to actual execution.
-/

namespace Complexity.Language.Examples.Traversal

open Ram.LanguageCompiler
open scoped Part.TotalCorrectness

/-- The source helper's existing ordinary equation supplies its callable
contract without a second proof of the addition. -/
theorem increment_total :
    FunctionTotal Implementation.program Implementation.incrementId (fun _ _ => True)
      (fun args heap value finish => value = args.head + 1 ∧ finish = heap) := by
  apply (Implementation.increment_total_iff (fun _ _ => True)
    (fun x heap value finish => value = x + 1 ∧ finish = heap)).mpr
  intro x heap _
  exact ⟨x + 1, heap, congrFun (increment_eval x) heap, rfl, rfl⟩

/-- The actual increment, not only its later clipped value, must fit the word
backend. The helper has no nested calls. -/
theorem increment_realizable {w : Nat} :
    FunctionRealizable Implementation.program w 0 Implementation.incrementId
      (fun args _ => args.head + 1 < 2 ^ w) := by
  ram_source_realize (x)
  all_goals omega

/-- The proved primitive, return and initialization charges bound this helper's
actual generated body. This bound is independent of its termination proof. -/
theorem increment_costBound :
    FunctionCostBound Implementation.program Implementation.incrementId (fun _ _ => True)
      (fun _ _ => 10) := by
  ram_source_cost (x)

/-- Guard evaluation includes the current buffer length, comparison and its
Boolean return. Its bound is uniform in the source locals and current heap. -/
theorem guard_costBound (locals : Implementation.boundedMap_loop1.Locals) (heap : Heap) :
    StmtCostBound Implementation.program Implementation.boundedMap_loop1.Guard
      ⟨Implementation.boundedMap_loop1.View.symm locals, heap⟩ 10 := by
  apply StmtCostBound.mono
  · ram_source_cost_step
  · ram_source_cost_step

/-- A body includes the real read, helper call, selected store and local index
update. Its uniform bound needs no second contents or termination proof. -/
theorem body_costBound (locals : Implementation.boundedMap_loop1.Locals) (heap : Heap) :
    StmtCostBound Implementation.program Implementation.boundedMap_loop1.Body
      ⟨Implementation.boundedMap_loop1.View.symm locals, heap⟩
      (callCost Implementation.program Implementation.incrementId 10 + 27) := by
  apply StmtCostBound.mono
  · ram_source_cost_step using increment_costBound
  · ram_source_cost_step
    omega

/-- The real loop has a linear potential: every round pays for its guard,
body and loop control, and the remaining constant pays for the final false
guard. The original source invariant supplies preservation, not new contents
or termination reasoning in the cost proof. -/
theorem loop_costBound (xs : Buffer .nat) (limit : Nat) (contents : Array Nat)
    (i : Nat) (heap : Heap) (current : invariant xs limit contents i heap) :
    StmtCostBound Implementation.program Implementation.boundedMap_loop1.Code
      ⟨Implementation.boundedMap_loop1.View.symm (i, xs, limit, ()), heap⟩
      ((callCost Implementation.program Implementation.incrementId 10 + 47) *
        (contents.size - i) + 21) := by
  apply StmtCostBound.while_contract_fixed Implementation.boundedMap_loop1.CaptureView
    Implementation.boundedMap_loop1.guard_preservesCaptures
    Implementation.boundedMap_loop1.body_preservesCaptures (xs, limit, ())
    (guard_contract xs limit contents) (body_contract xs limit contents)
    (fun _ _ _ _ _ ready => ⟨ready.2.2.1, ready.2.2.2.mp rfl⟩)
    (mutable := (i, ())) (heap := heap)
    (invariant := fun mutable => invariant xs limit contents mutable.1)
    (guardBound := fun _ _ => 10)
    (bodyBound := fun _ _ _ _ => callCost Implementation.program Implementation.incrementId 10 + 27)
    (potential := fun locals _ =>
      (callCost Implementation.program Implementation.incrementId 10 + 47) *
        (contents.size - locals.1) + 21)
  · intro mutable heap _
    exact guard_costBound (mutable.1, xs, limit, ()) heap
  · intro mutable heap afterGuard afterHeap _ _
    exact body_costBound (afterGuard.1, xs, limit, ()) afterHeap
  · intro _ _ _ _ _ _ _ _ completed
    exact completed.2.1
  · intro mutable heap afterGuard afterHeap _ _
    dsimp only
    omega
  · rintro ⟨j, ⟨⟩⟩ entry ⟨k, ⟨⟩⟩ afterHeap ⟨l, ⟨⟩⟩ bodyHeap initial ready completed
    have next : l = j + 1 := completed.1.trans (congrArg (· + 1) ready.1)
    have nextBound : l ≤ contents.size := completed.2.1.1
    have remaining : contents.size - j = contents.size - (j + 1) + 1 := by omega
    dsimp (config := { failIfUnchanged := false }) only
    rw [next, remaining, Nat.mul_add, Nat.mul_one]
    omega
  · intro _ _ _ _ _ _ _ _ _ impossible
    exact False.elim impossible
  · exact current

/-- Guard realization only needs the compared natural values and its Boolean
result to fit. No assumption on the array's contents is used by the guard. -/
theorem guard_realizable {w : Nat} (hw : 0 < w) (xs : Buffer .nat) (limit i : Nat)
    (heap : Heap) (indexFits : i < 2 ^ w) (lengthFits : xs.length < 2 ^ w) :
    RealizationWP Implementation.program w 1 Implementation.boundedMap_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨Implementation.boundedMap_loop1.View.symm (i, xs, limit, ()), heap⟩ := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  rw [Implementation.boundedMap_loop1.view_symm_apply]
  ram_source_realize_step
  all_goals
    first
    | omega
    | split <;> omega

/-- Realize a single body using its current unread cell and the already proved
helper contract. The ordinary source invariant supplies access validity; only
actual intermediate ranges and one call level are added here. -/
theorem body_realizable {w : Nat} (hw : 0 < w) (xs : Buffer .nat) (limit : Nat)
    (contents : Array Nat) (i : Nat) (heap : Heap)
    (current : invariant xs limit contents i heap) (bound : i < contents.size)
    (lengthFits : xs.length < 2 ^ w) (limitFits : limit < 2 ^ w)
    (incrementFits : contents[i] + 1 < 2 ^ w) :
    RealizationWP Implementation.program w 1 Implementation.boundedMap_loop1.Body
      (fun _ => True) (fun _ _ => True)
      ⟨Implementation.boundedMap_loop1.View.symm (i, xs, limit, ()), heap⟩ := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have size : contents.size = xs.length := by
    simpa only [Array.size_mapIdx] using current.2.size_eq
  have loaded : heap.read xs i = .ok contents[i] :=
    invariant_read xs limit contents current bound
  have writable (value : Nat) : ∃ finish, heap.write xs i value = .ok finish := by
    have available : i <
        (contents.mapIdx fun j x => if j < i then min (x + 1) limit else x).size := by
      simpa only [Array.size_mapIdx] using bound
    obtain ⟨finish, written, _⟩ := current.2.write_exists available value
    exact ⟨finish, written⟩
  rw [Implementation.boundedMap_loop1.view_symm_apply]
  ram_source_realize_step using increment_realizable, increment_total
  all_goals
    simp only [loaded, Except.ok.injEq] at *
    first
    | omega
    | exact ⟨contents[i], rfl, by omega⟩
    | have sameHeap : _ = heap := (‹_ ∧ _ = heap›).2
      rw [sameHeap]
      exact writable _

/-- Source totality already proves termination of this loop. The additional
proof only checks guard/body realizability and reuses the source step's closed
invariant; there is no second well-founded induction or time-budget premise. -/
theorem loop_realizable {w : Nat} (hw : 0 < w) (xs : Buffer .nat) (limit : Nat)
    (contents : Array Nat) (i : Nat) (heap : Heap)
    (current : invariant xs limit contents i heap)
    (lengthFits : xs.length < 2 ^ w) (limitFits : limit < 2 ^ w)
    (incrementsFit : ∀ j (hj : j < contents.size), contents[j] + 1 < 2 ^ w) :
    RealizationWP Implementation.program w 1 Implementation.boundedMap_loop1.Code
      (fun _ => True) (fun _ _ => False)
      ⟨Implementation.boundedMap_loop1.View.symm (i, xs, limit, ()), heap⟩ := by
  have total : TotalWP Implementation.program Implementation.boundedMap_loop1.Code
      (fun _ => True) (fun _ _ => False)
      ⟨Implementation.boundedMap_loop1.View.symm (i, xs, limit, ()), heap⟩ := by
    apply (TotalWP.iff_triple_observe Implementation.boundedMap_loop1.CaptureView
      (locals := ((i, ()), xs, limit, ()))).mpr
    exact (Stmt.BlockSpec.mono (loop_contract xs limit contents heap)
      (fun _ _ initial => initial) (fun _ _ _ _ _ _ => True.intro)
      (fun _ _ _ _ _ _ impossible => impossible)).«at» (i, ()) heap
        ⟨current, Buffer.PreservesOutside.refl xs heap⟩
  apply RealizationWP.while_contract_fixed_of_total Implementation.boundedMap_loop1.CaptureView
    Implementation.boundedMap_loop1.guard_preservesCaptures
    Implementation.boundedMap_loop1.body_preservesCaptures (xs, limit, ())
    (guard_contract xs limit contents) (body_contract xs limit contents)
    (fun _ _ _ _ _ ready => ⟨ready.2.2.1, ready.2.2.2.mp rfl⟩)
    (mutable := (i, ())) (heap := heap)
    (invariant := fun mutable => invariant xs limit contents mutable.1) total
  · rintro ⟨j, ⟨⟩⟩ entry initial
    have size : contents.size = xs.length := by
      simpa only [Array.size_mapIdx] using initial.2.size_eq
    exact guard_realizable hw xs limit j entry (by have := initial.1; omega) lengthFits
  · rintro ⟨j, ⟨⟩⟩ entry ⟨k, ⟨⟩⟩ afterHeap initial ready
    have available : k < contents.size := ready.2.2.2.mp rfl
    exact body_realizable hw xs limit contents k afterHeap ready.2.2.1 available lengthFits limitFits
      (incrementsFit k available)
  · intro _ _ _ _ _ _ _ _ completed
    exact completed.2.1
  · exact current

/-- The traversal uses one call level for its helper. Its original values'
increments, limit and view length are the genuine bounded-word obligations. -/
theorem boundedMap_realizable {w : Nat} (hw : 0 < w) (contents : Array Nat)
    (incrementsFit : ∀ j (hj : j < contents.size), contents[j] + 1 < 2 ^ w) :
    FunctionRealizable Implementation.program w 1 Implementation.boundedMapId
      (fun args heap => args.head.Contents heap contents ∧ args.head.length < 2 ^ w ∧
        args.tail.head < 2 ^ w) := by
  have positive : 0 < 2 ^ w := Nat.two_pow_pos w
  ram_source_realize (xs limit)
  all_goals
    rcases ‹xs.Contents _ contents ∧ xs.length < 2 ^ w ∧ limit < 2 ^ w› with
      ⟨observed, lengthFits, limitFits⟩
    first
    | omega
    | apply (loop_realizable hw xs limit contents 0 _
        (invariant_zero xs limit contents observed) lengthFits limitFits incrementsFit).mono_post
      · intro finish _
        ram_source_realize_step
      · intro value finish impossible
        exact False.elim impossible

/-- The complete body bound adds initialization and the actual final return to
the loop potential. The supplied source contents are reused solely to identify
the traversal's already proved state transitions. -/
theorem boundedMap_costBound (contents : Array Nat) :
    FunctionCostBound Implementation.program Implementation.boundedMapId
      (fun args heap => args.head.Contents heap contents)
      (fun _ _ =>
        (callCost Implementation.program Implementation.incrementId 10 + 47) * contents.size + 29) := by
  ram_source_cost (xs limit)
  · have bound : StmtCostBound Implementation.program Implementation.boundedMap_loop1.Code
        ⟨Implementation.boundedMap_loop1.View.symm (0, xs, limit, ()), _⟩
        ((callCost Implementation.program Implementation.incrementId 10 + 47) *
          (contents.size - 0) + 21) :=
      @loop_costBound xs limit contents 0 _
        (invariant_zero xs limit contents ‹xs.Contents _ contents›)
    simp only [Implementation.boundedMap_loop1.view_symm_apply, Nat.sub_zero] at bound
    exact @bound
  · omega

/-- The compiled traversal halts with its ordinary array-map result and preserves
every initially observed disjoint view in the same represented final heap.
Its independent linear instruction bound describes that very invocation.
Preloaded objects, intermediate increments, code and stack capacity are explicit;
no operational time budget or algorithm-specific register proof is assumed. -/
theorem boundedMap_runUntil_le_frame {w heapLimit : Nat} (hw : 0 < w)
    (placement : Nat → Ram.Word w) (xs : Buffer .nat) (limit : Nat)
    (sourceHeap : Heap) (contents : Array Nat) (observed : xs.Contents sourceHeap contents)
    (lengthFits : xs.length < 2 ^ w) (limitFits : limit < 2 ^ w)
    (incrementsFit : ∀ j (hj : j < contents.size), contents[j] + 1 < 2 ^ w)
    (entry : Ram.Source.State w) (represented : HeapRep placement heapLimit sourceHeap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.boundedMapId).length < 2 ^ w)
    (stackCapacity :
      heapLimit + 2 * Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w) :
    ∃ (finalHeap : Heap) (targetFinish : Ram.Source.State w)
        (bodySteps : Nat) (target : Ram.State w),
      Implementation.boundedMap xs limit sourceHeap = Part.some (.ok (), finalHeap) ∧
      xs.Contents finalHeap (contents.map fun x => min (x + 1) limit) ∧
      xs.PreservesOutside sourceHeap finalHeap ∧
      Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 1
        (lowerFunc Implementation.program Implementation.boundedMapId)
        (envWords placement (Env.cons (τ := .buffer .nat) xs
          (Env.cons (τ := .nat) limit Env.empty))) entry [] targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.boundedMapId.val 3 heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.boundedMapId) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 0 target = [] ∧
      Ram.Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc Implementation.program Implementation.boundedMapId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry = Part.some bodySteps ∧
      bodySteps ≤
        (callCost Implementation.program Implementation.incrementId 10 + 47) * contents.size + 29 ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapId)
          ((callCost Implementation.program Implementation.incrementId 10 + 47) *
            contents.size + 29) + 1 := by
  let args : Env [.buffer .nat, .nat] :=
    Env.cons (τ := .buffer .nat) xs (Env.cons (τ := .nat) limit Env.empty)
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using
      And.intro lengthFits limitFits
  obtain ⟨value, finalHeap, targetFinish, bodySteps, target, sourceEval, property, invocation,
      representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩ :=
    (boundedMap_realizable hw contents incrementsFit).runUntil_le
      (boundedMap_total_frame contents) (boundedMap_costBound contents) hw args sourceHeap arguments
      ⟨observed, lengthFits, limitFits⟩ observed observed entry represented
      codeCapacity stackCapacity
  cases value
  simp only [valueWords_unit] at invocation values
  exact ⟨finalHeap, targetFinish, bodySteps, target, sourceEval, property.1, property.2, invocation,
    representedFinal, run, values, targetObserved, time, bodyBound, invocationBound⟩

/-- The same compiled traversal halts, realizes the ordinary array-map result
in its actual final heap, and satisfies the independent linear body bound.
Preloaded objects, intermediate increments, code and stack capacity are explicit;
no operational time budget or algorithm-specific register proof is assumed. -/
theorem boundedMap_runUntil_le {w heapLimit : Nat} (hw : 0 < w)
    (placement : Nat → Ram.Word w) (xs : Buffer .nat) (limit : Nat)
    (sourceHeap : Heap) (contents : Array Nat) (observed : xs.Contents sourceHeap contents)
    (lengthFits : xs.length < 2 ^ w) (limitFits : limit < 2 ^ w)
    (incrementsFit : ∀ j (hj : j < contents.size), contents[j] + 1 < 2 ^ w)
    (entry : Ram.Source.State w) (represented : HeapRep placement heapLimit sourceHeap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.boundedMapId).length < 2 ^ w)
    (stackCapacity :
      heapLimit + 2 * Ram.ABI.frameSize (programControl Implementation.program) < 2 ^ w) :
    ∃ (finalHeap : Heap) (targetFinish : Ram.Source.State w)
        (bodySteps : Nat) (target : Ram.State w),
      Implementation.boundedMap xs limit sourceHeap = Part.some (.ok (), finalHeap) ∧
      xs.Contents finalHeap (contents.map fun x => min (x + 1) limit) ∧
      Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 1
        (lowerFunc Implementation.program Implementation.boundedMapId)
        (envWords placement (Env.cons (τ := .buffer .nat) xs
          (Env.cons (τ := .nat) limit Env.empty))) entry [] targetFinish ∧
      HeapRep placement heapLimit finalHeap targetFinish ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.boundedMapId.val 3 heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry =
        some ⟨target,
          Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
            (lowerFunc Implementation.program Implementation.boundedMapId) bodySteps + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 0 target = [] ∧
      Ram.Source.State.Observes heapLimit 0 targetFinish target ∧
      (lowerFunc Implementation.program Implementation.boundedMapId).bodyTime
          (lowerProgram Implementation.program) heapLimit
          (envWords placement (Env.cons (τ := .buffer .nat) xs
            (Env.cons (τ := .nat) limit Env.empty))) entry = Part.some bodySteps ∧
      bodySteps ≤
        (callCost Implementation.program Implementation.incrementId 10 + 47) * contents.size + 29 ∧
      Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapId) bodySteps + 1 ≤
        Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.boundedMapId)
          ((callCost Implementation.program Implementation.incrementId 10 + 47) *
            contents.size + 29) + 1 := by
  obtain ⟨finalHeap, targetFinish, bodySteps, target, executed, updated, _, rest⟩ :=
    boundedMap_runUntil_le_frame hw placement xs limit sourceHeap contents observed
      lengthFits limitFits incrementsFit entry represented codeCapacity stackCapacity
  exact ⟨finalHeap, targetFinish, bodySteps, target, executed, updated, rest⟩

end Complexity.Language.Examples.Traversal
