/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.ScopeCompiledWork
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop
import Complexity.Computability.Ram.Compiler.Language.Arena.Memory
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiling repeated calls with reusable temporary storage

The source declaration and its mathematical correctness proof remain unchanged.
Its real worker allocates nested scratch arrays, returns through scope cleanup,
and updates a result allocated outside those scopes. Resource readiness adds
only finite-word ranges, actual call nesting and simultaneous scratch capacity.

The loop reuses the same arena boundary after every call. Its source proof
supplies termination; the compiled memory guarantee concerns every real access
of the complete call-and-halt invocation, including transient accesses and the
call stack, rather than only the final allocator cursor.
-/

namespace Complexity.Language.Examples.Scope

open Ram.LanguageCompiler
open scoped Part.TotalCorrectness

/-- The existing scalar realization rules handle the actual generated guard.
Only the remaining call count is read; heap contents do not affect it. -/
theorem guard_realizable {w depth : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    (remainingFits : remaining < 2 ^ w) :
    RealizationWP Implementation.program w depth Implementation.make_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩ := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  rw [Implementation.make_loop1.view_symm_apply]
  ram_source_realize_step
  all_goals first | omega | split <;> omega

/-- Realize the exact successful guard execution already used by source
correctness, with no allocation and no change to the arena cursor. -/
theorem guard_ready {w limit depth cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State [.nat, .buffer .nat, .nat, .nat, .nat]} {decision : Bool}
    (remainingFits : remaining < 2 ^ w)
    (execution : Exec Implementation.program Implementation.make_loop1.Guard
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩
      finish (.returned decision)) :
    ArenaReady execution w limit depth cursor cursor := by
  obtain ⟨actualFinish, actualControl, actual, _⟩ :=
    guard_realizable hw remaining out count n value heap remainingFits
  obtain ⟨rfl, rfl⟩ := execution.deterministic actual.erase
  exact actual.arenaReady limit cursor

/-- The body calls the actual reclaiming worker and decrements the saved count.
The caller and callee share one cursor; returning from the worker restores its
scratch extent before the caller's normal continuation. -/
theorem body_ready {w limit cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State [.nat, .buffer .nat, .nat, .nat, .nat]}
    {control : Control (.buffer .nat)}
    (outRooted : out.Rooted heap) (outFits : out.length < 2 ^ w)
    (remainingFits : remaining < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.program Implementation.make_loop1.Body
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩
      finish control) (successful : ControlFits w control) :
    ArenaReady execution w limit 1 cursor cursor := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have arguments : EnvFits w
      (Env.cons (τ := .buffer .nat) out
        (Env.cons (τ := .nat) n (Env.cons (τ := .nat) value Env.empty))) := by
    simp only [EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty,
      outFits, nFits, valueFits, and_self]
  cases execution with
  | seqNormal called assigned =>
      cases called with
      | @callReturn _ _ _ _ _ _ calleeFinish returned _ _ callee continuation =>
          cases returned
          cases continuation with
          | skip =>
              cases assigned
              exact .seqNormal
                (.callReturn (callee := callee) (fun {τ} => arguments (τ := τ))
                  (work_ready out n value heap outRooted outFits nFits valueFits capacity callee)
                  (.skip _))
                (.assign _ _ _ ⟨remainingFits, oneFits⟩)
  | seqReturn called =>
      cases called with
      | callReturn callee continuation => cases continuation
  | seqFault called => exact False.elim successful

private theorem guard_exec (remaining : Nat) (out : Buffer .nat) (count n value : Nat)
    (heap : Heap) :
    Exec Implementation.program Implementation.make_loop1.Guard
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩
      (.returned (decide (0 < remaining))) := by
  apply Stmt.observe_eq_some_iff.mp
  rw [Implementation.make_loop1.guard_observe, guard_eval]
  rfl

/-- Every finite source loop reuses the same scratch capacity. The original
mathematical invariant and body contract supply preservation; the additional
proof checks only ranges and one level of actual callee nesting. -/
theorem loop_ready {w limit cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State [.nat, .buffer .nat, .nat, .nat, .nat]}
    {control : Control (.buffer .nat)}
    (current : invariant out count n value remaining heap)
    (countFits : count < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.program Implementation.make_loop1.Code
      ⟨Implementation.make_loop1.View.symm (remaining, out, count, n, value, ()), heap⟩
      finish control) (successful : ControlFits w control) :
    ArenaReady execution w limit 1 cursor cursor := by
  let roundInvariant : State [.nat, .buffer .nat, .nat, .nat, .nat] → Prop :=
    fun state => ∃ left,
      state.locals = Implementation.make_loop1.View.symm (left, out, count, n, value, ()) ∧
        invariant out count n value left state.heap
  apply ArenaReady.while_of_exec (invariant := roundInvariant) execution
  · rintro ⟨locals, entryHeap⟩ after decision ⟨left, rfl, initial⟩ tested
    have leftFits : left < 2 ^ w := lt_of_le_of_lt initial.1 countFits
    exact guard_ready hw left out count n value entryHeap leftFits tested
  · rintro ⟨locals, entryHeap⟩ afterGuard afterBody outcome ⟨left, rfl, initial⟩
      tested iterated success
    obtain ⟨sameState, _⟩ := tested.deterministic (guard_exec left out count n value entryHeap)
    cases sameState
    have length : out.length = 1 := by simpa using initial.2.size_eq.symm
    exact body_ready hw left out count n value entryHeap initial.2.valid.rooted
      (by rw [length]; exact Nat.one_lt_two_pow (Nat.ne_of_gt hw))
      (lt_of_le_of_lt initial.1 countFits) nFits valueFits capacity iterated success
  · rintro ⟨locals, entryHeap⟩ afterGuard afterBody ⟨left, rfl, initial⟩ tested iterated
    obtain ⟨sameState, sameControl⟩ :=
      tested.deterministic (guard_exec left out count n value entryHeap)
    cases sameState
    have active : 0 < left := of_decide_eq_true (Control.returned.inj sameControl).symm
    have observed : Implementation.make_loop1.body left out count n value entryHeap =
        Part.some ((.normal, Implementation.make_loop1.View afterBody.locals), afterBody.heap) := by
      rw [← Implementation.make_loop1.body_observe (left, out, count, n, value, ())]
      apply Stmt.observe_eq_some_iff.mpr
      simpa only [Equiv.symm_apply_apply] using iterated
    have updated := Part.TotalCorrectness.stateT_post_of_eq
      (body_spec out count n value initial active) rfl observed
    refine ⟨left - 1, ?_, updated.2⟩
    have localsEqual := congrArg Prod.snd updated.1
    simpa only [Equiv.symm_apply_apply] using
      congrArg Implementation.make_loop1.View.symm localsEqual
  · exact ⟨remaining, rfl, current⟩
  · exact successful

/-- The generated maker's ordinary arguments, in the source function table's
parameter order. This is an environment encoding, not another implementation. -/
def makeArgs (count n value : Nat) : Env [.nat, .nat, .nat] :=
  Env.cons count (Env.cons n (Env.cons value Env.empty))

/-- The complete maker retains only its one result cell. Its successful source
execution supplies termination, and the loop's source contract rules out an
unexpected early return. Temporary capacity is independent of `count`. -/
theorem make_ready {w limit cursor : Nat} (hw : 0 < w)
    (count n value : Nat) (heap : Heap)
    {finish : State [.nat, .nat, .nat]} {out : Buffer .nat}
    (countFits : count < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 1 + 2 * n ≤ limit)
    (execution : Exec Implementation.program Implementation.makeBody
      ⟨makeArgs count n value, heap⟩ finish (.returned out)) :
    ArenaReady execution w limit 1 cursor (cursor + 1) := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have initialized : (heap.alloc (τ := .nat) 1 0).1.Contents
      (heap.alloc (τ := .nat) 1 0).2 #[0] := by
    simpa using heap.alloc_contents (τ := .nat) 1 0
  have initial := invariant_initial (heap.alloc (τ := .nat) 1 0).1
    count n value initialized
  cases execution with
  | alloc continuation =>
      apply ArenaReady.alloc (body := continuation) (Nat.two_pow_pos w)
        (by change cursor + 1 ≤ limit; omega)
      cases continuation with
      | letPrim sequence =>
          apply ArenaReady.letPrim (body := sequence) countFits
          cases sequence with
          | @seqNormal _ _ _ _ _ middle _ _ loop returned =>
              apply ArenaReady.seqNormal (head := loop) (tail := returned)
                (loop_ready hw count (heap.alloc (τ := .nat) 1 0).1 count n value
                  (heap.alloc (τ := .nat) 1 0).2 initial
                  countFits nFits valueFits capacity loop trivial)
              have preserved : middle.locals.get (.there .here) =
                  (heap.alloc (τ := .nat) 1 0).1 :=
                loop.get_eq (.there .here) (by
                  simp [Implementation.make_loop1.Code, Implementation.make_loop1.Guard,
                    Implementation.make_loop1.Body, Stmt.PreservesLocal])
              have fits : ValueFits w
                  ((.var (.there .here) : Atom [.nat, .buffer .nat, .nat, .nat, .nat]
                    (.buffer .nat)).eval middle.locals) := by
                change (middle.locals.get (.there .here)).length < 2 ^ w
                rw [preserved]
                exact oneFits
              cases returned
              exact .ret _ _ fits
          | seqReturn loop =>
              obtain ⟨⟨actualControl, finalLocals⟩, finalHeap, actualObserved, property⟩ :=
                (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
                  (loop_spec (heap.alloc (τ := .nat) 1 0).1 count n value count)
                  (heap.alloc (τ := .nat) 1 0).2 initial
              have actual : Exec Implementation.program Implementation.make_loop1.Code
                  ⟨Implementation.make_loop1.View.symm
                    (count, (heap.alloc (τ := .nat) 1 0).1, count, n, value, ()),
                    (heap.alloc (τ := .nat) 1 0).2⟩
                  ⟨Implementation.make_loop1.View.symm finalLocals, finalHeap⟩ actualControl :=
                Stmt.observe_eq_some_iff.mp actualObserved
              have sameControl := (loop.deterministic actual).2
              cases actualControl with
              | normal => cases sameControl
              | returned _ => exact False.elim property
              | fault _ => exact False.elim property

/-- A sufficient physical workspace envelope: the retained entry arena, one
result word, two simultaneously live scratch arrays, and two actual call frames.
The frame size is derived from the fixed generated program, not from `count`. -/
def workspaceWords (entryCursor n : Nat) : Nat :=
  heapLimit entryCursor n + 2 * Ram.ABI.frameSize (programControl Implementation.program)

set_option maxRecDepth 2048 in
/-- The same high-level declaration returns its mathematical array in the real
halted RAM invocation. Every actual memory access, and therefore every distinct
word touched, stays within a workspace bound independent of the iteration count.
Preloaded input representation, scalar ranges and word/code capacity are explicit;
input loading and output conversion remain outside this invocation boundary. -/
theorem make_runUntil {w cursor : Nat} (hw : 0 < w)
    (count n value : Nat) (heap : Heap)
    (countFits : count < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (entry : Ram.Source.State w) {placement : Nat → Ram.Word w}
    (arena : ArenaRep placement cursor (heapLimit cursor n) heap entry)
    (codeCapacity : (lowerCode Implementation.program Implementation.makeId).length < 2 ^ w)
    (stackCapacity : workspaceWords cursor n < 2 ^ w) :
    ∃ (out : Buffer .nat) (finalHeap : Heap) (steps : Nat)
        (finalPlacement : Nat → Ram.Word w) (finishTarget : Ram.Source.State w)
        (target : Ram.State w),
      Implementation.make count n value heap = Part.some (.ok out, finalHeap) ∧
      out.Contents finalHeap (resultContents count n value) ∧
      ArenaRep finalPlacement (cursor + 1) (heapLimit cursor n) finalHeap finishTarget ∧
      Ram.LocalCompiler.Function.runUntil (programControl Implementation.program)
          (lowerProgram Implementation.program) Implementation.makeId.val
          (contextSize Implementation.signatures[Implementation.makeId].params)
          (heapLimit cursor n) (envWords placement (makeArgs count n value)) entry =
        some ⟨target, Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.makeId) (steps + 2) + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues 2 target =
        valueWords finalPlacement (τ := .buffer .nat) out ∧
      (bufferRef finalPlacement out).Rep (heapLimit cursor n)
        (objectWords w (τ := .nat) (resultContents count n value)).toList finishTarget ∧
      Ram.Source.State.Observes (heapLimit cursor n) 0 finishTarget target ∧
      (∀ address ∈ Ram.heapAccesses
        (lowerCode Implementation.program Implementation.makeId)
        (Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.makeId) (steps + 2) + 1)
        (Ram.LocalCompiler.Function.start (programControl Implementation.program)
          (heapLimit cursor n) (envWords placement (makeArgs count n value)) entry),
        address.toNat < workspaceWords cursor n) ∧
      (Ram.heapAccesses (lowerCode Implementation.program Implementation.makeId)
        (Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
          (lowerFunc Implementation.program Implementation.makeId) (steps + 2) + 1)
        (Ram.LocalCompiler.Function.start (programControl Implementation.program)
          (heapLimit cursor n) (envWords placement (makeArgs count n value)) entry)).card ≤
        workspaceWords cursor n := by
  have arguments : EnvFits w (makeArgs count n value) := by
    simp only [makeArgs, EnvFits.cons_nat_iff, EnvFits.empty,
      countFits, nFits, valueFits, and_self]
  have rooted : (makeArgs count n value).Rooted heap := by
    simp only [makeArgs, Env.Rooted.cons_iff, Env.Rooted.empty, ValueRooted, and_self]
  obtain ⟨finish, out, execution, contents⟩ :=
    make_total (makeArgs count n value) heap trivial
  have ready := make_ready hw count n value heap countFits nFits valueFits
    (limit := heapLimit cursor n) (cursor := cursor) (Nat.le_refl _) execution
  obtain ⟨steps, cost⟩ := ready.exists_cost
  obtain ⟨finalPlacement, finishTarget, target, invocation, finalArena, agreed,
    returned, fields, observed⟩ :=
    cost.runUntil (fn := Implementation.makeId) hw arguments rooted entry arena
      codeCapacity stackCapacity
  have outFits : out.length < 2 ^ w := by
    have length : out.length = 1 := by
      simpa only [resultContents] using contents.size_eq.symm
    rw [length]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  refine ⟨out, finish.heap, steps, finalPlacement, finishTarget, target, ?_, contents,
    finalArena, returned, fields, finalArena.heapRep.view contents outFits, observed, ?_, ?_⟩
  · exact Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩
  · intro address member
    exact cost.heapAccesses_below hw arguments rooted entry arena codeCapacity stackCapacity member
  · exact cost.heapAccesses_card_le hw arguments rooted entry arena codeCapacity stackCapacity

end Complexity.Language.Examples.Scope
