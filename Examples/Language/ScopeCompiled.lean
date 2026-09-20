/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.ScopeCompiledWork
import Complexity.Computability.Ram.Compiler.Language.LoopTactic
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution
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
    RealizationWP Implementation.Source.program w depth Implementation.Source.make_loop1.Guard
      (fun _ => False) (fun _ _ => True)
      ⟨Implementation.Source.make_loop1.View.symm
        (Implementation.Source.make_loop1.entry (remaining, out, count, n, value, ())), heap⟩ := by
  have booleanFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  dsimp only [Implementation.Source.make_loop1.entry]
  rw [Implementation.Source.make_loop1.view_symm_apply]
  ram_source_realize_step
  all_goals first | omega | split <;> omega

/-- Realize the exact successful guard execution already used by source
correctness, with no allocation and no change to the arena cursor. -/
theorem guard_ready {w limit depth cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State _} {decision : Bool}
    (remainingFits : remaining < 2 ^ w)
    (execution : Exec Implementation.Source.program Implementation.Source.make_loop1.Guard
      ⟨Implementation.Source.make_loop1.View.symm
        (Implementation.Source.make_loop1.entry (remaining, out, count, n, value, ())), heap⟩
      finish (.returned decision)) :
    ArenaReady execution w limit depth cursor cursor := by
  obtain ⟨actualFinish, actualControl, actual, _⟩ :=
    guard_realizable hw remaining out count n value heap remainingFits
  obtain ⟨rfl, rfl⟩ := execution.deterministic actual.erase
  exact actual.arenaReady limit cursor

/-- A completed local block takes the existing guard's false branch. Only
the stored result's range is needed; the original numeric test is not run. -/
private theorem completed_guard_ready {w limit depth cursor : Nat} (hw : 0 < w)
    (state : State _) (out : Buffer .nat) {finish : State _} {decision : Bool}
    (outFits : out.length < 2 ^ w)
    (stopped : Implementation.Source.make_loop1.pending
      (Implementation.Source.make_loop1.View state.locals) = some out)
    (execution : Exec Implementation.Source.program Implementation.Source.make_loop1.Guard
      state finish (.returned decision)) :
    ArenaReady execution w limit depth cursor cursor := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  dsimp only [Implementation.Source.make_loop1.pending,
    Implementation.Source.make_loop1.view_apply] at stopped
  refine RealizationWP.arenaReady
    (normal := fun _ => False) (returned := fun _ _ => True) ?_ execution limit cursor
  ram_source_realize_step
  all_goals simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals first | assumption | trivial | omega

/-- The body calls the actual reclaiming worker and decrements the saved count.
The caller and callee share one cursor; returning from the worker restores its
scratch extent before the caller's normal continuation. -/
theorem body_ready {w limit cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State _}
    {control : Control (.buffer .nat)}
    (outRooted : out.Rooted heap) (outFits : out.length < 2 ^ w)
    (remainingFits : remaining < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.make_loop1.Body
      ⟨Implementation.Source.make_loop1.View.symm
        (Implementation.Source.make_loop1.entry (remaining, out, count, n, value, ())), heap⟩
      finish control) (successful : ControlFits w control) :
    ArenaReady execution w limit 1 cursor cursor := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  dsimp only [Implementation.Source.make_loop1.entry] at execution
  rw [Implementation.Source.make_loop1.view_symm_apply] at execution
  have arguments : EnvFits w
      (Env.cons (τ := .buffer .nat) out
        (Env.cons (τ := .nat) n (Env.cons (τ := .nat) value Env.empty))) := by
    simp only [EnvFits.cons_buffer_iff, EnvFits.cons_nat_iff, EnvFits.empty,
      outFits, nFits, valueFits, and_self]
  cases execution with
  | seqNormal called assigned =>
      have actualCall := called
      cases called with
      | @callReturn _ _ _ _ _ _ calleeFinish returned _ _ callee continuation =>
          cases returned
          cases continuation with
          | skip =>
              apply ArenaReady.seqNormal (head := actualCall) (tail := assigned)
                (middleCursor := cursor)
                (.callReturn (callee := callee) (fun {τ} => arguments (τ := τ))
                  (work_ready out n value heap hw outRooted outFits nFits valueFits capacity callee)
                  (.skip _))
              refine RealizationWP.arenaReady
                (normal := fun _ => True) (returned := fun _ _ => True) ?_ assigned limit cursor
              ram_source_realize_step
              all_goals omega
  | seqReturn called =>
      cases called with
      | callReturn callee continuation => cases continuation
  | seqFault called => exact False.elim successful

/-- Every finite source loop reuses the same scratch capacity. The original
mathematical invariant and body contract supply preservation; the additional
proof checks only ranges and one level of actual callee nesting. -/
theorem loop_ready {w limit cursor : Nat} (hw : 0 < w)
    (remaining : Nat) (out : Buffer .nat) (count n value : Nat) (heap : Heap)
    {finish : State _}
    {control : Control (.buffer .nat)}
    (current : invariant out count n value remaining heap)
    (countFits : count < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.make_loop1.Code
      ⟨Implementation.Source.make_loop1.View.symm
        (Implementation.Source.make_loop1.entry (remaining, out, count, n, value, ())), heap⟩
      finish control) (successful : ControlFits w control) :
    ArenaReady execution w limit 1 cursor cursor := by
  ram_source_loop_arena
    (stateRel := fun left locals heap => locals = (left, out, count, n, value, ()) ∧
      invariant out count n value left heap)
    (prepared := fun left _ heap locals finish =>
      locals = (left, out, count, n, value, ()) ∧ finish = heap ∧ 0 < left)
    (completed := fun returned _ finish =>
      returned = out ∧ out.Contents finish (resultContents count n value))
  · intro left
    refine (guard_eval left out count n value).mono (fun _ _ valid => valid.1)
      (fun _ _ _ _ _ impossible => impossible) ?_
    rintro _ heap again _ _ _ ⟨sameDecision, sameLocals, sameHeap⟩ active
    exact ⟨sameLocals, sameHeap, of_decide_eq_true (sameDecision.symm.trans active)⟩
  · rintro left _ heap ⟨rfl, valid⟩ _ _ ⟨rfl, rfl, active⟩
    refine (Implementation.Source.make_loop1.body_completion_spec_at
      (body_spec out count n value valid active) (left, out, count, n, value, ()) _).mono ?_
        (Std.Do.PostCond.entails.refl _)
    rintro _ rfl
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · rintro _ finish ⟨rfl, updated⟩
      exact ⟨left - 1, rfl, updated⟩
    · rintro returned locals finish ⟨rfl, _, contents⟩
      exact ⟨rfl, contents⟩
  · rintro left _ heap ⟨rfl, valid⟩ finish decision tested
    exact guard_ready hw left out count n value heap
      (lt_of_le_of_lt valid.1 countFits) tested
  · rintro left _ heap ⟨rfl, valid⟩ _ _ ⟨rfl, rfl, _⟩ finish outcome iterated fits
    have length : out.length = 1 := by simpa using valid.2.size_eq.symm
    exact body_ready hw left out count n value _ valid.2.valid.rooted
      (by rw [length]; exact Nat.one_lt_two_pow (Nat.ne_of_gt hw))
      (lt_of_le_of_lt valid.1 countFits) nFits valueFits capacity iterated fits
  · rintro state returned stopped ⟨rfl, contents⟩ finish decision tested
    have length : returned.length = 1 := by simpa [resultContents] using contents.size_eq.symm
    exact completed_guard_ready hw state returned
      (by rw [length]; exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)) stopped tested
  · exact ⟨rfl, current⟩
  · exact successful

/-- The generated maker's ordinary arguments, in the source function table's
parameter order. This is an environment encoding, not another implementation. -/
def makeArgs (count n value : Nat) : Env [.nat, .nat, .nat] :=
  Env.cons count (Env.cons n (Env.cons value Env.empty))

/-- The complete maker retains only its one result cell. Its loop contract
tracks both ordinary completion and the actual last-round local return;
temporary capacity is independent of `count`. -/
theorem make_ready {w limit cursor : Nat} (hw : 0 < w)
    (count n value : Nat) (heap : Heap)
    {finish : State [.nat, .nat, .nat]} {out : Buffer .nat}
    (countFits : count < 2 ^ w) (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 1 + 2 * n ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.makeBody
      ⟨makeArgs count n value, heap⟩ finish (.returned out)) :
    ArenaReady execution w limit 1 cursor (cursor + 1) := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have contents := make_total.postcondition (args := makeArgs count n value) trivial execution
  have returnedLength : out.length = 1 := by
    simpa [resultContents] using contents.size_eq.symm
  have returnedFits : ValueFits w (τ := .buffer .nat) out := by
    change out.length < 2 ^ w
    rw [returnedLength]
    exact oneFits
  have initialized : (heap.alloc (τ := .nat) 1 0).1.Contents
      (heap.alloc (τ := .nat) 1 0).2 #[0] := by
    simpa using heap.alloc_contents (τ := .nat) 1 0
  have initial := invariant_initial (heap.alloc (τ := .nat) 1 0).1
    count n value initialized
  cases execution with
  | letPrim body =>
      apply ArenaReady.letPrim (body := body) trivial
      cases body with
      | seqNormal completed continuation =>
          apply ArenaReady.seqNormal (head := completed) (tail := continuation)
            (middleCursor := cursor + 1)
          · cases completed with
            | alloc continuation =>
                apply ArenaReady.alloc (body := continuation) (Nat.two_pow_pos w)
                  (by change cursor + 1 ≤ limit; omega)
                cases continuation with
                | letPrim sequence =>
                    apply ArenaReady.letPrim (body := sequence) countFits
                    cases sequence with
                    | @seqNormal _ _ _ _ _ middle _ _ loop continued =>
                        apply ArenaReady.seqNormal (head := loop) (tail := continued)
                          (middleCursor := cursor + 1)
                          (loop_ready hw count (heap.alloc (τ := .nat) 1 0).1 count n value
                            (heap.alloc (τ := .nat) 1 0).2 initial
                            countFits nFits valueFits capacity loop trivial)
                        have property := Stmt.BlockSpec.post_of_exec
                          Implementation.Source.make_loop1.View Implementation.Source.make_loop1.entry
                          (loop_spec (heap.alloc (τ := .nat) 1 0).1 count n value count)
                          ⟨rfl, initial⟩ loop
                        have ranges :
                            ValueFits w (τ := .buffer .nat)
                              (Implementation.Source.make_loop1.visible
                                (Implementation.Source.make_loop1.View middle.locals)).2.1 ∧
                            ValueFits w (τ := .option (.buffer .nat))
                              (Implementation.Source.make_loop1.pending
                                (Implementation.Source.make_loop1.View middle.locals)) := by
                          cases completion : Implementation.Source.make_loop1.pending
                              (Implementation.Source.make_loop1.View middle.locals) with
                          | none =>
                              simp only [completion] at property
                              obtain ⟨left, same, _⟩ := property
                              constructor
                              · rw [same]
                                exact oneFits
                              · trivial
                          | some result =>
                              simp only [completion] at property
                              obtain ⟨rfl, same, _⟩ := property
                              constructor
                              · rw [same]
                                exact oneFits
                              · exact ⟨oneFits, oneFits⟩
                        rcases ranges with ⟨visibleFits, pendingFits⟩
                        dsimp only [Implementation.Source.make_loop1.visible,
                          Implementation.Source.make_loop1.pending,
                          Implementation.Source.make_loop1.view_apply] at visibleFits pendingFits
                        refine RealizationWP.arenaReady
                          (normal := fun _ => True) (returned := fun _ _ => True)
                          ?_ continued limit (cursor + 1)
                        ram_source_realize_step
                        all_goals simp_all only [ValueFits]
                        all_goals first | omega | trivial
          · cases continuation with
            | matchNone selected skipped => cases skipped
            | matchSome selected returned =>
                cases returned
                apply ArenaReady.matchSome (selected := selected)
                  (body := Exec.ret _ _) returnedFits
                exact .ret _ _ returnedFits
      | seqReturn completed =>
          exact False.elim (completed.not_returned (by
            simp only [Stmt.NoReturn, Implementation.Source.make_loop1.noReturn,
              Stmt.LocalReturn.resume, Stmt.LocalReturn.store, and_self]) _ rfl)

/-- A sufficient physical workspace envelope: the retained entry arena, one
result word, two simultaneously live scratch arrays, and two actual call frames.
The frame size is derived from the fixed generated program, not from `count`. -/
def workspaceWords (entryCursor n : Nat) : Nat :=
  heapLimit entryCursor n + 2 * Ram.ABI.frameSize (programControl Implementation.Source.program)

set_option maxRecDepth 2048 in
/-- The same high-level declaration returns its mathematical array in the real
halted RAM invocation. Every actual memory access, and therefore every distinct
word touched, stays within a workspace bound independent of the iteration count.
The shared launch carries the same preloaded representation, scalar ranges and
word/code capacity. The result retains actual RAM memory, returned fields and
counted execution; input loading and output conversion remain outside it. -/
theorem make_runUntil {w cursor : Nat} (count n value : Nat) {heap : Heap}
    {entry : Ram.Source.State w} {placement : Nat → Ram.Word w}
    (launch : FunctionArenaLaunch Implementation.Source.program Implementation.Source.makeId 1
      (heapLimit cursor n) placement (makeArgs count n value) heap cursor entry) :
    ∃ outcome : FunctionArenaExecution Implementation.Source.program Implementation.Source.makeId 1
        (heapLimit cursor n) placement (makeArgs count n value) heap entry,
      outcome.value.Contents outcome.heap (resultContents count n value) ∧
      outcome.cursor = cursor + 1 ∧
      (∀ address ∈ outcome.heapAccesses, address.toNat < workspaceWords cursor n) ∧
      outcome.heapAccesses.card ≤ workspaceWords cursor n := by
  have countFits : count < 2 ^ w := launch.arguments .here
  have nFits : n < 2 ^ w := launch.arguments (.there .here)
  have valueFits : value < 2 ^ w := launch.arguments (.there (.there .here))
  obtain ⟨finish, out, execution, contents⟩ :=
    make_total (makeArgs count n value) heap trivial
  have ready := make_ready launch.toFunctionCapacity.positive count n value heap
    countFits nFits valueFits
    (limit := heapLimit cursor n) (cursor := cursor) (Nat.le_refl _) execution
  obtain ⟨outcome, resultEq, heapEq, cursorEq⟩ := ready.execute launch
  refine ⟨outcome, ?_, cursorEq, ?_, ?_⟩
  · simpa only [resultEq, heapEq] using contents
  · intro address member
    exact outcome.heapAccesses_below member
  · exact outcome.heapAccesses_card_le

end Complexity.Language.Examples.Scope
