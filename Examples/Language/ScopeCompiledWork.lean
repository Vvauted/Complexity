/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Scope
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization

/-!
# Resource readiness of the actual scratch worker

The source correctness proof supplies the worker's successful execution. This
module adds only word ranges and temporary capacity for that same execution;
it neither repeats termination nor supplies a separately maintained program.
Both nested scopes restore their respective entry cursors. Consequently the
worker's temporary capacity depends on the two simultaneous arrays, not on the
number of later calls to the worker.
-/

namespace Complexity.Language.Examples.Scope

open Ram.LanguageCompiler

/-- A successful inner scratch block needs exactly one temporary extent and
returns the allocator to its entry cursor. The complete local coordinates keep
all pending results; their values do not affect the allocation-only body. -/
theorem inner_ready (locals : Implementation.Source.work_scope2.Locals) (heap : Heap)
    {w limit depth cursor : Nat}
    {finish : State _}
    {control : Control .unit}
    (capacity : cursor + (Implementation.Source.work_scope2.visible locals).2.2.1 ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.work_scope2.Code
      ⟨Implementation.Source.work_scope2.View.symm locals, heap⟩
      finish control)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ArenaReady execution w limit depth cursor cursor := by
  apply ArenaReady.scope_of_exec execution successful
  intro after outcome body success
  cases body with
  | alloc body =>
      cases body with
      | skip =>
          exact ⟨_, .alloc (Nat.two_pow_pos w) capacity (.skip _)⟩

private theorem inner_exec (locals : Implementation.Source.work_scope2.Locals) (heap : Heap)
    (rooted : (Implementation.Source.work_scope2.View.symm locals).Rooted heap) :
    Exec Implementation.Source.program Implementation.Source.work_scope2.Code
      ⟨Implementation.Source.work_scope2.View.symm locals, heap⟩
      ⟨Implementation.Source.work_scope2.View.symm locals, heap⟩ .normal := by
  have body : Exec Implementation.Source.program Implementation.Source.work_scope2.Body
      ⟨Implementation.Source.work_scope2.View.symm locals, heap⟩
      ⟨Implementation.Source.work_scope2.View.symm locals,
        (heap.alloc (τ := .nat) (Implementation.Source.work_scope2.visible locals).2.2.1 0).2⟩
      .normal := .alloc (.skip _)
  have safe : ScopeSafe heap
      ⟨Implementation.Source.work_scope2.View.symm locals,
        (heap.alloc (τ := .nat) (Implementation.Source.work_scope2.visible locals).2.2.1 0).2⟩
      (.normal : Control .unit) := ⟨rooted, trivial⟩
  simpa only [Heap.take_alloc_self] using Exec.scope body safe

private theorem outer_ready (out : Buffer .nat) (n value : Nat) (heap : Heap)
    {w limit depth cursor : Nat} (hw : 0 < w)
    {finish : State _} {control : Control .unit}
    (outRooted : out.Rooted heap) (outFits : out.length < 2 ^ w)
    (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.work_scope1.Code
      ⟨Implementation.Source.work_scope1.View.symm
        (Implementation.Source.work_scope1.entry (out, n, value, ())), heap⟩
      finish control)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ArenaReady execution w limit depth cursor cursor := by
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have outerCapacity : cursor + n ≤ limit := by omega
  have innerCapacity : cursor + n + n ≤ limit := by omega
  have nested := inner_exec
    (Implementation.Source.work_scope2.entry ((heap.alloc (τ := .nat) n value).1,
      out, n, value, ())) (heap.alloc (τ := .nat) n value).2 (by
        simp only [Implementation.Source.work_scope2.entry,
          Implementation.Source.work_scope2.view_symm_apply,
          Env.Rooted.cons_iff, Env.Rooted.empty, ValueRooted,
          heap.alloc_rooted (τ := .nat) n value, outRooted.alloc (τ := .nat) n value,
          and_self])
  apply ArenaReady.scope_of_exec execution successful
  intro after outcome outer successful
  cases outer with
  | alloc continuation =>
      refine ⟨cursor + n, .alloc (body := continuation) valueFits outerCapacity ?_⟩
      cases continuation with
      | seqNormal inner rest =>
          have innerExecution := inner
          cases inner with
          | letPrim scopedCommit =>
              have scopedCommitExecution := scopedCommit
              cases scopedCommit with
              | seqNormal scopedExecution commit =>
                  have commitExecution := commit
                  obtain ⟨same, _⟩ := scopedExecution.deterministic nested
                  cases same
                  cases commit with
                  | matchNone selected skipped =>
                      cases skipped
                      have innerReady : ArenaReady innerExecution w limit depth
                          (cursor + n) (cursor + n) := by
                        apply ArenaReady.letPrim (body := scopedCommitExecution) trivial
                        apply ArenaReady.seqNormal (head := scopedExecution)
                          (tail := commitExecution) (middleCursor := cursor + n)
                        · exact inner_ready
                            (Implementation.Source.work_scope2.entry
                              ((heap.alloc (τ := .nat) n value).1, out, n, value, ()))
                            (heap.alloc (τ := .nat) n value).2
                            innerCapacity scopedExecution (by trivial)
                        · exact .matchNone (selected := selected) (.skip _)
                      apply ArenaReady.seqNormal (head := innerExecution) (tail := rest)
                        (middleCursor := cursor + n) innerReady
                      cases rest with
                      | matchNone selected branch =>
                          apply ArenaReady.matchNone (selected := selected) (body := branch)
                          cases branch with
                          | letPrim conditional =>
                              apply ArenaReady.letPrim (body := conditional) ⟨zeroFits, nFits⟩
                              cases conditional with
                              | iteTrue test reading =>
                                  apply ArenaReady.iteTrue (test := test) (body := reading)
                                  cases reading with
                                  | @read _ _ _ _ _ _ _ _ _ readValue loaded tail =>
                                      have nonempty : 0 < n := of_decide_eq_true test
                                      have loadedValue : readValue = value :=
                                        Except.ok.inj (loaded.symm.trans
                                          (heap.read_alloc (τ := .nat) value nonempty))
                                      subst readValue
                                      apply ArenaReady.read (loaded := loaded) (body := tail)
                                        nFits zeroFits valueFits
                                      cases tail with
                                      | seqNormal writing returned =>
                                          cases writing with
                                          | write written =>
                                              apply ArenaReady.seqNormal (tail := returned)
                                                (middleCursor := cursor + n)
                                                (.write (written := written)
                                                  outFits zeroFits valueFits)
                                              cases returned with
                                              | matchNone selected stored =>
                                                  apply ArenaReady.matchNone
                                                    (selected := selected) (body := stored)
                                                  cases stored
                                                  refine .assign _ _ _ ?_
                                                  exact ⟨oneFits, trivial⟩
                                              | matchSome selected stopped => cases selected
                                      | seqReturn writing => cases writing
                                      | seqFault writing => exact False.elim successful
                                  | readFault failed => exact False.elim successful
                              | iteFalse test stored =>
                                  apply ArenaReady.iteFalse (test := test) (body := stored)
                                  cases stored
                                  refine .assign _ _ _ ?_
                                  exact ⟨oneFits, trivial⟩
                      | matchSome selected stopped => cases selected
                  | matchSome selected stored => cases selected
      | seqReturn inner =>
          exact False.elim (inner.not_returned (by
            simp only [Stmt.NoReturn, Implementation.Source.work_scope2.noReturn,
              Stmt.LocalReturn.store, and_self]) _ rfl)
      | seqFault inner => exact False.elim successful

/-- The actual worker can be invoked at any available call depth. Its two
simultaneous temporary arrays fit in `2 * n` words, and both scopes have released
that space before the call returns. The positive word width also represents the
local completion tag; no instruction or termination budget enters the premise. -/
theorem work_ready (out : Buffer .nat) (n value : Nat) (heap : Heap)
    {w limit depth cursor : Nat} (hw : 0 < w)
    {finish : State [.buffer .nat, .nat, .nat]}
    (outRooted : out.Rooted heap) (outFits : out.length < 2 ^ w)
    (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.Source.program Implementation.Source.workBody
      ⟨Implementation.Source.work_args out n value, heap⟩ finish (.returned ())) :
    ArenaReady execution w limit depth cursor cursor := by
  have oneFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  cases execution with
  | letPrim body =>
      apply ArenaReady.letPrim (body := body) trivial
      cases body with
      | seqNormal completed continuation =>
          have completedExecution := completed
          cases completed with
          | letPrim scopedCommit =>
              have scopedCommitExecution := scopedCommit
              cases scopedCommit with
              | seqNormal scopedExecution commit =>
                  apply ArenaReady.seqNormal (head := completedExecution)
                    (tail := continuation) (middleCursor := cursor)
                  · apply ArenaReady.letPrim (body := scopedCommitExecution) trivial
                    apply ArenaReady.seqNormal (head := scopedExecution) (tail := commit)
                      (middleCursor := cursor)
                      (outer_ready out n value heap hw outRooted outFits nFits valueFits
                        capacity scopedExecution (by trivial))
                    cases commit with
                    | matchNone selected skipped =>
                        apply ArenaReady.matchNone (selected := selected) (body := skipped)
                        cases skipped
                        exact .skip _
                    | matchSome selected stored =>
                        apply ArenaReady.matchSome (selected := selected) (body := stored) trivial
                        cases stored
                        refine .assign _ _ _ ?_
                        exact ⟨oneFits, trivial⟩
                  · cases continuation with
                    | matchNone selected skipped => cases skipped
                    | matchSome selected returned =>
                        apply ArenaReady.matchSome (selected := selected) (body := returned) trivial
                        cases returned
                        refine .ret _ _ ?_
                        trivial
      | seqReturn completed =>
          exact False.elim (completed.not_returned (by
            simp only [Stmt.NoReturn, Implementation.Source.work_scope1.noReturn,
              Stmt.LocalReturn.store, and_self]) _ rfl)

end Complexity.Language.Examples.Scope
