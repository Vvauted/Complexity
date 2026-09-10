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
returns the allocator to its entry cursor. Its mathematical heap behavior is
already described by `inner_eval`. -/
theorem inner_ready (temp out : Buffer .nat) (n value : Nat) (heap : Heap)
    {w limit depth cursor : Nat}
    {finish : State [.buffer .nat, .buffer .nat, .nat, .nat]}
    {control : Control .unit}
    (capacity : cursor + n ≤ limit)
    (execution : Exec Implementation.program Implementation.work_scope2.Code
      ⟨Implementation.work_scope2.View.symm (temp, out, n, value, ()), heap⟩
      finish control)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ArenaReady execution w limit depth cursor cursor := by
  apply ArenaReady.scope_of_exec execution successful
  intro after outcome body success
  cases body with
  | alloc body =>
      cases body with
      | skip =>
          exact ⟨cursor + n, .alloc (Nat.two_pow_pos w) capacity (.skip _)⟩

private theorem inner_exec (temp out : Buffer .nat) (n value : Nat) (heap : Heap)
    (tempRooted : temp.Rooted heap) (outRooted : out.Rooted heap) :
    Exec Implementation.program Implementation.work_scope2.Code
      ⟨Implementation.work_scope2.View.symm (temp, out, n, value, ()), heap⟩
      ⟨Implementation.work_scope2.View.symm (temp, out, n, value, ()), heap⟩ .normal :=
  Stmt.observe_eq_some_iff.mp (inner_eval temp out n value heap tempRooted outRooted)

/-- The actual worker can be invoked at any available call depth. Its two
simultaneous temporary arrays fit in `2 * n` words, and both scopes have released
that space before the call returns. No instruction or termination budget enters
the independently established source execution premise. -/
theorem work_ready (out : Buffer .nat) (n value : Nat) (heap : Heap)
    {w limit depth cursor : Nat}
    {finish : State [.buffer .nat, .nat, .nat]}
    (outRooted : out.Rooted heap) (outFits : out.length < 2 ^ w)
    (nFits : n < 2 ^ w) (valueFits : value < 2 ^ w)
    (capacity : cursor + 2 * n ≤ limit)
    (execution : Exec Implementation.program Implementation.workBody
      ⟨Implementation.work_scope1.View.symm (out, n, value, ()), heap⟩
      finish (.returned ())) :
    ArenaReady execution w limit depth cursor cursor := by
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  have outerCapacity : cursor + n ≤ limit := by omega
  have innerCapacity : cursor + n + n ≤ limit := by omega
  have nested := inner_exec (heap.alloc (τ := .nat) n value).1 out n value
    (heap.alloc (τ := .nat) n value).2
    (heap.alloc_rooted (τ := .nat) n value) (outRooted.alloc (τ := .nat) n value)
  apply ArenaReady.scope_of_exec execution (by trivial)
  intro after outcome outer successful
  cases outer with
  | alloc continuation =>
      refine ⟨cursor + n, .alloc (body := continuation) valueFits outerCapacity ?_⟩
      cases continuation with
      | seqNormal inner rest =>
          obtain ⟨same, _⟩ := inner.deterministic nested
          cases same
          apply ArenaReady.seqNormal (head := inner) (tail := rest)
            (inner_ready _ out n value _ innerCapacity inner (by trivial))
          cases rest with
          | letPrim branch =>
              apply ArenaReady.letPrim (body := branch) ⟨zeroFits, nFits⟩
              cases branch with
              | iteTrue test reading =>
                  apply ArenaReady.iteTrue (test := test) (body := reading)
                  cases reading with
                  | @read _ _ _ _ _ _ _ _ _ readValue loaded tail =>
                      have nonempty : 0 < n := of_decide_eq_true test
                      have loadedValue : readValue = value :=
                        Except.ok.inj
                          (loaded.symm.trans (heap.read_alloc (τ := .nat) value nonempty))
                      subst readValue
                      apply ArenaReady.read (loaded := loaded) (body := tail)
                        nFits zeroFits valueFits
                      cases tail with
                      | seqNormal writing returned =>
                          apply ArenaReady.seqNormal (head := writing) (tail := returned)
                          · cases writing with
                            | write written =>
                                exact .write (written := written) outFits zeroFits valueFits
                          · cases returned
                            exact .ret _ _ trivial
                      | seqReturn writing => cases writing
                      | seqFault writing => exact False.elim successful
                  | readFault failed => exact False.elim successful
              | iteFalse test returned =>
                  apply ArenaReady.iteFalse (test := test) (body := returned)
                  cases returned
                  exact .ret _ _ trivial
      | seqReturn inner =>
          have impossible := (inner.deterministic nested).2
          cases impossible
      | seqFault inner => exact False.elim successful

end Complexity.Language.Examples.Scope
