/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Basic

/-!
# Compositional source evaluation

The partial-value semantics of source statements composes through mathlib's
`Part.map` and `Part.bind`. These equations are consequences of the existing
finite source execution relation, not a second interpreter or a lowering.

Sequencing preserves early returns and faults. Lexical bindings are removed on
exit without discarding outer-local or heap changes, and calls bind the actual callee result
in the caller's locals with the callee's final shared heap.
`eval_call` deliberately is not a simplification rule: recursive program bodies
must not be unfolded automatically. Missing returns remain defined faults.
-/

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable (program : Program signatures)

/-- An empty statement continues normally without changing its environment. -/
@[simp] theorem eval_skip (entry : State Γ) :
    (Stmt.skip : Stmt signatures Γ result).eval program entry =
      Part.some (entry, .normal) :=
  (Exec.skip entry).eval_eq_some

/-- Assignment evaluates its actual primitive in the entry environment and
continues with the updated local, retaining the current shared heap. -/
@[simp] theorem eval_assign {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ)
    (entry : State Γ) :
    (Stmt.assign target value : Stmt signatures Γ result).eval program entry =
      Part.some (entry.set target (value.eval entry.locals), .normal) :=
  (Exec.assign target value entry).eval_eq_some

/-- Returning an atom produces its actual source value and stops continuation. -/
@[simp] theorem eval_ret (value : Atom Γ result) (entry : State Γ) :
    (Stmt.ret value).eval program entry =
      Part.some (entry, .returned (value.eval entry.locals)) :=
  (Exec.ret value entry).eval_eq_some

/-- A primitive binding evaluates its scoped body and removes only that binding
from the final environment, preserving the body's control outcome. -/
theorem eval_letPrim {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) (entry : State Γ) :
    (Stmt.letPrim value continuation).eval program entry =
      (continuation.eval program (State.cons (value.eval entry.locals) entry)).map
        (fun outcome => (outcome.1.tail, outcome.2)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | letPrim body =>
        exact Part.mem_map_iff _ |>.mpr ⟨(_, _), mem_eval_iff.mpr body, rfl⟩
  · intro member
    obtain ⟨⟨scopedFinish, scopedControl⟩, body, same⟩ := Part.mem_map_iff _ |>.mp member
    cases same
    exact mem_eval_iff.mpr (.letPrim (mem_eval_iff.mp body))

/-- Reading observes the current shared heap before binding its actual cell.
A finite heap fault skips the scoped continuation and retains that heap. -/
theorem eval_read {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (continuation : Stmt signatures (kind.toTy :: Γ) result) (entry : State Γ) :
    (Stmt.read buffer index continuation).eval program entry =
      match entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) with
      | .ok value =>
          (continuation.eval program (State.cons (kind.toValue value) entry)).map
            (fun outcome => (outcome.1.tail, outcome.2))
      | .error error => Part.some (entry, .fault (.heap error)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | read loaded body =>
        rw [loaded]
        exact Part.mem_map_iff _ |>.mpr ⟨(_, _), mem_eval_iff.mpr body, rfl⟩
    | readFault failed =>
        rw [failed]
        exact Part.mem_some_iff.mpr rfl
  · intro member
    cases loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) with
    | ok value =>
        rw [loaded] at member
        obtain ⟨⟨scopedFinish, scopedControl⟩, body, same⟩ := Part.mem_map_iff _ |>.mp member
        cases same
        exact mem_eval_iff.mpr (.read loaded (mem_eval_iff.mp body))
    | error error =>
        rw [loaded] at member
        cases Part.mem_some_iff.mp member
        exact mem_eval_iff.mpr (.readFault loaded)

/-- A write continues normally at the actual updated heap. Its failure is
finite and preserves the entry state of this operation, not an older snapshot. -/
theorem eval_write {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) (entry : State Γ) :
    (Stmt.write buffer index value : Stmt signatures Γ result).eval program entry =
      match entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
          (kind.ofValue (value.eval entry.locals)) with
      | .ok heap => Part.some (⟨entry.locals, heap⟩, .normal)
      | .error error => Part.some (entry, .fault (.heap error)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | write written =>
        rw [written]
        exact Part.mem_some_iff.mpr rfl
    | writeFault failed =>
        rw [failed]
        exact Part.mem_some_iff.mpr rfl
  · intro member
    cases written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) with
    | ok heap =>
        rw [written] at member
        cases Part.mem_some_iff.mp member
        exact mem_eval_iff.mpr (.write written)
    | error error =>
        rw [written] at member
        cases Part.mem_some_iff.mp member
        exact mem_eval_iff.mpr (.writeFault written)

/-- Slicing binds checked metadata for the same shared object. It performs no
heap read or copy, and a failed relative extent skips its continuation. -/
theorem eval_slice {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) (entry : State Γ) :
    (Stmt.slice buffer offset length continuation).eval program entry =
      match (buffer.eval entry.locals).slice (offset.eval entry.locals) (length.eval entry.locals) with
      | .ok view =>
          (continuation.eval program (State.cons view entry)).map
            (fun outcome => (outcome.1.tail, outcome.2))
      | .error error => Part.some (entry, .fault (.heap error)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | slice sliced body =>
        rw [sliced]
        exact Part.mem_map_iff _ |>.mpr ⟨(_, _), mem_eval_iff.mpr body, rfl⟩
    | sliceFault failed =>
        rw [failed]
        exact Part.mem_some_iff.mpr rfl
  · intro member
    cases sliced : (buffer.eval entry.locals).slice
        (offset.eval entry.locals) (length.eval entry.locals) with
    | ok view =>
        rw [sliced] at member
        obtain ⟨⟨scopedFinish, scopedControl⟩, body, same⟩ := Part.mem_map_iff _ |>.mp member
        cases same
        exact mem_eval_iff.mpr (.slice sliced (mem_eval_iff.mp body))
    | error error =>
        rw [sliced] at member
        cases Part.mem_some_iff.mp member
        exact mem_eval_iff.mpr (.sliceFault sliced)

/-- Only normal continuation executes the second statement. A finite return or
fault from the first statement is retained without evaluating the second. -/
theorem eval_seq (first second : Stmt signatures Γ result) (entry : State Γ) :
    (Stmt.seq first second).eval program entry =
      (first.eval program entry).bind (fun outcome =>
        match outcome.2 with
        | .normal => second.eval program outcome.1
        | .returned value => Part.some (outcome.1, .returned value)
        | .fault error => Part.some (outcome.1, .fault error)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | seqNormal head tail =>
        apply Part.mem_bind_iff.mpr
        refine ⟨(_, .normal), mem_eval_iff.mpr head, ?_⟩
        exact mem_eval_iff.mpr tail
    | seqReturn head =>
        exact Part.mem_bind (mem_eval_iff.mpr head) (Part.mem_some_iff.mpr rfl)
    | seqFault head =>
        exact Part.mem_bind (mem_eval_iff.mpr head) (Part.mem_some_iff.mpr rfl)
  · intro member
    obtain ⟨⟨middle, headControl⟩, headMember, tailMember⟩ := Part.mem_bind_iff.mp member
    have head := mem_eval_iff.mp headMember
    apply mem_eval_iff.mpr
    cases headControl with
    | normal => exact .seqNormal head (mem_eval_iff.mp tailMember)
    | returned value =>
        cases Part.mem_some_iff.mp tailMember
        exact .seqReturn head
    | fault error =>
        cases Part.mem_some_iff.mp tailMember
        exact .seqFault head

/-- A source conditional observes only the branch selected by its actual atom. -/
theorem eval_ite (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result)
    (entry : State Γ) :
    (Stmt.ite condition yes no).eval program entry =
      if condition.eval entry.locals = true then yes.eval program entry else no.eval program entry := by
  apply Part.ext
  intro outcome
  rw [mem_eval_iff]
  by_cases test : condition.eval entry.locals = true
  · rw [if_pos test, mem_eval_iff]
    constructor
    · intro execution
      cases execution with
      | iteTrue _ body => exact body
      | iteFalse falseTest _ =>
          exact False.elim (Bool.noConfusion (test.symm.trans falseTest))
    · exact Exec.iteTrue test
  · rw [if_neg test, mem_eval_iff]
    have falseTest : condition.eval entry.locals = false := by
      cases value : condition.eval entry.locals with
      | false => rfl
      | true => exact False.elim (test value)
    constructor
    · intro execution
      cases execution with
      | iteTrue trueTest _ => exact False.elim (test trueTest)
      | iteFalse _ body => exact body
    · exact Exec.iteFalse falseTest

/-- A call evaluates the selected source function and binds its actual returned
value in the caller's continuation using the callee's actual final heap. Faults,
including missing returns, retain that heap without running the continuation
or exposing the callee's final lexical environment. -/
theorem eval_call (fn : Fin signatures.length) (args : Args Γ signatures[fn].params)
    (continuation : Stmt signatures (signatures[fn].result :: Γ) result) (entry : State Γ) :
    (Stmt.call fn args continuation).eval program entry =
      (program.eval fn (args.eval entry.locals) entry.heap).bind (fun returned =>
        match returned.1 with
        | .ok value =>
            (continuation.eval program (State.cons value ⟨entry.locals, returned.2⟩)).map
              (fun outcome => (outcome.1.tail, outcome.2))
        | .error error => Part.some (⟨entry.locals, returned.2⟩, .fault error)) := by
  apply Part.ext
  rintro ⟨finish, control⟩
  constructor
  · intro member
    cases mem_eval_iff.mp member with
    | callReturn callee body =>
        exact Part.mem_bind (Program.mem_eval_ok_iff.mpr ⟨_, callee, rfl⟩)
          (Part.mem_map_iff _ |>.mpr ⟨(_, _), mem_eval_iff.mpr body, rfl⟩)
    | callFault callee =>
        have fault := Program.eval_eq_error_iff.mpr (Or.inr ⟨_, callee, rfl⟩)
        exact Part.mem_bind (Part.eq_some_iff.mp fault) (Part.mem_some_iff.mpr rfl)
    | callMissingReturn callee =>
        have fault := Program.eval_eq_error_iff.mpr (Or.inl ⟨rfl, _, callee, rfl⟩)
        exact Part.mem_bind (Part.eq_some_iff.mp fault) (Part.mem_some_iff.mpr rfl)
  · intro member
    obtain ⟨⟨returned, finalHeap⟩, calleeMember, bodyMember⟩ := Part.mem_bind_iff.mp member
    apply mem_eval_iff.mpr
    cases returned with
    | ok value =>
        obtain ⟨calleeFinish, callee, rfl⟩ := Program.mem_eval_ok_iff.mp calleeMember
        obtain ⟨⟨scopedFinish, scopedControl⟩, body, same⟩ :=
          Part.mem_map_iff _ |>.mp bodyMember
        cases same
        exact .callReturn callee (mem_eval_iff.mp body)
    | error error =>
        cases Part.mem_some_iff.mp bodyMember
        have fault := Program.eval_eq_error_iff.mp (Part.eq_some_iff.mpr calleeMember)
        rcases fault with ⟨rfl, calleeFinish, callee, rfl⟩ | ⟨calleeFinish, callee, rfl⟩
        · exact .callMissingReturn callee
        · exact .callFault callee

end Complexity.Language.Stmt
