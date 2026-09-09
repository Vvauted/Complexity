/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.State

/-!
# Independent finite source execution

`Exec` relates a typed statement, its initial and final source states,
and its control outcome. It does not refer to a lowering, machine state, clock
or proposed time bound. Recursive calls execute the selected source body; the
inductive relation describes only finite executions, not assumed termination.

Returns and faults bypass later statements. Leaving a lexical binding removes
only that binding from the final environment. Calls evaluate their atomic
arguments in the caller, run a real body with independent callee locals and the
same shared heap, then bind the actual returned value in the caller's continuation.
Caller-local restoration retains the callee's actual final heap, including on
fault or missing return. A body that
falls through faults at this function boundary, including a Unit-returning body:
Unit must be returned explicitly and is not a default for a missing return.

Reads and writes operate on the current shared heap. A failed operation leaves
its entry state unchanged, without rolling back earlier effects. Slices check
their relative extent and bind another view of the same object, not a snapshot.
Assignment evaluates its right-hand side in the current locals once, then updates
the selected local without changing the heap. Scope exit preserves assignments
to outer locals; caller restoration is lexical, not heap rollback.
-/

namespace Complexity.Language

/-- A finite source execution can fault instead of returning a value. -/
inductive Fault where
  | missingReturn
  | heap (error : Heap.Error)
  deriving DecidableEq, Repr

/-- Statement continuation, function return and failure are distinct outcomes. -/
inductive Control (result : Ty) where
  | normal
  | returned : Value result → Control result
  | fault : Fault → Control result

/-- Finite execution of the source syntax itself. The state of each
statement is separate from its control outcome; scoped and call bindings are
removed on exit without swallowing returns or faults. -/
inductive Exec {signatures : List Signature} (program : Program signatures) :
    {Γ : List Ty} → {result : Ty} → Stmt signatures Γ result →
      State Γ → State Γ → Control result → Prop where
  | skip {Γ : List Ty} {result : Ty} (entry : State Γ) :
      Exec program (.skip : Stmt signatures Γ result) entry entry .normal
  | assign {Γ : List Ty} {τ result : Ty} (target : Var Γ τ) (value : Prim Γ τ)
      (entry : State Γ) :
      Exec program (.assign target value : Stmt signatures Γ result) entry
        (entry.set target (value.eval entry.locals)) .normal
  | letPrim {Γ : List Ty} {τ result : Ty} {value : Prim Γ τ}
      {continuation : Stmt signatures (τ :: Γ) result}
      {entry : State Γ} {finish : State (τ :: Γ)} {control : Control result}
      (body : Exec program continuation (State.cons (value.eval entry.locals) entry)
        finish control) :
      Exec program (.letPrim value continuation) entry finish.tail control
  | read {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Stmt signatures (kind.toTy :: Γ) result}
      {entry : State Γ} {finish : State (kind.toTy :: Γ)} {control : Control result}
      {value : CellValue kind}
      (loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value)
      (body : Exec program continuation (State.cons (kind.toValue value) entry) finish control) :
      Exec program (.read buffer index continuation) entry finish.tail control
  | readFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Stmt signatures (kind.toTy :: Γ) result}
      {entry : State Γ} {error : Heap.Error}
      (failed : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .error error) :
      Exec program (.read buffer index continuation) entry entry (.fault (.heap error))
  | write {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : State Γ} {heap : Heap}
      (written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap) :
      Exec program (.write buffer index value : Stmt signatures Γ result)
        entry ⟨entry.locals, heap⟩ .normal
  | writeFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : State Γ} {error : Heap.Error}
      (failed : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .error error) :
      Exec program (.write buffer index value : Stmt signatures Γ result)
        entry entry (.fault (.heap error))
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Stmt signatures (.buffer kind :: Γ) result}
      {entry : State Γ} {finish : State (.buffer kind :: Γ)} {control : Control result}
      {view : Buffer kind}
      (sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view)
      (body : Exec program continuation (State.cons view entry) finish control) :
      Exec program (.slice buffer offset length continuation) entry finish.tail control
  | sliceFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Stmt signatures (.buffer kind :: Γ) result}
      {entry : State Γ} {error : Heap.Error}
      (failed : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .error error) :
      Exec program (.slice buffer offset length continuation) entry entry (.fault (.heap error))
  | seqNormal {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry middle finish : State Γ} {control : Control result}
      (head : Exec program first entry middle .normal)
      (tail : Exec program second middle finish control) :
      Exec program (.seq first second) entry finish control
  | seqReturn {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : State Γ} {value : Value result}
      (head : Exec program first entry finish (.returned value)) :
      Exec program (.seq first second) entry finish (.returned value)
  | seqFault {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : State Γ} {error : Fault}
      (head : Exec program first entry finish (.fault error)) :
      Exec program (.seq first second) entry finish (.fault error)
  | iteTrue {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : State Γ} {control : Control result}
      (test : condition.eval entry.locals = true)
      (body : Exec program yes entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | iteFalse {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : State Γ} {control : Control result}
      (test : condition.eval entry.locals = false)
      (body : Exec program no entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | ret {Γ : List Ty} {result : Ty} (value : Atom Γ result) (entry : State Γ) :
      Exec program (.ret value) entry entry (.returned (value.eval entry.locals))
  | callReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params}
      {value : Value signatures[fn].result} {finish : State (signatures[fn].result :: Γ)}
      {control : Control result}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish (.returned value))
      (body : Exec program continuation (State.cons value (entry.restore calleeFinish))
        finish control) :
      Exec program (.call fn args continuation) entry finish.tail control
  | callFault {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params} {error : Fault}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish (.fault error)) :
      Exec program (.call fn args continuation) entry (entry.restore calleeFinish) (.fault error)
  | callMissingReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish .normal) :
      Exec program (.call fn args continuation) entry (entry.restore calleeFinish)
        (.fault .missingReturn)

namespace Exec

/-- Statements with no local writes preserve their enclosing environment even
when the shared heap changes. Callee-local assignment is allowed: calls restore
the caller's locals before executing its continuation. -/
theorem locals_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) (unchanged : stmt.NoLocalWrites) :
    finish.locals = entry.locals := by
  revert unchanged
  induction execution with
  | skip => intro _; rfl
  | assign => intro impossible; exact False.elim impossible
  | letPrim body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | read loaded body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | readFault => intro _; rfl
  | write => intro _; rfl
  | writeFault => intro _; rfl
  | slice sliced body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | sliceFault => intro _; rfl
  | seqNormal head tail ihHead ihTail =>
      intro unchanged
      exact (ihTail unchanged.2).trans (ihHead unchanged.1)
  | seqReturn head ih => intro unchanged; exact ih unchanged.1
  | seqFault head ih => intro unchanged; exact ih unchanged.1
  | iteTrue test body ih => intro unchanged; exact ih unchanged.1
  | iteFalse test body ih => intro unchanged; exact ih unchanged.2
  | ret => intro _; rfl
  | callReturn callee body ihCallee ihBody =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons, State.locals_restore] using
        congrArg Env.tail (ihBody unchanged)
  | callFault => intro _; rfl
  | callMissingReturn => intro _; rfl

/-- The same source statement and entry state determine both its final state
and its finite control outcome, independently of execution proofs. -/
theorem deterministic {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish finish' : State Γ} {control control' : Control result}
    (first : Exec program stmt entry finish control)
    (second : Exec program stmt entry finish' control') :
    finish = finish' ∧ control = control' := by
  induction first with
  | skip =>
      cases second
      exact ⟨rfl, rfl⟩
  | assign =>
      cases second
      exact ⟨rfl, rfl⟩
  | letPrim body ih =>
      cases second with
      | letPrim body' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | read loaded body ih =>
      cases second with
      | read loaded' body' =>
          cases Except.ok.inj (loaded.symm.trans loaded')
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | readFault failed => cases loaded.symm.trans failed
  | readFault failed =>
      cases second with
      | read loaded body => cases failed.symm.trans loaded
      | readFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | write written =>
      cases second with
      | write written' =>
          cases Except.ok.inj (written.symm.trans written')
          exact ⟨rfl, rfl⟩
      | writeFault failed => cases written.symm.trans failed
  | writeFault failed =>
      cases second with
      | write written => cases failed.symm.trans written
      | writeFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | slice sliced body ih =>
      cases second with
      | slice sliced' body' =>
          cases Except.ok.inj (sliced.symm.trans sliced')
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | sliceFault failed => cases sliced.symm.trans failed
  | sliceFault failed =>
      cases second with
      | slice sliced body => cases failed.symm.trans sliced
      | sliceFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | seqNormal head tail ihHead ihTail =>
      cases second with
      | seqNormal head' tail' =>
          obtain ⟨rfl, _⟩ := ihHead head'
          exact ihTail tail'
      | seqReturn head' => cases (ihHead head').2
      | seqFault head' => cases (ihHead head').2
  | seqReturn head ih =>
      cases second with
      | seqNormal head' tail' => cases (ih head').2
      | seqReturn head' => exact ih head'
      | seqFault head' => cases (ih head').2
  | seqFault head ih =>
      cases second with
      | seqNormal head' tail' => cases (ih head').2
      | seqReturn head' => cases (ih head').2
      | seqFault head' => exact ih head'
  | iteTrue test body ih =>
      cases second with
      | iteTrue test' body' => exact ih body'
      | iteFalse test' body' => simp_all
  | iteFalse test body ih =>
      cases second with
      | iteTrue test' body' => simp_all
      | iteFalse test' body' => exact ih body'
  | ret =>
      cases second
      exact ⟨rfl, rfl⟩
  | callReturn callee body ihCallee ihBody =>
      cases second with
      | callReturn callee' body' =>
          obtain ⟨rfl, sameControl⟩ := ihCallee callee'
          cases Control.returned.inj sameControl
          obtain ⟨rfl, rfl⟩ := ihBody body'
          exact ⟨rfl, rfl⟩
      | callFault callee' => cases (ihCallee callee').2
      | callMissingReturn callee' => cases (ihCallee callee').2
  | callFault callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' =>
          obtain ⟨rfl, sameControl⟩ := ih callee'
          cases Control.fault.inj sameControl
          exact ⟨rfl, rfl⟩
      | callMissingReturn callee' => cases (ih callee').2
  | callMissingReturn callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' => cases (ih callee').2
      | callMissingReturn callee' =>
          obtain ⟨rfl, _⟩ := ih callee'
          exact ⟨rfl, rfl⟩

end Exec

end Complexity.Language
