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

The current statement vocabulary remains scalar and has no heap operations or
assignments. Shared state is nevertheless passed explicitly; restoration is a
lexical operation, not rollback of heap effects.
-/

namespace Complexity.Language

/-- A finite source execution can fault instead of returning a value. -/
inductive Fault where
  | missingReturn
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
  | letPrim {Γ : List Ty} {τ result : Ty} {value : Prim Γ τ}
      {continuation : Stmt signatures (τ :: Γ) result}
      {entry : State Γ} {finish : State (τ :: Γ)} {control : Control result}
      (body : Exec program continuation (State.cons (value.eval entry.locals) entry)
        finish control) :
      Exec program (.letPrim value continuation) entry finish.tail control
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

/-- The current scalar vocabulary has no assignment or heap operation, so
lexical exit restores the entire entry state. This is a property of this
vocabulary, not a rollback rule for calls or faults. -/
theorem state_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) : finish = entry := by
  induction execution with
  | skip => rfl
  | letPrim body ih =>
      simpa only [State.tail_cons] using congrArg State.tail ih
  | seqNormal head tail ihHead ihTail => exact ihTail.trans ihHead
  | seqReturn head ih => exact ih
  | seqFault head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | ret => rfl
  | callReturn callee body ihCallee ihBody =>
      rw [ihBody, State.tail_cons, ihCallee]
      rfl
  | callFault callee ih =>
      rw [ih]
      rfl
  | callMissingReturn callee ih =>
      rw [ih]
      rfl

/-- Current scalar statements preserve their outer lexical values. -/
theorem locals_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) : finish.locals = entry.locals :=
  congrArg State.locals execution.state_eq

/-- Current scalar statements have no shared-heap effects. -/
theorem heap_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) : finish.heap = entry.heap :=
  congrArg State.heap execution.state_eq

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
  | letPrim body ih =>
      cases second with
      | letPrim body' =>
          obtain ⟨rfl, rfl⟩ := ih body'
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
