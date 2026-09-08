/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic

/-!
# Independent finite source execution

`Exec` relates a typed statement, its initial and final lexical environments,
and its control outcome. It does not refer to a lowering, machine state, clock
or proposed time bound. Recursive calls execute the selected source body; the
inductive relation describes only finite executions, not assumed termination.

Returns and faults bypass later statements. Leaving a lexical binding removes
only that binding from the final environment. Calls evaluate their atomic
arguments in the caller, run a real body in an independent callee environment,
then bind the actual returned value in the caller's continuation. A body that
falls through faults at this function boundary, including a Unit-returning body:
Unit must be returned explicitly and is not a default for a missing return.

The scalar fragment has no shared heap or mutable locals. Callee-environment
restoration is a lexical operation, not a claim about future shared effects.
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

/-- Finite execution of the source syntax itself. The environment of each
statement is separate from its control outcome; scoped and call bindings are
removed on exit without swallowing returns or faults. -/
inductive Exec {signatures : List Signature} (program : Program signatures) :
    {Γ : List Ty} → {result : Ty} → Stmt signatures Γ result →
      Env Γ → Env Γ → Control result → Prop where
  | skip {Γ : List Ty} {result : Ty} (entry : Env Γ) :
      Exec program (.skip : Stmt signatures Γ result) entry entry .normal
  | letPrim {Γ : List Ty} {τ result : Ty} {value : Prim Γ τ}
      {continuation : Stmt signatures (τ :: Γ) result}
      {entry : Env Γ} {finish : Env (τ :: Γ)} {control : Control result}
      (body : Exec program continuation (Env.cons (value.eval entry) entry) finish control) :
      Exec program (.letPrim value continuation) entry finish.tail control
  | seqNormal {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry middle finish : Env Γ} {control : Control result}
      (head : Exec program first entry middle .normal)
      (tail : Exec program second middle finish control) :
      Exec program (.seq first second) entry finish control
  | seqReturn {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : Env Γ} {value : Value result}
      (head : Exec program first entry finish (.returned value)) :
      Exec program (.seq first second) entry finish (.returned value)
  | seqFault {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : Env Γ} {error : Fault}
      (head : Exec program first entry finish (.fault error)) :
      Exec program (.seq first second) entry finish (.fault error)
  | iteTrue {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : Env Γ} {control : Control result}
      (test : condition.eval entry = true)
      (body : Exec program yes entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | iteFalse {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : Env Γ} {control : Control result}
      (test : condition.eval entry = false)
      (body : Exec program no entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | ret {Γ : List Ty} {result : Ty} (value : Atom Γ result) (entry : Env Γ) :
      Exec program (.ret value) entry entry (.returned (value.eval entry))
  | callReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Env Γ} {calleeFinish : Env signatures[fn].params}
      {value : Value signatures[fn].result} {finish : Env (signatures[fn].result :: Γ)}
      {control : Control result}
      (callee : Exec program (program.body fn) (args.eval entry) calleeFinish (.returned value))
      (body : Exec program continuation (Env.cons value entry) finish control) :
      Exec program (.call fn args continuation) entry finish.tail control
  | callFault {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Env Γ} {calleeFinish : Env signatures[fn].params} {error : Fault}
      (callee : Exec program (program.body fn) (args.eval entry) calleeFinish (.fault error)) :
      Exec program (.call fn args continuation) entry entry (.fault error)
  | callMissingReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Env Γ} {calleeFinish : Env signatures[fn].params}
      (callee : Exec program (program.body fn) (args.eval entry) calleeFinish .normal) :
      Exec program (.call fn args continuation) entry entry (.fault .missingReturn)

namespace Exec

/-- The same source statement and entry environment determine both its final
environment and its finite control outcome, independently of execution proofs. -/
theorem deterministic {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish finish' : Env Γ} {control control' : Control result}
    (first : Exec program stmt entry finish control)
    (second : Exec program stmt entry finish' control') :
    @Eq (Env Γ) finish finish' ∧ control = control' := by
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
          cases Control.returned.inj (ihCallee callee').2
          obtain ⟨rfl, rfl⟩ := ihBody body'
          exact ⟨rfl, rfl⟩
      | callFault callee' => cases (ihCallee callee').2
      | callMissingReturn callee' => cases (ihCallee callee').2
  | callFault callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' =>
          cases Control.fault.inj (ih callee').2
          exact ⟨rfl, rfl⟩
      | callMissingReturn callee' => cases (ih callee').2
  | callMissingReturn callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' => cases (ih callee').2
      | callMissingReturn callee' => exact ⟨rfl, rfl⟩

end Exec

end Complexity.Language
