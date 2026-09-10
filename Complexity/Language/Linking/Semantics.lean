/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Basic
import Complexity.Language.Verification

/-!
# Execution and verification through typed program embeddings

Relocating a function table preserves the actual source states and control
outcomes. In particular, a recursive call uses the relocated body, and a fault
retains every heap effect preceding it. The proof uses the existing finite
execution relation, without a machine backend or an assumed termination bound.
-/

namespace Complexity.Language

namespace Exec

/-- The ordinary returning-call rule through an equality of complete signatures. -/
theorem callReturnOfEq {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature) {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Stmt signatures (signature.result :: Γ) result}
    {entry : State Γ} {calleeFinish : State signature.params}
    {value : Value signature.result} {finish : State (signature.result :: Γ)}
    {control : Control result}
    (callee : Exec program
      (Eq.mp (congrArg (fun s => Stmt signatures s.params s.result) same) (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value))
    (body : Exec program continuation (State.cons value (entry.restore calleeFinish))
      finish control) :
    Exec program (Stmt.callOfEq fn same args continuation) entry finish.tail control := by
  cases same
  exact .callReturn callee body

/-- A transported call retains the actual callee heap when the callee faults. -/
theorem callFaultOfEq {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature) {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Stmt signatures (signature.result :: Γ) result}
    {entry : State Γ} {calleeFinish : State signature.params} {error : Fault}
    (callee : Exec program
      (Eq.mp (congrArg (fun s => Stmt signatures s.params s.result) same) (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.fault error)) :
    Exec program (Stmt.callOfEq fn same args continuation) entry
      (entry.restore calleeFinish) (.fault error) := by
  cases same
  exact .callFault callee

/-- Falling through a transported callee still produces a missing-return fault. -/
theorem callMissingReturnOfEq {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature) {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Stmt signatures (signature.result :: Γ) result}
    {entry : State Γ} {calleeFinish : State signature.params}
    (callee : Exec program
      (Eq.mp (congrArg (fun s => Stmt signatures s.params s.result) same) (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish .normal) :
    Exec program (Stmt.callOfEq fn same args continuation) entry
      (entry.restore calleeFinish) (.fault .missingReturn) := by
  cases same
  exact .callMissingReturn callee

/-- A checked function-table embedding preserves every finite execution,
including normal fallthrough, early return and failure after heap effects. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Stmt source Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec sourceProgram statement entry finish control) :
    Exec targetProgram (statement.renameCalls map) entry finish control := by
  induction execution with
  | skip => exact .skip _
  | assign => exact .assign _ _ _
  | letPrim _ ih => exact .letPrim ih
  | alloc _ ih => exact .alloc ih
  | scope _ safe ih => exact .scope ih safe
  | scopeEscape _ escapes ih => exact .scopeEscape ih escapes
  | read loaded _ ih => exact .read loaded ih
  | readFault failed => exact .readFault failed
  | write written => exact .write written
  | writeFault failed => exact .writeFault failed
  | slice sliced _ ih => exact .slice sliced ih
  | sliceFault failed => exact .sliceFault failed
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | seqFault _ ih => exact .seqFault ih
  | iteTrue test _ ih => exact .iteTrue test ih
  | iteFalse test _ ih => exact .iteFalse test ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | whileFault _ _ ihGuard ihBody => exact .whileFault ihGuard ihBody
  | whileGuardFault _ ih => exact .whileGuardFault ih
  | whileGuardMissingReturn _ ih => exact .whileGuardMissingReturn ih
  | ret => exact .ret _ _
  | @callReturn Γ result fn args continuation entry calleeFinish value finish control
      _ _ ihCallee ihBody =>
      apply callReturnOfEq (map.signature_eq fn) (body := ihBody)
      change Exec targetProgram (map.body targetProgram fn) _ _ _
      rw [embedded fn]
      exact ihCallee
  | @callFault Γ result fn args continuation entry calleeFinish error _ ih =>
      apply callFaultOfEq (map.signature_eq fn)
      change Exec targetProgram (map.body targetProgram fn) _ _ _
      rw [embedded fn]
      exact ih
  | @callMissingReturn Γ result fn args continuation entry calleeFinish _ ih =>
      apply callMissingReturnOfEq (map.signature_eq fn)
      change Exec targetProgram (map.body targetProgram fn) _ _ _
      rw [embedded fn]
      exact ih

end Exec

/-- Source total correctness is reusable after relocation with the same
pre-state and postconditions; it does not require a new termination argument. -/
theorem TotalWP.renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Stmt source Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop}
    {entry : State Γ} (specification : TotalWP sourceProgram statement normal returned entry) :
    TotalWP targetProgram (statement.renameCalls map) normal returned entry := by
  obtain ⟨finish, control, execution, postcondition⟩ := specification
  exact ⟨finish, control, execution.renameCalls embedded, postcondition⟩

end Complexity.Language
