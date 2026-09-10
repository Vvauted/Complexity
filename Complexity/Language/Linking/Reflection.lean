/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Semantics

/-!
# Reflection of finite execution through typed program embeddings

Every finite execution of a renamed statement comes from the original statement.
The proof follows the target execution, including recursive calls and all loop
outcomes. It preserves the complete final state and control outcome and requires
neither injectivity of the function map nor an independent termination premise.
-/

namespace Complexity.Language

namespace Exec

private theorem renamed_body_cast {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (cast (congrArg (fun signature => Stmt source signature.params signature.result)
      (map.signature_eq fn).symm) (sourceProgram.body fn)).renameCalls map =
        targetProgram.body (map.toFun fn) := by
  rw [Stmt.renameCalls_cast map (map.signature_eq fn).symm, ← embedded fn]
  simp only [SignatureMap.body, cast_cast, cast_eq]

private theorem of_renameCalls_aux {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {targetStatement : Stmt target Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec targetProgram targetStatement entry finish control) :
    ∀ statement : Stmt source Γ result, statement.renameCalls map = targetStatement →
      Exec sourceProgram statement entry finish control := by
  induction execution with
  | skip =>
      intro statement same
      cases statement <;> cases same
      exact .skip _
  | assign =>
      intro statement same
      cases statement <;> cases same
      exact .assign _ _ _
  | letPrim _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .letPrim (ih _ rfl)
  | alloc _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .alloc (ih _ rfl)
  | scope _ safe ih =>
      intro statement same
      cases statement <;> cases same
      exact .scope (ih _ rfl) safe
  | scopeEscape _ escapes ih =>
      intro statement same
      cases statement <;> cases same
      exact .scopeEscape (ih _ rfl) escapes
  | read loaded _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .read loaded (ih _ rfl)
  | readFault failed =>
      intro statement same
      cases statement <;> cases same
      exact .readFault failed
  | write written =>
      intro statement same
      cases statement <;> cases same
      exact .write written
  | writeFault failed =>
      intro statement same
      cases statement <;> cases same
      exact .writeFault failed
  | slice sliced _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .slice sliced (ih _ rfl)
  | sliceFault failed =>
      intro statement same
      cases statement <;> cases same
      exact .sliceFault failed
  | seqNormal _ _ ihHead ihTail =>
      intro statement same
      cases statement <;> cases same
      exact .seqNormal (ihHead _ rfl) (ihTail _ rfl)
  | seqReturn _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .seqReturn (ih _ rfl)
  | seqFault _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .seqFault (ih _ rfl)
  | iteTrue test _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .iteTrue test (ih _ rfl)
  | iteFalse test _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .iteFalse test (ih _ rfl)
  | matchNone selected _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .matchNone selected (ih _ rfl)
  | matchSome selected _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .matchSome selected (ih _ rfl)
  | whileFalse _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .whileFalse (ih _ rfl)
  | whileTrue _ _ _ ihGuard ihBody ihRest =>
      intro statement same
      cases statement <;> cases same
      exact .whileTrue (ihGuard _ rfl) (ihBody _ rfl) (ihRest _ rfl)
  | whileReturn _ _ ihGuard ihBody =>
      intro statement same
      cases statement <;> cases same
      exact .whileReturn (ihGuard _ rfl) (ihBody _ rfl)
  | whileFault _ _ ihGuard ihBody =>
      intro statement same
      cases statement <;> cases same
      exact .whileFault (ihGuard _ rfl) (ihBody _ rfl)
  | whileGuardFault _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .whileGuardFault (ih _ rfl)
  | whileGuardMissingReturn _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .whileGuardMissingReturn (ih _ rfl)
  | ret =>
      intro statement same
      cases statement <;> cases same
      exact .ret _ _
  | @callReturn Γ result _ _ _ _ _ _ _ _ _ _ ihCallee ihBody =>
      intro statement same
      cases statement
      case call fn args continuation =>
        cases same
        have callee := ihCallee _ (renamed_body_cast embedded fn)
        have body := ihBody _ (Stmt.renameCalls_cast map
          (congrArg (fun signature => Signature.mk (signature.result :: Γ) result)
            (map.signature_eq fn).symm) continuation)
        simpa only [Stmt.callOfEq, cast_cast, cast_eq] using
          (Exec.callReturnOfEq (program := sourceProgram) (fn := fn)
            (args := cast (congrArg (fun signature => Args Γ signature.params)
              (map.signature_eq fn).symm) args)
            (continuation := cast (congrArg
              (fun signature => Stmt source (signature.result :: Γ) result)
              (map.signature_eq fn).symm) continuation)
            (map.signature_eq fn).symm callee body)
      all_goals cases same
  | @callFault Γ result _ _ _ _ _ _ _ ih =>
      intro statement same
      cases statement
      case call fn args continuation =>
        cases same
        have callee := ih _ (renamed_body_cast embedded fn)
        simpa only [Stmt.callOfEq, cast_cast, cast_eq] using
          (Exec.callFaultOfEq (program := sourceProgram) (fn := fn)
            (args := cast (congrArg (fun signature => Args Γ signature.params)
              (map.signature_eq fn).symm) args)
            (continuation := cast (congrArg
              (fun signature => Stmt source (signature.result :: Γ) result)
              (map.signature_eq fn).symm) continuation)
            (map.signature_eq fn).symm callee)
      all_goals cases same
  | @callMissingReturn Γ result _ _ _ _ _ _ ih =>
      intro statement same
      cases statement
      case call fn args continuation =>
        cases same
        have callee := ih _ (renamed_body_cast embedded fn)
        simpa only [Stmt.callOfEq, cast_cast, cast_eq] using
          (Exec.callMissingReturnOfEq (program := sourceProgram) (fn := fn)
            (args := cast (congrArg (fun signature => Args Γ signature.params)
              (map.signature_eq fn).symm) args)
            (continuation := cast (congrArg
              (fun signature => Stmt source (signature.result :: Γ) result)
              (map.signature_eq fn).symm) continuation)
            (map.signature_eq fn).symm callee)
      all_goals cases same

/-- A finite execution of the renamed statement reflects to the same source
state and outcome, including faults and early returns. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Stmt source Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec targetProgram (statement.renameCalls map) entry finish control) :
    Exec sourceProgram statement entry finish control :=
  of_renameCalls_aux embedded execution statement rfl

/-- Relocating a statement preserves and reflects all finite source behavior. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Stmt source Γ result}
    {entry finish : State Γ} {control : Control result} :
    Exec targetProgram (statement.renameCalls map) entry finish control ↔
      Exec sourceProgram statement entry finish control :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end Exec

end Complexity.Language
