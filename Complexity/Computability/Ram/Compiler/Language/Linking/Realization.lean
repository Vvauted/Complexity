/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Reflection
import Complexity.Computability.Ram.Compiler.Language.Realization

/-!
# Realization through typed source program embeddings

Renaming calls preserves and reflects successful source realizations at the same
word width and call-nesting capacity. Every primitive, argument, buffer and
returned-value range condition is retained, together with the actual final heap.
The proof follows the existing `RealizedExec`; no additional execution relation,
termination premise or instruction budget is introduced.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace RealizedExec

/-- The realized returning-call rule through an equality of complete signatures.
Transport changes no value range, heap effect or call-nesting requirement. -/
theorem callReturnOfEq {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature) {w depth : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params}
    {value : Value signature.result}
    {finish : Complexity.Language.State (signature.result :: Γ)} {control : Control result}
    (arguments : EnvFits w (args.eval entry.locals))
    (callee : RealizedExec program w depth
      (cast (congrArg (fun signature =>
        Complexity.Language.Stmt signatures signature.params signature.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value))
    (body : RealizedExec program w (depth + 1) continuation
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control) :
    RealizedExec program w (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation)
      entry finish.tail control := by
  cases same
  exact .callReturn arguments callee body

/-- A typed function-table embedding preserves every successful realization at
the same word width and nesting capacity, with all range premises unchanged. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : RealizedExec sourceProgram w depth statement entry finish control) :
    RealizedExec targetProgram w depth (statement.renameCalls map) entry finish control := by
  induction execution with
  | skip => exact .skip _
  | assign target value entry fits => exact .assign target value entry fits
  | letPrim fits _ ih => exact .letPrim fits ih
  | read bufferFits indexFits loaded valueFits _ ih =>
      exact .read bufferFits indexFits loaded valueFits ih
  | write bufferFits indexFits valueFits written =>
      exact .write bufferFits indexFits valueFits written
  | slice bufferFits offsetFits lengthFits sliced viewFits _ ih =>
      exact .slice bufferFits offsetFits lengthFits sliced viewFits ih
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | iteTrue test _ ih => exact .iteTrue test ih
  | iteFalse test _ ih => exact .iteFalse test ih
  | matchNone selected _ ih => exact .matchNone selected ih
  | matchSome selected payloadFits _ ih => exact .matchSome selected payloadFits ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | ret value entry fits => exact .ret value entry fits
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments _ _ ihCallee ihBody =>
      apply callReturnOfEq (map.signature_eq fn) arguments (body := ihBody)
      change RealizedExec targetProgram _ _ (map.body targetProgram fn) _ _ _
      rw [embedded fn]
      exact ihCallee

private theorem renamed_body_cast {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (cast (congrArg (fun signature =>
      Complexity.Language.Stmt source signature.params signature.result)
      (map.signature_eq fn).symm) (sourceProgram.body fn)).renameCalls map =
        targetProgram.body (map.toFun fn) := by
  rw [Complexity.Language.Stmt.renameCalls_cast map (map.signature_eq fn).symm, ← embedded fn]
  simp only [SignatureMap.body, cast_cast, cast_eq]

private theorem of_renameCalls_aux {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {targetStatement : Complexity.Language.Stmt target Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : RealizedExec targetProgram w depth targetStatement entry finish control) :
    ∀ statement : Complexity.Language.Stmt source Γ result,
      statement.renameCalls map = targetStatement →
        RealizedExec sourceProgram w depth statement entry finish control := by
  induction execution with
  | skip =>
      intro statement same
      cases statement <;> cases same
      exact .skip _
  | assign target value entry fits =>
      intro statement same
      cases statement <;> cases same
      exact .assign _ _ _ fits
  | letPrim fits _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .letPrim fits (ih _ rfl)
  | read bufferFits indexFits loaded valueFits _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .read bufferFits indexFits loaded valueFits (ih _ rfl)
  | write bufferFits indexFits valueFits written =>
      intro statement same
      cases statement <;> cases same
      exact .write bufferFits indexFits valueFits written
  | slice bufferFits offsetFits lengthFits sliced viewFits _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih _ rfl)
  | seqNormal _ _ ihHead ihTail =>
      intro statement same
      cases statement <;> cases same
      exact .seqNormal (ihHead _ rfl) (ihTail _ rfl)
  | seqReturn _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .seqReturn (ih _ rfl)
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
  | matchSome selected payloadFits _ ih =>
      intro statement same
      cases statement <;> cases same
      exact .matchSome selected payloadFits (ih _ rfl)
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
  | ret value entry fits =>
      intro statement same
      cases statement <;> cases same
      exact .ret _ _ fits
  | @callReturn Γ result depth _ _ _ _ _ _ _ _ arguments _ _ ihCallee ihBody =>
      intro statement same
      cases statement
      case call fn args continuation =>
        cases same
        have callee := ihCallee _ (renamed_body_cast embedded fn)
        have body := ihBody _ (Complexity.Language.Stmt.renameCalls_cast map
          (congrArg (fun signature => Signature.mk (signature.result :: Γ) result)
            (map.signature_eq fn).symm) continuation)
        simpa only [Complexity.Language.Stmt.callOfEq, cast_cast, cast_eq] using
          (RealizedExec.callReturnOfEq (program := sourceProgram) (fn := fn)
            (args := cast (congrArg (fun signature => Args Γ signature.params)
              (map.signature_eq fn).symm) args)
            (continuation := cast (congrArg
              (fun signature => Complexity.Language.Stmt source (signature.result :: Γ) result)
              (map.signature_eq fn).symm) continuation)
            (map.signature_eq fn).symm arguments callee body)
      all_goals cases same

/-- A successful renamed realization comes from the original statement with
the same ranges, word width, nesting capacity and complete final state. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : RealizedExec targetProgram w depth (statement.renameCalls map)
      entry finish control) :
    RealizedExec sourceProgram w depth statement entry finish control :=
  of_renameCalls_aux embedded execution statement rfl

/-- Typed relocation preserves and reflects realization without changing any
resource-capacity or mathematical value-range assumption. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result} :
    RealizedExec targetProgram w depth (statement.renameCalls map) entry finish control ↔
      RealizedExec sourceProgram w depth statement entry finish control :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end RealizedExec

namespace RealizationWP

/-- Reuse source realization postconditions after linking, retaining the same
word width, nesting capacity and final states. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    (specification : RealizationWP sourceProgram w depth statement normal returned entry) :
    RealizationWP targetProgram w depth (statement.renameCalls map) normal returned entry := by
  obtain ⟨finish, control, execution, postcondition⟩ := specification
  exact ⟨finish, control, execution.renameCalls embedded, postcondition⟩

/-- Reflect realization postconditions through the same typed source embedding. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    (specification : RealizationWP targetProgram w depth (statement.renameCalls map)
      normal returned entry) :
    RealizationWP sourceProgram w depth statement normal returned entry := by
  obtain ⟨finish, control, execution, postcondition⟩ := specification
  exact ⟨finish, control, execution.of_renameCalls embedded, postcondition⟩

/-- Linking leaves realization specifications equivalent, not merely valid in
one direction under a separately assumed terminating source execution. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ} :
    RealizationWP targetProgram w depth (statement.renameCalls map) normal returned entry ↔
      RealizationWP sourceProgram w depth statement normal returned entry :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end RealizationWP

end Ram.LanguageCompiler
