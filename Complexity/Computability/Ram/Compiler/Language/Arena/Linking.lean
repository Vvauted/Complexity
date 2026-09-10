/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Reflection
import Complexity.Computability.Ram.Compiler.Language.Arena.ExecutionCost
import Complexity.Computability.Ram.Compiler.Language.Linking.Lowering

/-!
# Allocation readiness and cost through source program embeddings

The existing source execution bridge retains the actual heaps and control
outcomes. These rules transport its additional arena evidence without changing
word width, heap limit, call capacity or either cursor. Calls use the same
signature transport as source linking, and their count uses the existing
compiler-derived equality of call overheads.

Cost reflection combines readiness reflection with existence and determinism
of the same cost observation. It neither assumes source termination nor creates
another execution, allocator or cost model.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaReady

/-- Signature transport for the existing returning-call readiness rule. -/
theorem callReturnOfEq {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {w heapLimit depth next₀ calleeCursor next₁ : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params} {value : Value signature.result}
    {finish : Complexity.Language.State (signature.result :: Γ)} {control : Control result}
    {callee : Complexity.Language.Exec program
      (cast (congrArg (fun signature =>
        Complexity.Language.Stmt signatures signature.params signature.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
    (arguments : EnvFits w (args.eval entry.locals))
    (calleeReady : ArenaReady callee w heapLimit depth next₀ calleeCursor)
    (bodyReady : ArenaReady body w heapLimit (depth + 1) calleeCursor next₁) :
    ArenaReady (Complexity.Language.Exec.callReturnOfEq same callee body)
      w heapLimit (depth + 1) next₀ next₁ := by
  cases same
  exact .callReturn arguments calleeReady bodyReady

/-- Typed relocation retains every range and capacity premise of the same
source execution, including the actual cursor passed from a callee to its caller. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec sourceProgram statement entry finish control}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    ArenaReady (execution.renameCalls embedded) w heapLimit depth next₀ next₁ := by
  induction ready with
  | skip entry => exact .skip entry
  | assign target value entry fits => exact .assign target value entry fits
  | letPrim fits _ ih => exact .letPrim fits ih
  | @read Γ result kind w heapLimit depth next₀ next₁ buffer index continuation
      entry finish control value loaded body bufferFits indexFits valueFits _ ih =>
      exact .read (loaded := loaded) bufferFits indexFits valueFits ih
  | @write Γ result kind w heapLimit depth next buffer index value entry heap written
      bufferFits indexFits valueFits =>
      exact .write (written := written) bufferFits indexFits valueFits
  | @slice Γ result kind w heapLimit depth next₀ next₁ buffer offset length continuation
      entry finish control view sliced body bufferFits offsetFits lengthFits viewFits _ ih =>
      exact .slice (sliced := sliced) bufferFits offsetFits lengthFits viewFits ih
  | alloc initialFits capacity _ ih => exact .alloc initialFits capacity ih
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | @iteTrue Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih => exact .iteTrue (test := test) ih
  | @iteFalse Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih => exact .iteFalse (test := test) ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | ret value entry fits => exact .ret value entry fits
  | @callReturn Γ result w heapLimit depth next₀ calleeCursor next₁ fn args continuation
      entry calleeFinish value finish control callee body arguments _ _ ihCallee ihBody =>
      obtain ⟨callee', calleeReady⟩ :
          ∃ callee' : Complexity.Language.Exec targetProgram (map.body targetProgram fn)
              (entry.enter (args.eval entry.locals)) calleeFinish (.returned value),
            ArenaReady callee' w heapLimit depth next₀ calleeCursor := by
        rw [embedded fn]
        exact ⟨callee.renameCalls embedded, ihCallee⟩
      exact callReturnOfEq (map.signature_eq fn) arguments calleeReady ihBody

private theorem renamed_body_cast {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (cast (congrArg (fun signature =>
      Complexity.Language.Stmt source signature.params signature.result)
      (map.signature_eq fn).symm) (sourceProgram.body fn)).renameCalls map =
        targetProgram.body (map.toFun fn) := by
  rw [Complexity.Language.Stmt.renameCalls_cast map (map.signature_eq fn).symm, ← embedded fn]
  simp only [SignatureMap.body, cast_cast, cast_eq]

private theorem of_renameCalls_aux {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {targetStatement : Complexity.Language.Stmt target Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec targetProgram targetStatement entry finish control}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    ∀ statement : Complexity.Language.Stmt source Γ result,
      statement.renameCalls map = targetStatement →
        ∃ original : Complexity.Language.Exec sourceProgram statement entry finish control,
          ArenaReady original w heapLimit depth next₀ next₁ := by
  induction ready with
  | skip =>
      intro statement same
      cases statement <;> cases same
      exact ⟨_, .skip _⟩
  | assign target value entry fits =>
      intro statement same
      cases statement <;> cases same
      exact ⟨_, .assign _ _ _ fits⟩
  | letPrim fits _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .letPrim fits original⟩
  | @read Γ result kind w heapLimit depth next₀ next₁ buffer index continuation
      entry finish control value loaded body bufferFits indexFits valueFits _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .read (loaded := loaded) bufferFits indexFits valueFits original⟩
  | @write Γ result kind w heapLimit depth next buffer index value entry heap written
      bufferFits indexFits valueFits =>
      intro statement same
      cases statement <;> cases same
      exact ⟨_, .write (written := written) bufferFits indexFits valueFits⟩
  | @slice Γ result kind w heapLimit depth next₀ next₁ buffer offset length continuation
      entry finish control view sliced body bufferFits offsetFits lengthFits viewFits _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .slice (sliced := sliced) bufferFits offsetFits lengthFits viewFits original⟩
  | alloc initialFits capacity _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .alloc initialFits capacity original⟩
  | seqNormal _ _ ihHead ihTail =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, originalHead⟩ := ihHead _ rfl
      obtain ⟨_, originalTail⟩ := ihTail _ rfl
      exact ⟨_, .seqNormal originalHead originalTail⟩
  | seqReturn _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .seqReturn original⟩
  | @iteTrue Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .iteTrue (test := test) original⟩
  | @iteFalse Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .iteFalse (test := test) original⟩
  | whileFalse _ ih =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, original⟩ := ih _ rfl
      exact ⟨_, .whileFalse original⟩
  | whileTrue _ _ _ ihGuard ihBody ihRest =>
      intro statement same
      cases statement
      case «while» guard body =>
        cases same
        obtain ⟨_, originalGuard⟩ := ihGuard guard rfl
        obtain ⟨_, originalBody⟩ := ihBody body rfl
        obtain ⟨_, originalRest⟩ := ihRest (.while guard body) rfl
        exact ⟨_, .whileTrue originalGuard originalBody originalRest⟩
      all_goals cases same
  | whileReturn _ _ ihGuard ihBody =>
      intro statement same
      cases statement <;> cases same
      obtain ⟨_, originalGuard⟩ := ihGuard _ rfl
      obtain ⟨_, originalBody⟩ := ihBody _ rfl
      exact ⟨_, .whileReturn originalGuard originalBody⟩
  | ret value entry fits =>
      intro statement same
      cases statement <;> cases same
      exact ⟨_, .ret _ _ fits⟩
  | @callReturn Γ result w heapLimit depth next₀ calleeCursor next₁ _ _ _ _ _ _ _ _ _ _
      arguments _ _ ihCallee ihBody =>
      intro statement same
      cases statement
      case call fn args continuation =>
        cases same
        obtain ⟨callee, calleeReady⟩ := ihCallee _ (renamed_body_cast embedded fn)
        obtain ⟨body, bodyReady⟩ := ihBody _ (Complexity.Language.Stmt.renameCalls_cast map
          (congrArg (fun signature => Signature.mk (signature.result :: Γ) result)
            (map.signature_eq fn).symm) continuation)
        have transported := callReturnOfEq (program := sourceProgram) (fn := fn)
            (w := w) (heapLimit := heapLimit) (depth := depth)
            (next₀ := next₀) (calleeCursor := calleeCursor) (next₁ := next₁)
            (args := cast (congrArg (fun signature => Args Γ signature.params)
              (map.signature_eq fn).symm) args)
            (continuation := cast (congrArg
              (fun signature => Complexity.Language.Stmt source (signature.result :: Γ) result)
              (map.signature_eq fn).symm) continuation)
            (map.signature_eq fn).symm (fun {τ} => arguments (τ := τ)) calleeReady bodyReady
        refine ⟨?_, ?_⟩
        · simpa only [Complexity.Language.Stmt.callOfEq, cast_cast, cast_eq] using
            (Complexity.Language.Exec.callReturnOfEq (program := sourceProgram) (fn := fn)
              (args := cast (congrArg (fun signature => Args Γ signature.params)
                (map.signature_eq fn).symm) args)
              (continuation := cast (congrArg
                (fun signature => Complexity.Language.Stmt source (signature.result :: Γ) result)
                (map.signature_eq fn).symm) continuation)
              (map.signature_eq fn).symm callee body)
        · simpa only [Complexity.Language.Stmt.callOfEq, cast_cast, cast_eq] using transported
      all_goals cases same

/-- A ready renamed execution reflects to the existing source execution with
unchanged input and final cursors, not a separately chosen allocation history. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec targetProgram (statement.renameCalls map)
      entry finish control}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    ArenaReady (execution.of_renameCalls embedded) w heapLimit depth next₀ next₁ := by
  obtain ⟨_, original⟩ := of_renameCalls_aux embedded ready statement rfl
  exact original

/-- Source relocation preserves and reflects allocation readiness. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec sourceProgram statement entry finish control} :
    ArenaReady (execution.renameCalls embedded) w heapLimit depth next₀ next₁ ↔
      ArenaReady execution w heapLimit depth next₀ next₁ :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end ArenaReady

namespace ArenaExecutionCost

/-- The same complete-signature transport preserves the actual returning-call count. -/
theorem callReturnOfEq {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {w heapLimit depth next₀ calleeCursor next₁ : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params} {value : Value signature.result}
    {finish : Complexity.Language.State (signature.result :: Γ)} {control : Control result}
    {arguments : EnvFits w (args.eval entry.locals)}
    {callee : Complexity.Language.Exec program
      (cast (congrArg (fun signature =>
        Complexity.Language.Stmt signatures signature.params signature.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
    {calleeReady : ArenaReady callee w heapLimit depth next₀ calleeCursor}
    {bodyReady : ArenaReady body w heapLimit (depth + 1) calleeCursor next₁}
    {calleeSteps bodySteps : Nat}
    (calleeCost : ArenaExecutionCost calleeReady calleeSteps)
    (bodyCost : ArenaExecutionCost bodyReady bodySteps) :
    ArenaExecutionCost (ArenaReady.callReturnOfEq same arguments calleeReady bodyReady)
      (callCost program fn (calleeSteps + 2) + bodySteps) := by
  cases same
  exact .callReturn (arguments := arguments) calleeCost bodyCost

/-- Renaming source calls preserves exact core costs, including allocation and
the actual linked callee frame, without changing either cursor. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec sourceProgram statement entry finish control}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁}
    {steps : Nat} (cost : ArenaExecutionCost ready steps) :
    ArenaExecutionCost (ready.renameCalls embedded) steps := by
  induction cost with
  | skip entry => exact .skip entry
  | @assign Γ τ result depth next target value entry fits =>
      exact .assign target value entry (fits := fits)
  | @letPrim Γ τ result depth next₀ next₁ value continuation entry finish control fits
      body ready steps _ ih => exact .letPrim (fits := fits) ih
  | @read Γ result kind depth next₀ next₁ buffer index continuation entry finish control
      value bufferFits indexFits loaded valueFits body ready steps _ ih =>
      exact .read (bufferFits := bufferFits) (indexFits := indexFits)
        (loaded := loaded) (valueFits := valueFits) ih
  | @write Γ result kind depth next buffer index value entry heap bufferFits indexFits
      valueFits written =>
      exact .write (bufferFits := bufferFits) (indexFits := indexFits)
        (valueFits := valueFits) (written := written)
  | @slice Γ result kind depth next₀ next₁ buffer offset length continuation entry finish
      control view bufferFits offsetFits lengthFits sliced viewFits body ready steps _ ih =>
      exact .slice (bufferFits := bufferFits) (offsetFits := offsetFits)
        (lengthFits := lengthFits) (sliced := sliced) (viewFits := viewFits) ih
  | @alloc Γ result kind depth next₀ next₁ length initial continuation entry finish control
      body initialFits capacity ready steps _ ih =>
      exact .alloc (initialFits := initialFits) (capacity := capacity) ih
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | @iteTrue Γ result depth next₀ next₁ condition yes no entry finish control test body
      ready steps _ ih => exact .iteTrue (test := test) ih
  | @iteFalse Γ result depth next₀ next₁ condition yes no entry finish control test body
      ready steps _ ih => exact .iteFalse (test := test) ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | @ret Γ result depth next value entry fits => exact .ret value entry (fits := fits)
  | @callReturn Γ result depth next₀ calleeCursor next₁ fn args continuation entry
      calleeFinish value finish control arguments callee body calleeReady bodyReady
      calleeSteps bodySteps _ _ ihCallee ihBody =>
      obtain ⟨callee', ready', calleeCost⟩ :
          ∃ callee' : Complexity.Language.Exec targetProgram (map.body targetProgram fn)
              (entry.enter (args.eval entry.locals)) calleeFinish (.returned value),
            ∃ ready' : ArenaReady callee' w heapLimit depth next₀ calleeCursor,
              ArenaExecutionCost ready' calleeSteps := by
        rw [embedded fn]
        exact ⟨callee.renameCalls embedded, calleeReady.renameCalls embedded, ihCallee⟩
      have relocated := callReturnOfEq (map.signature_eq fn)
        (args := args) (continuation := continuation.renameCalls map)
        (arguments := arguments) calleeCost ihBody
      simpa only [callCost_embeds embedded fn] using relocated

/-- Reflect the exact count using readiness reflection and cost determinism. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec targetProgram (statement.renameCalls map)
      entry finish control}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁}
    {steps : Nat} (cost : ArenaExecutionCost ready steps) :
    ArenaExecutionCost (ready.of_renameCalls embedded) steps := by
  obtain ⟨originalSteps, originalCost⟩ := (ready.of_renameCalls embedded).exists_cost
  have same : originalSteps = steps := (originalCost.renameCalls embedded).deterministic cost
  exact same ▸ originalCost

/-- Source relocation preserves and reflects the same allocation-ready core count. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w heapLimit depth next₀ next₁ : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec sourceProgram statement entry finish control}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁} {steps : Nat} :
    ArenaExecutionCost (ready.renameCalls embedded) steps ↔ ArenaExecutionCost ready steps :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end ArenaExecutionCost
end Ram.LanguageCompiler
