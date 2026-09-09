/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Linking.Realization
import Complexity.Computability.Ram.Compiler.Language.Linking.Lowering
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.CostDeterministic

/-!
# Exact execution costs through source program embeddings

Typed call relocation preserves the existing compiler-derived count, including
the actual callee frame and returning-body work. The forward proof follows
`ExecutionCost`; reflection reuses realization reflection, existence of a cost
observation and its determinism. It therefore covers every target realization,
not only a chosen execution obtained by forwarding a source witness.

Statement bounds transfer in both directions with unchanged entry states and
numerical bounds. They remain uniform over word widths and call capacities;
neither transfer provides or assumes a budget-based termination argument.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ExecutionCost

/-- Transport the existing returning-call charge along an equality of complete
signatures. The actual function and its compiler-derived call overhead are unchanged. -/
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
    {arguments : EnvFits w (args.eval entry.locals)}
    {callee : RealizedExec program w depth
      (cast (congrArg (fun signature =>
        Complexity.Language.Stmt signatures signature.params signature.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {body : RealizedExec program w (depth + 1) continuation
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
    {calleeSteps bodySteps : Nat}
    (calleeCost : ExecutionCost callee calleeSteps) (bodyCost : ExecutionCost body bodySteps) :
    ExecutionCost (RealizedExec.callReturnOfEq same arguments callee body)
      (callCost program fn (calleeSteps + 2) + bodySteps) := by
  cases same
  exact .callReturn (arguments := arguments) calleeCost bodyCost

/-- Renaming calls through an actual program embedding preserves the exact
compiled core count of the same realized execution. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec sourceProgram w depth statement entry finish control}
    {steps : Nat} (cost : ExecutionCost execution steps) :
    ExecutionCost (execution.renameCalls embedded) steps := by
  induction cost with
  | skip entry => exact .skip entry
  | @assign Γ τ result depth target value entry fits =>
      exact .assign target value entry (fits := fits)
  | @letPrim Γ τ result depth value continuation entry finish control fits body steps _ ih =>
      exact .letPrim (fits := fits) ih
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits body steps _ ih =>
      exact .read (bufferFits := bufferFits) (indexFits := indexFits)
        (loaded := loaded) (valueFits := valueFits) ih
  | @write Γ result kind depth buffer index value entry heap
      bufferFits indexFits valueFits written =>
      exact .write (bufferFits := bufferFits) (indexFits := indexFits)
        (valueFits := valueFits) (written := written)
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits body steps _ ih =>
      exact .slice (bufferFits := bufferFits) (offsetFits := offsetFits)
        (lengthFits := lengthFits) (sliced := sliced) (viewFits := viewFits) ih
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | @iteTrue Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteTrue (test := test) ih
  | @iteFalse Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteFalse (test := test) ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | @ret Γ result depth value entry fits => exact .ret value entry (fits := fits)
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments callee body calleeSteps bodySteps _ _ ihCallee ihBody =>
      obtain ⟨callee', calleeCost'⟩ :
          ∃ callee' : RealizedExec targetProgram w depth (map.body targetProgram fn)
              (entry.enter (args.eval entry.locals)) calleeFinish (.returned value),
            ExecutionCost callee' calleeSteps := by
        rw [embedded fn]
        exact ⟨callee.renameCalls embedded, ihCallee⟩
      have relocated := callReturnOfEq (map.signature_eq fn)
        (args := args) (continuation := continuation.renameCalls map)
        (arguments := arguments) calleeCost' ihBody
      simpa only [callCost_embeds embedded fn] using relocated

/-- Every realized execution of a renamed statement has the original count.
Reflection first recovers the source execution; cost determinism then identifies
its count with the given target observation, without assuming source termination. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec targetProgram w depth (statement.renameCalls map)
      entry finish control}
    {steps : Nat} (cost : ExecutionCost execution steps) :
    ExecutionCost (execution.of_renameCalls embedded) steps := by
  obtain ⟨originalSteps, originalCost⟩ := (execution.of_renameCalls embedded).exists_cost
  have same : originalSteps = steps := (originalCost.renameCalls embedded).deterministic cost
  exact same ▸ originalCost

/-- Exact cost observations are invariant under typed source relocation. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {w depth : Nat} {Γ : List Ty} {result : Ty}
    {statement : Complexity.Language.Stmt source Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec sourceProgram w depth statement entry finish control}
    {steps : Nat} :
    ExecutionCost (execution.renameCalls embedded) steps ↔ ExecutionCost execution steps :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end ExecutionCost

namespace StmtCostBound

/-- A source bound applies to every realized target execution of the relocated
statement, with the same mathematical entry and bound. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Complexity.Language.Stmt source Γ result}
    {entry : Complexity.Language.State Γ} {bound : Nat}
    (specification : StmtCostBound sourceProgram statement entry bound) :
    StmtCostBound targetProgram (statement.renameCalls map) entry bound := by
  intro w depth finish control execution steps cost
  exact specification (execution.of_renameCalls embedded) (cost.of_renameCalls embedded)

/-- Reflect a uniform target statement bound to its original source statement. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Complexity.Language.Stmt source Γ result}
    {entry : Complexity.Language.State Γ} {bound : Nat}
    (specification : StmtCostBound targetProgram (statement.renameCalls map) entry bound) :
    StmtCostBound sourceProgram statement entry bound := by
  intro w depth finish control execution steps cost
  exact specification (execution.renameCalls embedded) (cost.renameCalls embedded)

/-- Typed source embeddings preserve and reflect bounds over all realized
executions, uniformly in word width and call capacity. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} {statement : Complexity.Language.Stmt source Γ result}
    {entry : Complexity.Language.State Γ} {bound : Nat} :
    StmtCostBound targetProgram (statement.renameCalls map) entry bound ↔
      StmtCostBound sourceProgram statement entry bound :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end StmtCostBound

end Ram.LanguageCompiler
