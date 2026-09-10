/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Call capacity from a realized execution's cost

An `ExecutionCost` observation gives a sufficient call capacity for the same
statement, states and outcome. This reconstructs realization at the observed
instruction count; it does not bound the arbitrary capacity of the original
realization. Termination is supplied by that existing finite execution, not by
a proposed instruction budget.
-/

namespace Ram.LanguageCompiler.ExecutionCost

open Complexity.Language

/-- The observed core instruction count is a sufficient call capacity for the
same source execution. Sequential work reuses capacity, while every internal
call's actual compiler charge pays for its extra nesting level. -/
theorem realized_at_steps {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec program w depth stmt entry finish control} {steps : Nat}
    (cost : ExecutionCost execution steps) :
    RealizedExec program w steps stmt entry finish control := by
  induction cost with
  | skip entry => exact .skip entry
  | @assign Γ τ result depth target value entry fits =>
      exact .assign target value entry fits
  | @letPrim Γ τ result depth value continuation entry finish control fits body steps _ ih =>
      exact .letPrim fits (ih.mono_depth (by omega))
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits body steps _ ih =>
      exact .read bufferFits indexFits loaded valueFits (ih.mono_depth (by omega))
  | @write Γ result kind depth buffer index value entry heap
      bufferFits indexFits valueFits written =>
      exact .write bufferFits indexFits valueFits written
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits body steps _ ih =>
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih.mono_depth (by omega))
  | seqNormal _ _ ihHead ihTail =>
      exact .seqNormal (ihHead.mono_depth (by omega)) (ihTail.mono_depth (by omega))
  | seqReturn _ ih => exact .seqReturn (ih.mono_depth (by omega))
  | @iteTrue Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteTrue test (ih.mono_depth (by omega))
  | @iteFalse Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteFalse test (ih.mono_depth (by omega))
  | @matchNone Γ result τ depth value noneBranch someBranch entry finish control
      selected body steps _ ih =>
      exact .matchNone selected (ih.mono_depth (by omega))
  | @matchSome Γ result τ depth value noneBranch someBranch entry payload finish control
      selected payloadFits body steps _ ih =>
      exact .matchSome selected payloadFits (ih.mono_depth (by omega))
  | whileFalse _ ih => exact .whileFalse (ih.mono_depth (by omega))
  | whileTrue _ _ _ ihGuard ihBody ihRest =>
      exact .whileTrue (ihGuard.mono_depth (by omega)) (ihBody.mono_depth (by omega))
        (ihRest.mono_depth (by omega))
  | whileReturn _ _ ihGuard ihBody =>
      exact .whileReturn (ihGuard.mono_depth (by omega)) (ihBody.mono_depth (by omega))
  | @ret Γ result depth value entry fits => exact .ret value entry fits
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments callee body calleeSteps bodySteps _ _ ihCallee ihBody =>
      have rebuilt : RealizedExec program w (calleeSteps + bodySteps + 1)
          (.call fn args continuation) entry finish.tail control :=
        .callReturn arguments (ihCallee.mono_depth (by omega)) (ihBody.mono_depth (by omega))
      exact rebuilt.mono_depth (by rw [callCost_eq_add]; omega)

end Ram.LanguageCompiler.ExecutionCost
