/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.ExecutionCost
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Primitive
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Binding
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Buffer
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Composition
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Loop
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Call
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Scope

/-!
# Counted simulation of allocation-ready source programs

One induction on the existing cost observation composes the checked primitive,
binding, buffer, control-flow and call rules. Source execution, readiness and
cost all describe the same computation. The resulting RAM execution carries
the actual final heap, monotone cursor and placement agreement on old objects.

The function wrapper adds only the existing private-flag initialization. Outer
invocation, final halt and session bootstrap retain their separate boundaries.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaExecutionCost

/-- Every observed core cost is realized by the same lowered program, at every
legal layout and represented arena. No program-specific compiler proof is required. -/
theorem lowerCoreMeasured {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth next₀ next₁ steps : Nat} {Γ : List Ty} {result : Ty}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {outcome : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish outcome}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁}
    (cost : ArenaExecutionCost ready steps) :
    ArenaCoreSimulates execution w heapLimit depth next₀ next₁ steps := by
  induction cost with
  | skip entry => exact ArenaCoreSimulates.skip
  | @assign Γ τ result depth next target value entry fits =>
      exact ArenaCoreSimulates.assign fits
  | @letPrim Γ τ result depth next₀ next₁ value continuation entry finish outcome
      fits body ready steps tail ih =>
      exact ArenaCoreSimulates.letPrim fits ih
  | @read Γ result kind depth next₀ next₁ buffer index continuation entry finish outcome value
      bufferFits indexFits loaded valueFits body ready steps tail ih =>
      exact ArenaCoreSimulates.read (loaded := loaded) ih bufferFits indexFits valueFits
  | @write Γ result kind depth next buffer index value entry heap
      bufferFits indexFits valueFits written =>
      exact ArenaCoreSimulates.write (written := written) bufferFits indexFits valueFits
  | @slice Γ result kind depth next₀ next₁ buffer offset length continuation entry finish outcome
      view bufferFits offsetFits lengthFits sliced viewFits body ready steps tail ih =>
      exact ArenaCoreSimulates.slice (sliced := sliced) ih
        bufferFits offsetFits lengthFits viewFits
  | @alloc Γ result kind depth next₀ next₁ length initial continuation entry finish outcome
      body initialFits capacity ready steps tail ih =>
      exact ArenaCoreSimulates.alloc initialFits capacity ih
  | @scope Γ result depth next₀ bodyCursor stmt entry finish outcome body safe ready steps cost ih =>
      exact ArenaCoreSimulates.scope safe ih
  | seqNormal firstCost secondCost ihFirst ihSecond =>
      exact ArenaCoreSimulates.seqNormal ihFirst ihSecond
  | seqReturn cost ih => exact ArenaCoreSimulates.seqReturn ih
  | @iteTrue Γ result depth next₀ next₁ condition yes no entry finish outcome
      test body ready steps cost ih =>
      exact ArenaCoreSimulates.iteTrue (test := test) ih
  | @iteFalse Γ result depth next₀ next₁ condition yes no entry finish outcome
      test body ready steps cost ih =>
      exact ArenaCoreSimulates.iteFalse (test := test) ih
  | @whileFalse Γ result depth next₀ next₁ guard body entry finish test ready guardSteps
      guardCost ih =>
      exact ArenaCoreSimulates.whileFalse test ih
  | @whileTrue Γ result depth next₀ guardCursor bodyCursor next₁ guard body
      entry afterGuard afterBody finish outcome test iteration rest testReady bodyReady restReady
      guardSteps bodySteps restSteps guardCost bodyCost restCost ihGuard ihBody ihRest =>
      exact ArenaCoreSimulates.whileTrue test iteration rest ihGuard ihBody ihRest
  | @whileReturn Γ result depth next₀ guardCursor next₁ guard body entry afterGuard finish value
      test iteration testReady bodyReady guardSteps bodySteps guardCost bodyCost ihGuard ihBody =>
      exact ArenaCoreSimulates.whileReturn test iteration ihGuard ihBody
  | @ret Γ result depth next value entry fits => exact ArenaCoreSimulates.ret fits
  | @callReturn Γ result depth next₀ calleeCursor next₁ fn args continuation entry calleeFinish
      value finish outcome arguments callee body calleeReady bodyReady calleeSteps bodySteps
      calleeCost bodyCost ihCallee ihBody =>
      exact ArenaCoreSimulates.callReturn ihCallee ihBody arguments calleeReady.outcome_fits

/-- A counted returning source body gives an actual compiled function invocation
and its final arena. The extra two instructions initialize the private return flag. -/
theorem functionMeasuredExec {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth next₀ next₁ steps : Nat} {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁}
    (cost : ArenaExecutionCost ready steps) (controlReg : Nat) (hw : 0 < w)
    (arguments : EnvFits w args) (rooted : args.Rooted heap) (s : Source.State w)
    {placement : Nat → Word w} (arena : ArenaRep placement next₀ heapLimit heap s) :
    ∃ finalPlacement t,
      Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) (steps + 2) s
        (valueWords finalPlacement value) t ∧
      ArenaRep finalPlacement next₁ heapLimit finish.heap t ∧
      Placement.Agrees heap placement finalPlacement :=
  ArenaCoreSimulates.functionMeasuredExec cost.lowerCoreMeasured controlReg hw
    arguments rooted s arena

end ArenaExecutionCost
end Ram.LanguageCompiler
