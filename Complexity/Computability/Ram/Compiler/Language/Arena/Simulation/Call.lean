/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.Call
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Allocating functions and their actual call continuations

The shared core postcondition initializes an ordinary compiled function at its
parameter layout and pays for the actual private-flag assignment. The existing
measured function and call rules retain the callee's final memory while restoring
caller registers. Placement agreement then transports the suspended caller's
rooted values before the continuation resumes at the actual advanced cursor.

Exact source result ranges remain explicit. Equality with an encoded word list
alone cannot recover a mathematical natural number from its modular encoding.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

/-- A returning core supplies an actual compiled function invocation. Its final
heap, cursor and placement survive the ordinary caller-register restoration. -/
theorem functionMeasuredExec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor finalCursor steps : Nat} {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {heap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)}
    (core : ArenaCoreSimulates execution w heapLimit depth cursor finalCursor steps)
    (controlReg : Nat) (hw : 0 < w) (arguments : EnvFits w args)
    (rooted : args.Rooted heap) (s : Source.State w)
    {placement : Nat → Word w} (arena : ArenaRep placement cursor heapLimit heap s) :
    ∃ finalPlacement t,
      Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) (steps + 2) s
        (valueWords finalPlacement value) t ∧
      ArenaRep finalPlacement finalCursor heapLimit finish.heap t ∧
      Placement.Agrees heap placement finalPlacement := by
  let resultSlot := contextSize signatures[fn].params
  let flag := resultSlot + fieldCount signatures[fn].result
  let entered := s.enter (envWords placement args)
  have parameters : RegisterMap.Bounded (parameterMap signatures[fn].params) resultSlot := by
    intro τ v i
    simpa only [Nat.zero_add] using parameterMap_bounded signatures[fn].params 0 v i
  have avoids : RegisterMap.Avoids (parameterMap signatures[fn].params) flag := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (parameters v i) (Nat.le_add_right _ _))
  have bounded : RegisterMap.Bounded (parameterMap signatures[fn].params) (flag + 1) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (parameters v i)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ flag))
  have matched : RegisterMap.Matches (parameterMap signatures[fn].params) placement args
      (entered.setReg flag 0).regs :=
    RegisterMap.Matches.setReg_of_ne (parameterMap_matches_enter s placement args arguments)
      avoids 0
  have preparedArena : ArenaRep placement cursor heapLimit heap (entered.setReg flag 0) :=
    arena.of_mem_eq rfl
  obtain ⟨finalPlacement, callee, body, property, finalArena, agreed, _⟩ :=
    core controlReg hw placement (parameterMap signatures[fn].params)
      (flag + 1) resultSlot flag (entered.setReg flag 0)
      (parameterMap_regular signatures[fn].params) bounded matched avoids
      (Nat.lt_succ_self flag) (Nat.le_refl _) (Or.inr (parameters.avoidsRange _))
      rooted preparedArena (Source.State.setReg_same _ _ _)
  have initialized : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) 2 entered (entered.setReg flag 0) := .assign trivial
  have measured : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (lowerBody program fn) (steps + 2) entered callee := by
    simpa only [lowerBody, returnFlag, Nat.max_self, Nat.add_comm 2 steps] using
      Source.LocalMeasuredExec.seq initialized body
  refine ⟨finalPlacement, s.restore callee, ?_,
    finalArena.of_mem_eq (Source.State.restore_mem s callee), agreed⟩
  rw [← property.1]
  exact Source.FunctionMeasuredExec.of_body (f := lowerFunc program fn)
    (by simp only [envWords_length, lowerFunc_params]) (lowerFunc_wellFormed program fn).1
    measured (resultExprs_readsBelow signatures[fn].result resultSlot callee)

/-- Resume the actual caller after an allocating callee. Old roots are
transported to the callee heap, while the returned value uses its final placement;
the continuation may allocate again and retains both placement agreements. -/
theorem callReturn
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor calleeCursor finalCursor calleeSteps bodySteps : Nat}
    {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
    {outcome : Control result}
    {callee : Complexity.Language.Exec program (program.body fn)
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish outcome}
    (calleeCore : ArenaCoreSimulates callee w heapLimit depth cursor calleeCursor calleeSteps)
    (bodyCore : ArenaCoreSimulates body w heapLimit (depth + 1)
      calleeCursor finalCursor bodySteps)
    (arguments : EnvFits w (args.eval entry.locals)) (resultFits : ValueFits w value) :
    ArenaCoreSimulates (.callReturn callee body) w heapLimit (depth + 1) cursor finalCursor
      (callCost program fn (calleeSteps + 2) + bodySteps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  have argumentsRooted : (args.eval entry.locals).Rooted entry.heap := args.eval_rooted rooted
  obtain ⟨calleePlacement, calleeTarget, invocation, calleeArena, calleeAgreed⟩ :=
    functionMeasuredExec calleeCore controlReg hw arguments argumentsRooted s arena
  obtain ⟨callRun, matching, preserved⟩ := lowerCall_measured_fresh_of_placement_agrees
    (τ := signatures[fn].result) (value := value)
    layout args entry.locals s next hw matched arguments calleeAgreed rooted invocation
    (lowerProgram_lookup program fn) (by simp only [lowerFunc_results_length]) bounded resultFits
  have callerRooted : entry.locals.Rooted calleeFinish.heap :=
    rooted.mono callee.heap_shapeExtends
  have continuationRooted : (Complexity.Language.State.cons value
      (entry.restore calleeFinish)).locals.Rooted calleeFinish.heap :=
    callerRooted.cons value (callee.returned_rooted argumentsRooted)
  have receivedArena : ArenaRep calleePlacement calleeCursor heapLimit calleeFinish.heap
      (calleeTarget.setRegs (valueRegs signatures[fn].result next)
        (valueWords calleePlacement value)) :=
    calleeArena.of_mem_eq (Source.State.setRegs_mem _ _ _)
  obtain ⟨finalPlacement, t, rest, property, finalArena, bodyAgreed, finalMatches⟩ :=
    bodyCore controlReg hw calleePlacement
      (RegisterMap.extend layout signatures[fn].result next)
      (next + fieldCount signatures[fn].result) resultSlot flag _
      (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching
      (RegisterMap.Avoids.extend avoids fresh)
      (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
      (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
      continuationRooted receivedArena
      ((preserved flag
        (flag_not_mem_valueRegs_of_lt signatures[fn].result next flag fresh)).trans flagZero)
  refine ⟨finalPlacement, t, ?_, ControlMatches.tail property, finalArena, ?_, ?_⟩
  · exact Source.LocalMeasuredExec.seq callRun rest
  · exact Placement.Agrees.trans calleeAgreed
      (Placement.Agrees.mono bodyAgreed callee.heap_shapeExtends.size_le)
  · intro separate
    exact RegisterMap.Matches.tail (finalMatches (separate.extend
      (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

end Ram.LanguageCompiler.ArenaCoreSimulates
