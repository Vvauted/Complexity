/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues
import Complexity.Computability.Ram.Compiler.Language.Control

/-!
# Exact costs of independently proved source executions

An `ExecutionCost` indexes an existing realized source execution. This module
connects its count to the existing `LocalMeasuredExec`, retaining the actual
source values and private return flag from the behavior simulation. It does not
introduce another evaluator or require an algorithm's correctness proof again.

The core's executed branches include their real guard and jump instructions.
A returned function additionally pays for flag initialization and final
dispatch. Internal calls include the callee's complete body and actual calling
convention exactly once. The outer invocation and final halt remain separate.

Register placement is a compiler detail: the canonical call-cost expression is
valid at every reserved-register boundary. The public function theorem asks
only for source arguments and their representation, not a register proof.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem parameterMap_bodyBound (Γ : List Ty) (result : Ty) :
    RegisterMap.Bounded (parameterMap Γ) (contextSize Γ + fieldCount result) := by
  intro τ scalar v
  have bound : parameterMap Γ 0 scalar v < contextSize Γ := by
    simpa only [Nat.zero_add] using (parameterMap_bounded Γ 0 scalar v)
  exact Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)

namespace ExecutionCost

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit steps : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Env Γ} {outcome : Control result}
variable {execution : RealizedExec program w depth stmt entry finish outcome}

/-- A returned core pays two instructions for flag initialization and three
for the final true-flag dispatch. Its external continuation is not executed. -/
private theorem lowerReturned_of_core {value : Value result} (controlReg : Nat) (hw : 0 < w)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout resultSlot flag finish (.returned value) t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt),
      layout.Bounded next → layout.Matches entry s.regs →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) (steps + 5) s t ∧
        (resultExprs result resultSlot).map t.eval = valueWords w value := by
  intro layout next resultSlot s continuation bounded matched
  let flag := returnFlag result next resultSlot
  have nextFlag : next ≤ flag := Nat.le_max_left _ _
  have resultFlag : resultSlot + fieldCount result ≤ flag := Nat.le_max_right _ _
  have avoids : layout.Avoids flag := by
    intro τ scalar v
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (bounded scalar v) nextFlag)
  have bounded' : layout.Bounded (flag + 1) := by
    intro τ scalar v
    exact Nat.lt_of_lt_of_le (bounded scalar v) (Nat.le_trans nextFlag (Nat.le_succ flag))
  have matched' : layout.Matches entry (s.setReg flag 0).regs :=
    RegisterMap.Matches.setReg_of_ne matched avoids 0
  obtain ⟨t, body, property⟩ := core layout (flag + 1) resultSlot flag (s.setReg flag 0)
    bounded' matched' avoids (Nat.lt_succ_self flag) resultFlag
    (Source.State.setReg_same s flag 0)
  have flagInit : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) 2 s (s.setReg flag 0) := .assign trivial
  have raised : t.eval (.var flag) ≠ 0 := by
    change t.regs flag ≠ 0
    rw [property.2]
    exact Word.one_ne_zero hw
  have dispatch : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.ite (.var flag) .skip continuation) 3 t t :=
    .iteTrue (c := .var flag) trivial raised .skip
  refine ⟨t, ?_, property.1⟩
  convert Source.LocalMeasuredExec.seq flagInit (Source.LocalMeasuredExec.seq body dispatch)
    using 1
  omega

/-- The observed core count is exactly the existing local compiler's measured
execution, with the same represented outcome. Register separation is internal
to this shared theorem; the function wrapper chooses those slots automatically. -/
theorem lowerCoreMeasured (cost : ExecutionCost execution steps) (controlReg : Nat)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout resultSlot flag finish outcome t := by
  induction cost with
  | skip entry =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      exact ⟨s, .skip, matched, flagZero⟩
  | @letPrim Γ τ result depth value body entry finish outcome fits execution steps cost ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have first := lowerPrim_measured (control := controlReg) (program := lowerProgram program)
        (heapLimit := heapLimit) (depth := depth) layout next value entry s hw matched fits
      have matching : RegisterMap.Matches (RegisterMap.extend layout τ next)
          (Env.cons (value.eval entry) entry)
          (s.setRegs (valueRegs τ next) (valueWords w (value.eval entry))).regs :=
        lowerPrim_matches layout next value entry s hw matched fits bounded
      have flagPreserved :
          (s.setRegs (valueRegs τ next) (valueWords w (value.eval entry))).regs flag = 0 :=
        (valueRegs_setRegs_other s τ next flag (valueWords w (value.eval entry))
          (Nat.ne_of_gt fresh)).trans flagZero
      obtain ⟨t, rest, property⟩ := ih (RegisterMap.extend layout τ next)
        (next + fieldCount τ) resultSlot flag _
        (RegisterMap.extend_bounded bounded) matching
        (RegisterMap.Avoids.extend avoids (Nat.ne_of_gt fresh))
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag flagPreserved
      exact ⟨t, .seq first rest, ControlMatches.tail property⟩
  | @seqNormal Γ result depth first second entry middle finish outcome head tail
      firstSteps secondSteps firstCost secondCost ihHead ihTail =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨middleTarget, firstRun, middleMatches⟩ :=
        ihHead layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, secondRun, property⟩ :=
        ihTail layout next resultSlot flag middleTarget bounded middleMatches.1 avoids
          fresh resultFlag middleMatches.2
      refine ⟨t, ?_, property⟩
      convert Source.LocalMeasuredExec.seq firstRun
        (Source.LocalMeasuredExec.iteFalse (c := .var flag) (yes := .skip)
          trivial middleMatches.2 secondRun) using 1
      simp only [Expr.compile, List.length_singleton]
      omega
  | seqReturn cost ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, firstRun, property⟩ :=
        ih layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq firstRun (.iteTrue (c := .var flag) trivial raised .skip), property⟩
  | @iteTrue Γ result depth condition yes no entry finish outcome test execution steps cost ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, body, property⟩ :=
        ih layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have fits : valueToNat (condition.eval entry) < 2 ^ w := by
        rw [test]
        exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)
      have decoded := atomExpr_toNat layout condition .bool entry s.regs s.mem hw matched fits
      have conditionTrue : s.eval (atomExpr layout condition .bool) ≠ 0 := by
        intro zero
        change (s.eval (atomExpr layout condition .bool)).toNat = _ at decoded
        rw [zero, test] at decoded
        exact Nat.zero_ne_one decoded
      refine ⟨t, ?_, property⟩
      convert Source.LocalMeasuredExec.iteTrue
        (atomExpr_readsBelow layout condition .bool s) conditionTrue body using 1
      simp only [atomExpr_compile_length]
      omega
  | @iteFalse Γ result depth condition yes no entry finish outcome test execution steps cost ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, body, property⟩ :=
        ih layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have fits : valueToNat (condition.eval entry) < 2 ^ w := by
        rw [test]
        exact Nat.two_pow_pos w
      have decoded := atomExpr_toNat layout condition .bool entry s.regs s.mem hw matched fits
      have conditionFalse : s.eval (atomExpr layout condition .bool) = 0 := by
        apply (Word.toNat_eq_zero_iff _).mp
        simpa only [test, valueToNat] using decoded
      refine ⟨t, ?_, property⟩
      convert Source.LocalMeasuredExec.iteFalse
        (atomExpr_readsBelow layout condition .bool s) conditionFalse body using 1
      simp only [atomExpr_compile_length]
      omega
  | @ret Γ result depth value entry fits =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      let received := s.setRegs (valueRegs result resultSlot) (valueWords w (value.eval entry))
      have writeResult := lowerReturn_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout resultSlot value entry s hw matched (fun _ => fits)
      have raiseFlag : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
          (.assign flag (.const 1)) 2 received (received.setReg flag 1) := .assign trivial
      refine ⟨received.setReg flag 1, .seq writeResult raiseFlag, ?_⟩
      refine ⟨?_, Source.State.setReg_same received flag 1⟩
      rw [resultExprs_setReg_eval result resultSlot flag 1 received
        (flag_not_mem_valueRegs result resultSlot flag resultFlag)]
      exact resultExprs_setRegs_eval result resultSlot (value.eval entry) s
  | @callReturn Γ result depth fn args body entry calleeFinish value finish outcome
      arguments callee execution calleeSteps bodySteps calleeCost bodyCost ihCallee ihBody =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨calleeTarget, calleeRun, calleeResult⟩ :=
        lowerReturned_of_core controlReg hw ihCallee (parameterMap signatures[fn].params)
          (contextSize signatures[fn].params + fieldCount signatures[fn].result)
          (contextSize signatures[fn].params) (s.enter (envWords w (args.eval entry))) .skip
          (parameterMap_bodyBound _ _) (parameterMap_matches_enter s _ arguments)
      have invocation : Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
          (lowerFunc program fn) (envWords w (args.eval entry)) (calleeSteps + 5) s
          (valueWords w value) (s.restore calleeTarget) := by
        exact ⟨by simp, (lowerFunc_wellFormed program fn).1, calleeTarget, calleeRun,
          resultExprs_readsBelow _ _ calleeTarget, calleeResult.symm, rfl⟩
      have callRun := lowerCall_measured (τ := signatures[fn].result)
        layout args entry s next hw matched arguments invocation
        (lowerProgram_lookup program fn)
        (by simp only [lowerFunc_results_length])
      have restored : layout.Matches entry (s.restore calleeTarget).regs :=
        matched.restore calleeTarget
      have matching : RegisterMap.Matches
          (RegisterMap.extend layout signatures[fn].result next) (Env.cons value entry)
          ((s.restore calleeTarget).setRegs (valueRegs signatures[fn].result next)
            (valueWords w value)).regs :=
        restored.setRegs bounded value (fun _ => callee.returned_fits)
      have flagPreserved :
          ((s.restore calleeTarget).setRegs (valueRegs signatures[fn].result next)
            (valueWords w value)).regs flag = 0 :=
        (valueRegs_setRegs_other (s.restore calleeTarget) signatures[fn].result next flag
          (valueWords w value) (Nat.ne_of_gt fresh)).trans flagZero
      obtain ⟨t, rest, property⟩ := ihBody
        (RegisterMap.extend layout signatures[fn].result next)
        (next + fieldCount signatures[fn].result) resultSlot flag _
        (RegisterMap.extend_bounded bounded) matching
        (RegisterMap.Avoids.extend avoids (Nat.ne_of_gt fresh))
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag flagPreserved
      exact ⟨t, .seq callRun rest, ControlMatches.tail property⟩

/-- A returned source statement executes its wrapper for exactly five further
steps. Any supplied normal continuation is bypassed, not copied or charged. -/
theorem lowerReturnedMeasured {value : Value result}
    {execution : RealizedExec program w depth stmt entry finish (.returned value)}
    (cost : ExecutionCost execution steps) (controlReg : Nat) (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt),
      layout.Bounded next → layout.Matches entry s.regs →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) (steps + 5) s t ∧
        (resultExprs result resultSlot).map t.eval = valueWords w value :=
  lowerReturned_of_core controlReg hw (cost.lowerCoreMeasured controlReg hw)

/-- The exact core observation yields the actual generated function's body
count, including its private flag wrapper. This does not include its enclosing
call's argument, frame, return or halt work. -/
theorem functionMeasuredExec {fn : Fin signatures.length}
    {args finish : Env signatures[fn].params} {value : Value signatures[fn].result}
    {execution : RealizedExec program w depth (program.body fn) args finish (.returned value)}
    (cost : ExecutionCost execution steps) (controlReg : Nat) (hw : 0 < w)
    (arguments : EnvFits w args) (s : Source.State w) :
    ∃ t, Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (lowerFunc program fn) (envWords w args) (steps + 5) s (valueWords w value) t := by
  obtain ⟨callee, body, result⟩ := cost.lowerReturnedMeasured controlReg hw
    (parameterMap signatures[fn].params)
    (contextSize signatures[fn].params + fieldCount signatures[fn].result)
    (contextSize signatures[fn].params) (s.enter (envWords w args)) .skip
    (parameterMap_bodyBound _ _) (parameterMap_matches_enter s args arguments)
  exact ⟨s.restore callee, by simp, (lowerFunc_wellFormed program fn).1,
    callee, body, resultExprs_readsBelow _ _ callee, result.symm, rfl⟩

end ExecutionCost

end Ram.LanguageCompiler
