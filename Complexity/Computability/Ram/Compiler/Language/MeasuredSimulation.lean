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

One induction on the existing cost observation supplies the measured RAM
execution, represented lexical fields and the source's actual final heap.
The fixed object placement is proof data, not runtime work. Calls retain the
callee's heap effects while restoring only caller registers.

Core branches include their real guard and jump instructions. A function pays
for flag initialization; the generic wrapper also dispatches around its normal
continuation. Internal calls include the actual callee body and ABI work once.

Multi-field copies are sequential assignments, not implicit snapshots. Their
source fields avoid the destination interval; scalar copies still allow operand
aliasing. Generated function layouts establish result-region separation without
requiring register obligations from algorithm authors.

Variable assignment uses the same regular layout to update its actual fields.
The represented locals change with the source assignment while the shared heap
and private return flag remain unchanged.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem parameterMap_bodyBound (Γ : List Ty) (result : Ty) :
    RegisterMap.Bounded (parameterMap Γ) (contextSize Γ + fieldCount result) := by
  intro τ v i
  have bound : parameterMap Γ 0 v i < contextSize Γ := by
    simpa only [Nat.zero_add] using (parameterMap_bounded Γ 0 v i)
  exact Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)

/-- Fresh fields preserve result-copy safety, including scalar layouts that
need not avoid the result register. -/
private theorem copySafe_extend {layout : RegisterMap Γ} {result : Ty}
    (safe : fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result))
    (fresh : resultSlot + fieldCount result ≤ next) :
    fieldCount result ≤ 1 ∨
      RegisterMap.AvoidsRange (RegisterMap.extend layout τ next)
        resultSlot (fieldCount result) := by
  rcases safe with single | separate
  · exact Or.inl single
  · exact Or.inr (separate.extend fresh)

namespace ExecutionCost

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit steps : Nat} {Γ : List Ty} {result : Ty}
variable {placement : Nat → Word w}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {outcome : Control result}
variable {execution : RealizedExec program w depth stmt entry finish outcome}

/-- Initialize the flag while retaining the actual heap and preparing the
same layout for the generic wrapper or a complete function. -/
private theorem lowerInitializedCore_of_core {value : Value result} (controlReg : Nat)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout placement resultSlot flag finish.locals (.returned value) t ∧
        HeapRep placement heapLimit finish.heap t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s →
      let flag := returnFlag result next resultSlot
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (.assign flag (.const 0)) 2 s (s.setReg flag 0) ∧
        Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
          (lowerStmtCore layout (flag + 1) resultSlot flag stmt) steps (s.setReg flag 0) t ∧
        ControlMatches layout placement resultSlot flag finish.locals (.returned value) t ∧
        HeapRep placement heapLimit finish.heap t := by
  intro layout next resultSlot s regular bounded matched copySafe represented
  let flag := returnFlag result next resultSlot
  have nextFlag : next ≤ flag := Nat.le_max_left _ _
  have resultFlag : resultSlot + fieldCount result ≤ flag := Nat.le_max_right _ _
  have avoids : layout.Avoids flag := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (bounded v i) nextFlag)
  have bounded' : layout.Bounded (flag + 1) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_trans nextFlag (Nat.le_succ flag))
  have matched' : layout.Matches placement entry.locals (s.setReg flag 0).regs :=
    RegisterMap.Matches.setReg_of_ne matched avoids 0
  obtain ⟨t, body, property, finalHeap⟩ := core layout (flag + 1) resultSlot flag (s.setReg flag 0)
    regular bounded' matched' avoids (Nat.lt_succ_self flag) resultFlag copySafe
    (represented.setReg flag 0) (Source.State.setReg_same s flag 0)
  exact ⟨t, .assign trivial, body, property, finalHeap⟩

/-- A returned generic wrapper pays for initialization and true-flag dispatch;
the external continuation is not executed. -/
private theorem lowerReturned_of_core {value : Value result} (controlReg : Nat) (hw : 0 < w)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout placement resultSlot flag finish.locals (.returned value) t ∧
        HeapRep placement heapLimit finish.heap t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) (steps + 5) s t ∧
        (resultExprs result resultSlot).map t.eval = valueWords placement value ∧
        HeapRep placement heapLimit finish.heap t := by
  intro layout next resultSlot s continuation regular bounded matched copySafe represented
  let flag := returnFlag result next resultSlot
  obtain ⟨t, flagInit, body, property, finalHeap⟩ :=
    lowerInitializedCore_of_core controlReg core layout next resultSlot s
      regular bounded matched copySafe represented
  have raised : t.eval (.var flag) ≠ 0 := by
    change t.regs flag ≠ 0
    rw [property.2]
    exact Word.one_ne_zero hw
  have dispatch : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.ite (.var flag) .skip continuation) 3 t t :=
    .iteTrue (c := .var flag) trivial raised .skip
  refine ⟨t, ?_, property.1, finalHeap⟩
  convert Source.LocalMeasuredExec.seq flagInit (Source.LocalMeasuredExec.seq body dispatch)
    using 1
  omega

/-- A complete function reserves its result interval after the parameters.
Its final heap survives caller restoration and its wrapper costs two steps. -/
private theorem lowerFunction_of_core {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {initialHeap : Heap}
    {calleeFinish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result} (controlReg : Nat)
    (core : ∀ (layout : RegisterMap signatures[fn].params)
      (next resultSlot flag : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement args s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount signatures[fn].result ≤ flag →
      (fieldCount signatures[fn].result ≤ 1 ∨
        layout.AvoidsRange resultSlot (fieldCount signatures[fn].result)) →
      HeapRep placement heapLimit initialHeap s → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag (program.body fn)) steps s t ∧
        ControlMatches layout placement resultSlot flag calleeFinish.locals (.returned value) t ∧
        HeapRep placement heapLimit calleeFinish.heap t)
    (arguments : EnvFits w args) (s : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap s) :
    ∃ t, Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (lowerFunc program fn) (envWords placement args) (steps + 2) s
        (valueWords placement value) t ∧ HeapRep placement heapLimit calleeFinish.heap t := by
  have parameters : RegisterMap.Bounded (parameterMap signatures[fn].params)
      (contextSize signatures[fn].params) := by
    intro τ v i
    simpa only [Nat.zero_add] using parameterMap_bounded signatures[fn].params 0 v i
  obtain ⟨callee, flagInit, body, property, finalHeap⟩ :=
    lowerInitializedCore_of_core (entry := ⟨args, initialHeap⟩)
      (finish := calleeFinish) (placement := placement) controlReg core
      (parameterMap signatures[fn].params)
      (contextSize signatures[fn].params + fieldCount signatures[fn].result)
      (contextSize signatures[fn].params) (s.enter (envWords placement args))
      (parameterMap_regular signatures[fn].params) (parameterMap_bodyBound _ _) (parameterMap_matches_enter s placement args arguments)
      (Or.inr (parameters.avoidsRange _)) (represented.enter _)
  have measured : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (lowerBody program fn) (steps + 2) (s.enter (envWords placement args)) callee := by
    convert Source.LocalMeasuredExec.seq flagInit body using 1
    omega
  refine ⟨s.restore callee, ?_, finalHeap.restore s⟩
  exact ⟨by simp, (lowerFunc_wellFormed program fn).1, callee, measured,
    resultExprs_readsBelow _ _ callee, property.1.symm, rfl⟩

/-- The same execution also retains its actual final locals when the result
region avoids them. Scalar return aliases remain supported by the original
control contract; the extra representation is conditional, not a new premise. -/
theorem lowerCoreMeasuredWithLocals (cost : ExecutionCost execution steps) (controlReg : Nat)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout placement resultSlot flag finish.locals outcome t ∧
        HeapRep placement heapLimit finish.heap t ∧
        (layout.AvoidsRange resultSlot (fieldCount result) →
          layout.Matches placement finish.locals t.regs) := by
  induction cost with
  | skip entry =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      exact ⟨s, .skip, ⟨matched, flagZero⟩, represented, fun _ => matched⟩
  | @assign Γ τ result depth target value entry fits =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      have assigned := lowerAssign_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout target value entry.locals s hw matched fits regular
      have matching : RegisterMap.Matches layout placement
          (entry.locals.set target (value.eval entry.locals))
          (s.setRegs (valueRegs τ (RegisterMap.base layout target))
            (valueWords placement (value.eval entry.locals))).regs :=
        lowerAssign_matches layout target value entry.locals s hw matched fits regular
      have flagPreserved := (valueRegs_setRegs_other s τ (RegisterMap.base layout target) flag
        (valueWords placement (value.eval entry.locals))
        (regular.not_mem_valueRegs_of_avoids avoids target)).trans flagZero
      exact ⟨_, assigned, ⟨matching, flagPreserved⟩, represented.setRegs _ _, fun _ => matching⟩
  | @letPrim Γ τ result depth value body entry finish outcome fits execution steps cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      have first := lowerPrim_measured (control := controlReg) (program := lowerProgram program)
        (heapLimit := heapLimit) (depth := depth) layout next value entry.locals s hw matched fits
        (Or.inr (bounded.avoidsRange _))
      have matching : RegisterMap.Matches (RegisterMap.extend layout τ next) placement
          (Env.cons (value.eval entry.locals) entry.locals)
          (s.setRegs (valueRegs τ next) (valueWords placement (value.eval entry.locals))).regs :=
        lowerPrim_matches layout next value entry.locals s hw matched fits bounded
      have flagPreserved := (valueRegs_setRegs_other s τ next flag
        (valueWords placement (value.eval entry.locals))
        (flag_not_mem_valueRegs_of_lt τ next flag fresh)).trans flagZero
      obtain ⟨t, rest, property, finalHeap, finalMatches⟩ := ih (RegisterMap.extend layout τ next)
        (next + fieldCount τ) resultSlot flag _
        (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching (RegisterMap.Avoids.extend avoids fresh)
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
        (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
        (represented.setRegs _ _) flagPreserved
      refine ⟨t, .seq first rest, ControlMatches.tail property, finalHeap, ?_⟩
      intro separate
      exact RegisterMap.Matches.tail (finalMatches (separate.extend
        (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))
  | @read Γ result kind depth buffer index body entry finish outcome value bufferFits indexFits
      loaded valueFits execution steps cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨first, preservedHeap, actualFits⟩ := lowerRead_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout next buffer index entry.locals s hw matched represented bufferFits indexFits loaded
      rw [lowerRead_stmtSize] at first
      have matching : RegisterMap.Matches (RegisterMap.extend layout kind.toTy next) placement
          (Env.cons (kind.toValue value) entry.locals)
          (s.setRegs (valueRegs kind.toTy next)
            (valueWords placement (kind.toValue value))).regs :=
        matched.setRegs (τ := kind.toTy) bounded (kind.toValue value) actualFits
      have flagPreserved := (valueRegs_setRegs_other s kind.toTy next flag
        (valueWords placement (kind.toValue value))
        (flag_not_mem_valueRegs_of_lt kind.toTy next flag fresh)).trans flagZero
      obtain ⟨t, rest, property, finalHeap, finalMatches⟩ := ih (RegisterMap.extend layout kind.toTy next)
        (next + fieldCount kind.toTy) resultSlot flag _
        (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching (RegisterMap.Avoids.extend avoids fresh)
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
        (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
        preservedHeap flagPreserved
      refine ⟨t, .seq first rest, ControlMatches.tail property, finalHeap, ?_⟩
      intro separate
      exact RegisterMap.Matches.tail (finalMatches (separate.extend
        (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))
  | @write Γ result kind depth buffer index value entry heap bufferFits indexFits valueFits written =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨first, finalHeap⟩ := lowerWrite_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout buffer index value entry.locals s hw matched represented
        bufferFits indexFits valueFits written
      rw [lowerWrite_stmtSize] at first
      exact ⟨_, first, ⟨matched, flagZero⟩, finalHeap, fun _ => matched⟩
  | @slice Γ result kind depth buffer offset length body entry finish outcome view bufferFits
      offsetFits lengthFits sliced viewFits execution steps cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨first, preservedHeap, actualFits⟩ := lowerSlice_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout next buffer offset length entry.locals s hw matched represented
        bufferFits offsetFits lengthFits bounded sliced
      rw [lowerSlice_stmtSize] at first
      have matching : RegisterMap.Matches (RegisterMap.extend layout (.buffer kind) next) placement
          (Env.cons (τ := .buffer kind) view entry.locals)
          (s.setRegs (valueRegs (.buffer kind) next)
            (valueWords placement (τ := .buffer kind) view)).regs :=
        matched.setRegs (τ := .buffer kind) bounded view actualFits
      have flagPreserved := (valueRegs_setRegs_other s (.buffer kind) next flag
        (valueWords placement (τ := .buffer kind) view)
        (flag_not_mem_valueRegs_of_lt (.buffer kind) next flag fresh)).trans flagZero
      obtain ⟨t, rest, property, finalHeap, finalMatches⟩ := ih (RegisterMap.extend layout (.buffer kind) next)
        (next + fieldCount (.buffer kind)) resultSlot flag _
        (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching (RegisterMap.Avoids.extend avoids fresh)
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
        (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
        preservedHeap flagPreserved
      refine ⟨t, .seq first rest, ControlMatches.tail property, finalHeap, ?_⟩
      intro separate
      exact RegisterMap.Matches.tail (finalMatches (separate.extend
        (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))
  | @seqNormal Γ result depth first second entry middle finish outcome head tail
      firstSteps secondSteps firstCost secondCost ihHead ihTail =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨middleTarget, firstRun, middleMatches, middleHeap, _⟩ :=
        ihHead layout next resultSlot flag s regular bounded matched avoids fresh resultFlag
          copySafe represented flagZero
      obtain ⟨t, secondRun, property, finalHeap, finalMatches⟩ :=
        ihTail layout next resultSlot flag middleTarget regular bounded middleMatches.1 avoids
          fresh resultFlag copySafe middleHeap middleMatches.2
      refine ⟨t, ?_, property, finalHeap, finalMatches⟩
      convert Source.LocalMeasuredExec.seq firstRun
        (Source.LocalMeasuredExec.iteFalse (c := .var flag) (yes := .skip)
          trivial middleMatches.2 secondRun) using 1
      simp only [Expr.compile, List.length_singleton]
      omega
  | seqReturn cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨t, firstRun, property, finalHeap, finalMatches⟩ :=
        ih layout next resultSlot flag s regular bounded matched avoids fresh resultFlag
          copySafe represented flagZero
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq firstRun (.iteTrue (c := .var flag) trivial raised .skip),
        property, finalHeap, finalMatches⟩
  | @iteTrue Γ result depth condition yes no entry finish outcome test execution steps cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨t, body, property, finalHeap, finalMatches⟩ :=
        ih layout next resultSlot flag s regular bounded matched avoids fresh resultFlag
          copySafe represented flagZero
      have fits : Scalar.toNat .bool (condition.eval entry.locals) < 2 ^ w := by
        rw [test]
        exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)
      have decoded :=
        atomExpr_toNat layout condition .bool entry.locals s.regs s.mem hw matched fits
      have conditionTrue : s.eval (atomExpr layout condition .bool) ≠ 0 := by
        intro zero
        change (s.eval (atomExpr layout condition .bool)).toNat = _ at decoded
        rw [zero, test] at decoded
        exact Nat.zero_ne_one decoded
      refine ⟨t, ?_, property, finalHeap, finalMatches⟩
      convert Source.LocalMeasuredExec.iteTrue
        (atomExpr_readsBelow layout condition .bool s) conditionTrue body using 1
      simp only [atomExpr_compile_length]
      omega
  | @iteFalse Γ result depth condition yes no entry finish outcome test execution steps cost ih =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨t, body, property, finalHeap, finalMatches⟩ :=
        ih layout next resultSlot flag s regular bounded matched avoids fresh resultFlag
          copySafe represented flagZero
      have fits : Scalar.toNat .bool (condition.eval entry.locals) < 2 ^ w := by
        rw [test]
        exact Nat.two_pow_pos w
      have decoded :=
        atomExpr_toNat layout condition .bool entry.locals s.regs s.mem hw matched fits
      have conditionFalse : s.eval (atomExpr layout condition .bool) = 0 := by
        apply (Word.toNat_eq_zero_iff _).mp
        simpa only [test, Scalar.toNat] using decoded
      refine ⟨t, ?_, property, finalHeap, finalMatches⟩
      convert Source.LocalMeasuredExec.iteFalse
        (atomExpr_readsBelow layout condition .bool s) conditionFalse body using 1
      simp only [atomExpr_compile_length]
      omega
  | @ret Γ result depth value entry fits =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      let received :=
        s.setRegs (valueRegs result resultSlot) (valueWords placement (value.eval entry.locals))
      have writeResult := lowerReturn_measured (control := controlReg)
        (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
        layout resultSlot value entry.locals s hw matched fits copySafe
      have raiseFlag : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
          (.assign flag (.const 1)) 2 received (received.setReg flag 1) := .assign trivial
      refine ⟨received.setReg flag 1, .seq writeResult raiseFlag, ?_,
        (represented.setRegs _ _).setReg flag 1, ?_⟩
      · refine ⟨?_, Source.State.setReg_same received flag 1⟩
        rw [resultExprs_setReg_eval result resultSlot flag 1 received
          (flag_not_mem_valueRegs result resultSlot flag resultFlag)]
        exact resultExprs_setRegs_eval result resultSlot (value.eval entry.locals) s
      · intro separate
        have copied : layout.Matches placement entry.locals received.regs :=
          lowerReturn_matches layout resultSlot value entry.locals s matched separate
        intro τ v i
        exact RegisterMap.Matches.setReg_of_ne (entry := received) copied avoids 1 v i
  | @callReturn Γ result depth fn args body entry calleeFinish value finish outcome
      arguments callee execution calleeSteps bodySteps calleeCost bodyCost ihCallee ihBody =>
      intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
        represented flagZero
      obtain ⟨calleeTarget, invocation, calleeHeap⟩ :=
        lowerFunction_of_core (fn := fn) (args := args.eval entry.locals)
          (initialHeap := entry.heap) (calleeFinish := calleeFinish) (value := value)
          controlReg (fun calleeLayout calleeNext calleeResult calleeFlag
            calleeEntry regular bounded matched avoids fresh resultFlag copySafe represented zero => by
          obtain ⟨target, measured, property, finalHeap, _⟩ :=
            ihCallee calleeLayout calleeNext calleeResult calleeFlag calleeEntry
              regular bounded matched avoids fresh resultFlag copySafe represented zero
          exact ⟨target, measured, property, finalHeap⟩) arguments s represented
      obtain ⟨callRun, matching, preserved⟩ := lowerCall_measured_fresh
        (τ := signatures[fn].result) (value := value)
        layout args entry.locals s next hw matched arguments invocation
        (lowerProgram_lookup program fn)
        (by simp only [lowerFunc_results_length]) bounded callee.returned_fits
      obtain ⟨t, rest, property, finalHeap, finalMatches⟩ := ihBody
        (RegisterMap.extend layout signatures[fn].result next)
        (next + fieldCount signatures[fn].result) resultSlot flag _
        (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching (RegisterMap.Avoids.extend avoids fresh)
        (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
        (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
        (calleeHeap.setRegs _ _)
        ((preserved flag
          (flag_not_mem_valueRegs_of_lt signatures[fn].result next flag fresh)).trans flagZero)
      refine ⟨t, .seq callRun rest, ControlMatches.tail property, finalHeap, ?_⟩
      intro separate
      exact RegisterMap.Matches.tail (finalMatches (separate.extend
        (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

/-- Forget the conditional final-local correspondence without restricting
scalar result aliases or changing the original compiler interface. -/
theorem lowerCoreMeasured (cost : ExecutionCost execution steps) (controlReg : Nat)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
        ControlMatches layout placement resultSlot flag finish.locals outcome t ∧
        HeapRep placement heapLimit finish.heap t := by
  intro layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
    represented flagZero
  obtain ⟨t, measured, property, finalHeap, _⟩ := cost.lowerCoreMeasuredWithLocals controlReg hw
    layout next resultSlot flag s regular bounded matched avoids fresh resultFlag copySafe
      represented flagZero
  exact ⟨t, measured, property, finalHeap⟩

/-- A returned generic statement pays five wrapper steps and retains its real
final heap. A supplied normal continuation is bypassed. -/
theorem lowerReturnedMeasured {value : Value result}
    {execution : RealizedExec program w depth stmt entry finish (.returned value)}
    (cost : ExecutionCost execution steps) (controlReg : Nat) (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt),
      RegisterMap.Regular layout → layout.Bounded next → layout.Matches placement entry.locals s.regs →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s →
      ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) (steps + 5) s t ∧
        (resultExprs result resultSlot).map t.eval = valueWords placement value ∧
        HeapRep placement heapLimit finish.heap t :=
  lowerReturned_of_core controlReg hw (cost.lowerCoreMeasured controlReg hw)

/-- The core observation yields the actual function body count and final heap;
result-copy separation is established automatically. -/
theorem functionMeasuredExec {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {initialHeap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    {execution : RealizedExec program w depth (program.body fn)
      ⟨args, initialHeap⟩ finish (.returned value)}
    (cost : ExecutionCost execution steps) (controlReg : Nat) (hw : 0 < w)
    (arguments : EnvFits w args) (s : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap s) :
    ∃ t, Source.FunctionMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (lowerFunc program fn) (envWords placement args) (steps + 2) s
        (valueWords placement value) t ∧ HeapRep placement heapLimit finish.heap t :=
  lowerFunction_of_core controlReg (cost.lowerCoreMeasured controlReg hw) arguments s represented

end ExecutionCost

end Ram.LanguageCompiler
