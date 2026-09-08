/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Control
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Computability.Ram.Verification.Total

/-!
# Simulation of independent scalar source executions

The proof follows a source execution, not an evaluation of its compiled syntax.
Normal completion preserves the represented lexical values and a zero return
flag. A source return writes its actual result and sets the flag; enclosing
sequences then skip their remaining statements. Calls execute the selected
lowered function and restore caller locals, including the caller's private
flag, using the existing RAM calling convention. Each source child appears
only once in the generated structured code.

The final function theorem combines this generic simulation with an independent
mathematical source contract. Algorithm-specific register layouts or lowering
proofs are not premises. Word ranges and call nesting remain explicit source
realization conditions; an instruction-time bound is not required.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem parameterMap_bodyBound (Γ : List Ty) (result : Ty) :
    RegisterMap.Bounded (parameterMap Γ) (contextSize Γ + fieldCount result) := by
  intro τ scalar v
  have bound : parameterMap Γ 0 scalar v < contextSize Γ := by
    simpa only [Nat.zero_add] using (parameterMap_bounded Γ 0 scalar v)
  exact Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)

/-- Normal completion retains the lexical environment; return exposes its
actual fields. The private flag distinguishes these outcomes without requiring
returned executions to preserve source bindings that are no longer live. -/
def ControlMatches (layout : RegisterMap Γ) (resultSlot flag : Reg) (finish : Env Γ)
    (control : Control result) (target : Source.State w) : Prop :=
  match control with
  | .normal => layout.Matches finish target.regs ∧ target.regs flag = 0
  | .returned value =>
      (resultExprs result resultSlot).map target.eval = valueWords w value ∧
        target.regs flag = 1
  | .fault _ => False

/-- Finishing a lexical binding drops only its temporary environment entry. -/
theorem ControlMatches.tail {layout : RegisterMap Γ} {finish : Env (τ :: Γ)}
    {target : Source.State w} {control : Control result}
    (matched : ControlMatches (RegisterMap.extend layout τ dst)
      resultSlot flag finish control target) :
    ControlMatches layout resultSlot flag finish.tail control target := by
  cases control with
  | normal => exact ⟨RegisterMap.Matches.tail matched.1, matched.2⟩
  | returned _ => exact matched
  | fault _ => exact matched

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Env Γ} {control : Control result}

/-- Initialize the private flag, run the core simulation, and dispatch the
normal continuation. The same wrapper serves an external statement and the
callee induction hypothesis, so calls do not require a separate lowering proof. -/
private theorem lower_of_core (hw : 0 < w)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout resultSlot flag finish control t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches entry s.regs →
      (control = .normal → ∀ t, layout.Matches finish t.regs →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords w value → post t) →
      Source.Verification.TotalWP (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) post s := by
  intro layout next resultSlot s continuation post bounded matched normal returned
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
  have flagInit : Source.SafeExec (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) s (s.setReg flag 0) := .assign trivial
  cases control with
  | normal =>
      obtain ⟨u, tail, property'⟩ := normal rfl t property.1
      exact ⟨u, .seq flagInit (.seq body (.iteFalse trivial property.2 tail)), property'⟩
  | returned value =>
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq flagInit (.seq body (.iteTrue trivial raised .skip)),
        returned value rfl t property.1⟩
  | fault _ => exact False.elim property

/-- Simulate the linear-size core with its private flag already initialized.
All register separation belongs to the compiler proof; `lower` chooses these
slots and discharges these conditions for callers automatically. -/
theorem lowerCore (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout resultSlot flag finish control t := by
  induction execution with
  | skip entry =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      exact ⟨s, .skip, matched, flagZero⟩
  | @letPrim Γ τ result depth value body entry finish control fits execution ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have first := lowerPrim_safe (program := lowerProgram program)
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
  | @seqNormal Γ result depth first second entry middle finish control head tail ihHead ihTail =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨middleTarget, firstRun, middleMatches⟩ :=
        ihHead layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, secondRun, property⟩ :=
        ihTail layout next resultSlot flag middleTarget bounded middleMatches.1 avoids
          fresh resultFlag middleMatches.2
      exact ⟨t, .seq firstRun (.iteFalse trivial middleMatches.2 secondRun), property⟩
  | seqReturn head ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, firstRun, property⟩ :=
        ih layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq firstRun (.iteTrue trivial raised .skip), property⟩
  | @iteTrue Γ result depth condition yes no entry finish control test body ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, execution, property⟩ :=
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
      exact ⟨t, .iteTrue (atomExpr_readsBelow layout condition .bool s) conditionTrue execution,
        property⟩
  | @iteFalse Γ result depth condition yes no entry finish control test body ih =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      obtain ⟨t, execution, property⟩ :=
        ih layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have fits : valueToNat (condition.eval entry) < 2 ^ w := by
        rw [test]
        exact Nat.two_pow_pos w
      have decoded := atomExpr_toNat layout condition .bool entry s.regs s.mem hw matched fits
      have conditionFalse : s.eval (atomExpr layout condition .bool) = 0 := by
        apply (Word.toNat_eq_zero_iff _).mp
        simpa only [test, valueToNat] using decoded
      exact ⟨t, .iteFalse (atomExpr_readsBelow layout condition .bool s) conditionFalse execution,
        property⟩
  | @ret Γ result depth value entry fits =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      let received := s.setRegs (valueRegs result resultSlot) (valueWords w (value.eval entry))
      have writeResult := lowerReturn_safe (program := lowerProgram program)
        (heapLimit := heapLimit) (depth := depth) layout resultSlot value entry s hw matched
        (fun _ => fits)
      have raiseFlag : Source.SafeExec (lowerProgram program) heapLimit depth
          (.assign flag (.const 1)) received (received.setReg flag 1) := .assign trivial
      refine ⟨received.setReg flag 1, .seq writeResult raiseFlag, ?_⟩
      refine ⟨?_, Source.State.setReg_same received flag 1⟩
      rw [resultExprs_setReg_eval result resultSlot flag 1 received
        (flag_not_mem_valueRegs result resultSlot flag resultFlag)]
      exact resultExprs_setRegs_eval result resultSlot (value.eval entry) s
  | @callReturn Γ result depth fn args body entry calleeFinish value finish control
      arguments callee execution ihCallee ihBody =>
      intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
      have encoded := argsExprs_eval layout args entry s hw matched arguments
      obtain ⟨calleeTarget, calleeRun, calleeResult⟩ :=
        lower_of_core hw ihCallee (parameterMap signatures[fn].params)
          (contextSize signatures[fn].params + fieldCount signatures[fn].result)
          (contextSize signatures[fn].params) (s.enter (envWords w (args.eval entry)))
          .skip (fun t => (lowerFunc program fn).results.map t.eval = valueWords w value)
          (parameterMap_bodyBound _ _) (parameterMap_matches_enter s _ arguments)
          (fun impossible => nomatch impossible)
          (fun value' same t ht => by cases Control.returned.inj same; exact ht)
      have invocation : Source.FunctionExec (lowerProgram program) heapLimit depth
          (lowerFunc program fn) ((argsExprs layout args).map s.eval) s
          (valueWords w value) (s.restore calleeTarget) := by
        rw [encoded]
        exact ⟨by simp, (lowerFunc_wellFormed program fn).1, calleeTarget, calleeRun,
          resultExprs_readsBelow _ _ calleeTarget, calleeResult.symm, rfl⟩
      have callRun := invocation.call (dsts := valueRegs signatures[fn].result next)
        (lowerProgram_lookup program fn)
        (by simp only [valueRegs_length, lowerFunc_results_length])
        (argsExprs_readsBelow layout args s)
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

/-- Generic continuation simulation. Register preservation is needed only when
normal source completion reaches the continuation; a return supplies the actual
result fields instead. The target postcondition can therefore be chosen by a
caller without exposing a per-program register invariant. -/
theorem lower (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches entry s.regs →
      (control = .normal → ∀ t, layout.Matches finish t.regs →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords w value → post t) →
      Source.Verification.TotalWP (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) post s :=
  lower_of_core hw (execution.lowerCore hw)

/-- A returned source execution lowers to an invocation of the actual generated
function. Argument fields initialize its compact frame, and its declared result
expressions evaluate to the actual returned source value. -/
theorem functionExec {fn : Fin signatures.length}
    {args finish : Env signatures[fn].params} {value : Value signatures[fn].result}
    (execution : RealizedExec program w depth (program.body fn) args finish (.returned value))
    (hw : 0 < w) (arguments : EnvFits w args) (s : Source.State w) :
    ∃ t, Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
      (envWords w args) s (valueWords w value) t := by
  obtain ⟨callee, body, result⟩ := execution.lower hw
    (parameterMap signatures[fn].params)
    (contextSize signatures[fn].params + fieldCount signatures[fn].result)
    (contextSize signatures[fn].params) (s.enter (envWords w args)) .skip
    (fun t => (lowerFunc program fn).results.map t.eval = valueWords w value)
    (parameterMap_bodyBound _ _) (parameterMap_matches_enter s args arguments)
    (fun impossible => nomatch impossible)
    (fun value' same t ht => by cases Control.returned.inj same; exact ht)
  exact ⟨s.restore callee, by simp, (lowerFunc_wellFormed program fn).1,
    callee, body, resultExprs_readsBelow _ _ callee, result.symm, rfl⟩

end RealizedExec

namespace FunctionRealizable

/-- Transfer a separately proved mathematical contract to the generated function.
Realization supplies ranges and nesting; source determinism supplies the same
actual returned value to the existing mathematical postcondition. -/
theorem functionExec {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (arguments : EnvFits w args)
    (hfeasible : feasible args) (hpre : pre args) (s : Source.State w) :
    ∃ value t, Source.FunctionExec (lowerProgram program) heapLimit depth
      (lowerFunc program fn) (envWords w args) s (valueWords w value) t ∧ post args value := by
  obtain ⟨finish, value, execution⟩ := realizable args hfeasible
  obtain ⟨t, invocation⟩ := execution.functionExec hw arguments s
  exact ⟨value, t, invocation, specification.postcondition hpre execution.erase⟩

end FunctionRealizable

end Ram.LanguageCompiler
