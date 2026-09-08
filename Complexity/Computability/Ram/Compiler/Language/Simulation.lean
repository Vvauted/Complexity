/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Values
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Computability.Ram.Verification.Total

/-!
# Simulation of independent scalar source executions

The proof follows a source execution, not an evaluation of its compiled syntax.
Normal completion runs the supplied continuation with the outer lexical values
still represented. A source return bypasses that continuation and exposes the
actual encoded result. Calls execute the selected lowered function and restore
caller locals using the existing RAM calling convention.

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

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Env Γ} {control : Control result}

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
        (lowerStmt layout next resultSlot stmt continuation) post s := by
  induction execution with
  | skip entry =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      exact normal rfl s matched
  | @letPrim Γ τ result depth value body entry finish control fits execution ih =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      have first := lowerPrim_safe (program := lowerProgram program)
        (heapLimit := heapLimit) (depth := depth) layout next value entry s hw matched fits
      have matching : RegisterMap.Matches (RegisterMap.extend layout τ next)
          (Env.cons (value.eval entry) entry)
          (s.setRegs (valueRegs τ next) (valueWords w (value.eval entry))).regs :=
        lowerPrim_matches layout next value entry s hw matched fits bounded
      obtain ⟨t, rest, property⟩ := ih (RegisterMap.extend layout τ next)
        (next + fieldCount τ) resultSlot _ continuation post
        (RegisterMap.extend_bounded bounded) matching
        (fun h t ht => normal h t ht.tail) returned
      exact ⟨t, .seq first rest, property⟩
  | @seqNormal Γ result depth first second entry middle finish control head tail ihHead ihTail =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      exact ihHead layout next resultSlot s
        (lowerStmt layout next resultSlot second continuation) post bounded matched
        (fun _ t ht => ihTail layout next resultSlot t continuation post bounded ht
          normal returned)
        (fun value impossible => nomatch impossible)
  | seqReturn head ih =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      exact ih layout next resultSlot s _ post bounded matched
        (fun impossible => nomatch impossible) returned
  | @iteTrue Γ result depth condition yes no entry finish control test body ih =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      obtain ⟨t, execution, property⟩ :=
        ih layout next resultSlot s continuation post bounded matched normal returned
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
      intro layout next resultSlot s continuation post bounded matched normal returned
      obtain ⟨t, execution, property⟩ :=
        ih layout next resultSlot s continuation post bounded matched normal returned
      have fits : valueToNat (condition.eval entry) < 2 ^ w := by
        rw [test]
        exact Nat.two_pow_pos w
      have decoded := atomExpr_toNat layout condition .bool entry s.regs s.mem hw matched fits
      have conditionFalse : s.eval (atomExpr layout condition .bool) = 0 := by
        apply (Word.toNat_eq_zero_iff _).mp
        simpa only [test, valueToNat] using decoded
      exact ⟨t, .iteFalse (atomExpr_readsBelow layout condition .bool s) conditionFalse execution,
        property⟩
  | ret value entry fits =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      refine ⟨_, lowerReturn_safe layout resultSlot value entry s hw matched
        (fun _ => fits), ?_⟩
      exact returned _ rfl _ (resultExprs_setRegs_eval _ resultSlot (value.eval entry) s)
  | @callReturn Γ result depth fn args body entry calleeFinish value finish control
      arguments callee execution ihCallee ihBody =>
      intro layout next resultSlot s continuation post bounded matched normal returned
      have encoded := argsExprs_eval layout args entry s hw matched arguments
      obtain ⟨calleeTarget, calleeRun, calleeResult⟩ :=
        ihCallee (parameterMap signatures[fn].params)
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
      obtain ⟨t, rest, property⟩ := ihBody
        (RegisterMap.extend layout signatures[fn].result next)
        (next + fieldCount signatures[fn].result) resultSlot _ continuation post
        (RegisterMap.extend_bounded bounded) matching
        (fun h t ht => normal h t ht.tail) returned
      exact ⟨t, .seq callRun rest, property⟩

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
