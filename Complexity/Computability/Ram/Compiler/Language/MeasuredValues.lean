/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CodeSize
import Complexity.Computability.Ram.Compiler.Language.Values
import Complexity.Computability.Ram.Compiler.Local.Function
import Complexity.Computability.Ram.Source.Function.Time

/-!
# Exact execution counts for lowered values and calls

Primitive bindings and return materialization are straight-line fragments, so
their existing safe executions have the exact lengths of their emitted code.
The endpoints remain the actual encoded fields established by the value
simulation; no time budget or additional representation condition is required.

An internal typed call materializes one instruction per argument field. Its
complete count therefore agrees with the existing function-call count, including
the actual callee frame, result expressions and receivers. The canonical control
register boundary used in that count changes no instruction length.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {control : Nat}

/-- Count the same primitive execution at its exact emitted size. -/
theorem lowerPrim_measured (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : PrimFits w env prim) :
    Source.LocalMeasuredExec control program heapLimit depth (lowerPrim layout dst prim)
      (primCodeSize prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords w (prim.eval env))) := by
  rw [← lowerPrim_stmtSize control (LocalCompiler.calleeLocals program) layout dst prim]
  have execution := lowerPrim_safe layout dst prim env entry hw matched fits
    (program := program) (heapLimit := heapLimit) (depth := depth)
  cases τ with
  | nat | bool => exact execution.assign_localMeasured control
  | unit => exact .skip

/-- Count actual result-field materialization. Unit performs no assignment. -/
theorem lowerReturn_measured (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs)
    (fits : ∀ i : Fin (fieldCount τ), valueField (atom.eval env) i < 2 ^ w) :
    Source.LocalMeasuredExec control program heapLimit depth (lowerReturn layout resultSlot atom)
      (2 * fieldCount τ) entry
      (entry.setRegs (valueRegs τ resultSlot) (valueWords w (atom.eval env))) := by
  rw [← lowerReturn_stmtSize control (LocalCompiler.calleeLocals program) layout resultSlot atom]
  have execution := lowerReturn_safe layout resultSlot atom env entry hw matched fits
    (program := program) (heapLimit := heapLimit) (depth := depth)
  cases τ with
  | nat | bool => exact execution.assign_localMeasured control
  | unit => exact .skip

/-- The actual typed call-site count agrees with the existing complete function
call count. Argument materialization and scratch relocation are justified by
the shared expression and ABI length theorems, not a separate numeric table. -/
theorem internalCall_steps_eq (control : Nat) (f : Func) (layout : RegisterMap Γ)
    (args : Args Γ params) (dsts : List Reg) (bodySteps : Nat)
    (arity : contextSize params = f.params) (resultCount : dsts.length = f.results.length) :
    (ABI.callPrefixLocals control f.locals (argsExprs layout args) 0).length + 1 + bodySteps +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length =
      LocalCompiler.Function.callSteps 0 f bodySteps := by
  have relocated :
      f.results.map (fun expr => (expr.compile (ABI.scratch control)).length) =
        f.results.map (fun expr => (expr.compile (ABI.scratch 0)).length) :=
    List.map_congr_left (fun expr _ => expr.compile_length_eq _ _)
  rw [LocalCompiler.Function.callSteps_eq, ABI.callPrefixLocals_length_eq,
    ABI.returnCodeResultsLocals_length, argsExprs_compile_lengths, argsExprs_length,
    arity, resultCount, relocated]
  omega

/-- Invoke a genuinely measured callee with the actual typed operands and
receive its real fields. The complete internal-call count uses the canonical
boundary, while the execution can use any reserved-register placement. -/
theorem lowerCall_measured (layout : RegisterMap Γ) (args : Args Γ params) (env : Env Γ)
    (entry : Source.State w) (dst : Reg) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : EnvFits w (args.eval env))
    (invocation : Source.FunctionMeasuredExec control program heapLimit depth f
      (envWords w (args.eval env)) bodySteps entry fields finish)
    (lookup : program[fn]? = some f) (resultCount : fieldCount τ = f.results.length) :
    Source.LocalMeasuredExec control program heapLimit (depth + 1)
      (.call (valueRegs τ dst) fn (argsExprs layout args))
      (LocalCompiler.Function.callSteps 0 f bodySteps)
      entry (finish.setRegs (valueRegs τ dst) fields) := by
  have arity : contextSize params = f.params := by
    simpa only [envWords_length] using invocation.1
  have receivers : (valueRegs τ dst).length = f.results.length := by
    simpa only [valueRegs_length] using resultCount
  have actual : Source.FunctionMeasuredExec control program heapLimit depth f
      ((argsExprs layout args).map entry.eval) bodySteps entry fields finish := by
    rw [argsExprs_eval layout args env entry hw matched fits]
    exact invocation
  have execution := actual.call lookup receivers (argsExprs_readsBelow layout args entry)
  rw [internalCall_steps_eq control f layout args (valueRegs τ dst) bodySteps arity receivers]
    at execution
  exact execution

/-- A measured call receiving a fresh lexical value extends the caller's
layout and preserves every register outside its actual receivers. The endpoint
retains the invocation's shared effects; only caller registers are restored.
Unit extends the lexical environment without allocating a result register. -/
theorem lowerCall_measured_fresh (layout : RegisterMap Γ) (args : Args Γ params) (env : Env Γ)
    (entry : Source.State w) (dst : Reg) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : EnvFits w (args.eval env))
    {value : Value τ}
    (invocation : Source.FunctionMeasuredExec control program heapLimit depth f
      (envWords w (args.eval env)) bodySteps entry (valueWords w value) finish)
    (lookup : program[fn]? = some f) (resultCount : fieldCount τ = f.results.length)
    (bounded : layout.Bounded dst)
    (resultFits : ∀ i : Fin (fieldCount τ), valueField value i < 2 ^ w) :
    let received := finish.setRegs (valueRegs τ dst) (valueWords w value)
    Source.LocalMeasuredExec control program heapLimit (depth + 1)
        (.call (valueRegs τ dst) fn (argsExprs layout args))
        (LocalCompiler.Function.callSteps 0 f bodySteps) entry received ∧
      RegisterMap.Matches (RegisterMap.extend layout τ dst) (Env.cons value env) received.regs ∧
      ∀ r, r ∉ valueRegs τ dst → received.regs r = entry.regs r := by
  dsimp only
  have registers : finish.regs = entry.regs := invocation.erase.regs_eq
  have restored : layout.Matches env finish.regs := by
    rw [registers]
    exact matched
  refine ⟨lowerCall_measured layout args env entry dst hw matched fits invocation lookup resultCount,
    restored.setRegs bounded value resultFits, ?_⟩
  intro r outside
  exact (Source.State.setRegs_ne finish _ _ r outside).trans (congrFun registers r)

end Ram.LanguageCompiler
