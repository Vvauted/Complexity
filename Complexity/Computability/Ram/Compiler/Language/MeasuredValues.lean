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
variable {placement : Nat → Word w}

/-- Count the actual sequential copy, with its proved preservation of source
fields, rather than assigning a cost to a simultaneous-copy abstraction. -/
theorem copyAtom_measured (layout : RegisterMap Γ) (dst : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : ValueFits w (atom.eval env))
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    Source.LocalMeasuredExec control program heapLimit depth (copyFields dst (atomExprs layout atom))
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (copyFields dst (atomExprs layout atom))) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (atom.eval env))) := by
  have execution := copyFields_localMeasured entry dst (atomExprs layout atom)
    (atomExprs_readsBelow layout atom entry) (atomExprs_copySafe layout atom dst copySafe)
    (control := control) (program := program) (heapLimit := heapLimit) (depth := depth)
  rw [atomExprs_eval layout atom env entry hw matched fits] at execution
  simpa only [valueRegs, atomExprs_length] using execution

/-- A selected `some` branch copies only its actual payload into fresh lexical
fields. The count is the emitted copy size, including all descriptor words. -/
theorem copyOptionPayload_measured (layout : RegisterMap Γ) (dst : Reg)
    (value : Atom Γ (.option τ)) (env : Env Γ) (entry : Source.State w) (_hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    (selected : value.eval env = some payload) (payloadFits : ValueFits w payload)
    (bounded : layout.Bounded dst) :
    Source.LocalMeasuredExec control program heapLimit depth
      (copyFields dst (optionPayloadExprs layout value)) (2 * fieldCount τ) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement payload)) := by
  have execution := copyFields_localMeasured entry dst (optionPayloadExprs layout value)
    (optionPayloadExprs_readsBelow layout value entry)
    (optionPayloadExprs_copySafe layout value dst bounded)
    (control := control) (program := program) (heapLimit := heapLimit) (depth := depth)
  rw [optionPayloadExprs_eval layout value env entry matched selected payloadFits] at execution
  simpa only [copyFields_stmtSize, optionPayloadExprs_compile_lengths,
    optionPayloadExprs_length, valueRegs, Nat.two_mul] using execution

/-- Count the same primitive execution at its exact emitted size. -/
theorem lowerPrim_measured (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    Source.LocalMeasuredExec control program heapLimit depth (lowerPrim layout dst prim)
      (primCodeSize prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))) := by
  rw [← lowerPrim_stmtSize control (LocalCompiler.calleeLocals program) layout dst prim]
  have execution := lowerPrim_safe layout dst prim env entry hw matched fits copySafe
    (program := program) (heapLimit := heapLimit) (depth := depth)
  rw [lowerPrim_eq_copyFields] at execution ⊢
  exact copyFields_safe_localMeasured execution control

/-- Existing-variable assignment retains the primitive's actual emitted cost,
including every field of self-copies. It reuses the proved safe endpoint. -/
theorem lowerAssign_measured (layout : RegisterMap Γ) (target : Var Γ τ) (value : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env value)
    (regular : layout.Regular) :
    Source.LocalMeasuredExec control program heapLimit depth (lowerAssign layout target value)
      (primCodeSize value) entry
      (entry.setRegs (valueRegs τ (layout.base target)) (valueWords placement (value.eval env))) := by
  rw [← lowerAssign_stmtSize control (LocalCompiler.calleeLocals program) layout target value]
  have execution := lowerAssign_safe layout target value env entry hw matched fits regular
    (program := program) (heapLimit := heapLimit) (depth := depth)
  dsimp only [lowerAssign] at execution ⊢
  rw [lowerPrim_eq_copyFields] at execution ⊢
  exact copyFields_safe_localMeasured execution control

/-- Count actual result-field materialization. Unit performs no assignment. -/
theorem lowerReturn_measured (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env))
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount τ)) :
    Source.LocalMeasuredExec control program heapLimit depth (lowerReturn layout resultSlot atom)
      (2 * fieldCount τ) entry
      (entry.setRegs (valueRegs τ resultSlot) (valueWords placement (atom.eval env))) := by
  rw [← lowerReturn_stmtSize control (LocalCompiler.calleeLocals program) layout resultSlot atom]
  exact copyAtom_measured layout resultSlot atom env entry hw matched fits copySafe

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
    (matched : layout.Matches placement env entry.regs) (fits : EnvFits w (args.eval env))
    (invocation : Source.FunctionMeasuredExec control program heapLimit depth f
      (envWords placement (args.eval env)) bodySteps entry fields finish)
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
    (matched : layout.Matches placement env entry.regs) (fits : EnvFits w (args.eval env))
    {value : Value τ}
    (invocation : Source.FunctionMeasuredExec control program heapLimit depth f
      (envWords placement (args.eval env)) bodySteps entry (valueWords placement value) finish)
    (lookup : program[fn]? = some f) (resultCount : fieldCount τ = f.results.length)
    (bounded : layout.Bounded dst)
    (resultFits : ValueFits w value) :
    let received := finish.setRegs (valueRegs τ dst) (valueWords placement value)
    Source.LocalMeasuredExec control program heapLimit (depth + 1)
        (.call (valueRegs τ dst) fn (argsExprs layout args))
        (LocalCompiler.Function.callSteps 0 f bodySteps) entry received ∧
      RegisterMap.Matches (RegisterMap.extend layout τ dst) placement (Env.cons value env)
        received.regs ∧
      ∀ r, r ∉ valueRegs τ dst → received.regs r = entry.regs r := by
  dsimp only
  have registers : finish.regs = entry.regs := invocation.erase.regs_eq
  have restored : layout.Matches placement env finish.regs := by
    rw [registers]
    exact matched
  refine ⟨lowerCall_measured layout args env entry dst hw matched fits invocation lookup resultCount,
    restored.setRegs bounded value resultFits, ?_⟩
  intro r outside
  exact (Source.State.setRegs_ne finish _ _ r outside).trans (congrFun registers r)

private theorem store_localMeasured
    {address value : Expr} {entry finish : Source.State w}
    (execution : Source.SafeExec program heapLimit depth (.store address value) entry finish) :
    Source.LocalMeasuredExec control program heapLimit depth (.store address value)
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) (.store address value))
      entry finish := by
  cases execution with
  | store addressReads valueReads destination => exact .store addressReads valueReads destination

private theorem twoAssignments_localMeasured
    {firstDst secondDst : Reg} {firstValue secondValue : Expr} {entry finish : Source.State w}
    (execution : Source.SafeExec program heapLimit depth
      (.seq (.assign firstDst firstValue) (.assign secondDst secondValue)) entry finish) :
    Source.LocalMeasuredExec control program heapLimit depth
      (.seq (.assign firstDst firstValue) (.assign secondDst secondValue))
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.seq (.assign firstDst firstValue) (.assign secondDst secondValue))) entry finish := by
  cases execution with
  | seq first second =>
      simpa only [LocalCompiler.stmtSize_seq] using
        Source.LocalMeasuredExec.seq (first.assign_localMeasured control)
          (second.assign_localMeasured control)

/-- The same successful buffer read has the exact instruction count of its
actual load-and-assignment code, with its native cell and shared heap intact. -/
theorem lowerRead_measured (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (indexFits : ValueFits w (index.eval env))
    {cell : CellValue kind} (loaded : heap.read (buffer.eval env) (index.eval env) = .ok cell) :
    let received := entry.setRegs (valueRegs kind.toTy dst)
      (valueWords placement (kind.toValue cell))
    Source.LocalMeasuredExec control program heapLimit depth (lowerRead layout dst buffer index)
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (lowerRead layout dst buffer index)) entry received ∧
      HeapRep placement heapLimit heap received ∧ ValueFits w (kind.toValue cell) := by
  obtain ⟨execution, preserved, fits⟩ := lowerRead_safe layout dst buffer index env entry hw matched
    represented bufferFits indexFits loaded (program := program) (depth := depth)
  exact ⟨execution.assign_localMeasured control, preserved, fits⟩

/-- Count the real shared-heap store without changing its endpoint or repeating
the proof of native heap mutation. -/
theorem lowerWrite_measured (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap finish : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (indexFits : ValueFits w (index.eval env))
    (valueFits : ValueFits w (value.eval env))
    (written : heap.write (buffer.eval env) (index.eval env)
      (kind.ofValue (value.eval env)) = .ok finish) :
    let updated := entry.setMem
      (arrayAddr (bufferRef placement (buffer.eval env)).base (index.eval env))
      (cellWord w (kind.ofValue (value.eval env)))
    Source.LocalMeasuredExec control program heapLimit depth (lowerWrite layout buffer index value)
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (lowerWrite layout buffer index value)) entry updated ∧
      HeapRep placement heapLimit finish updated := by
  obtain ⟨execution, preserved⟩ := lowerWrite_safe layout buffer index value env entry hw matched
    represented bufferFits indexFits valueFits written (program := program) (depth := depth)
  exact ⟨store_localMeasured execution, preserved⟩

/-- Slice descriptors execute two sequential assignments. Their exact count
retains the established source-field preservation and actual represented heap. -/
theorem lowerSlice_measured (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (offset length : Atom Γ .nat) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (offsetFits : ValueFits w (offset.eval env))
    (lengthFits : ValueFits w (length.eval env)) (bounded : layout.Bounded dst)
    {view : Buffer kind}
    (sliced : (buffer.eval env).slice (offset.eval env) (length.eval env) = .ok view) :
    let received := entry.setRegs (valueRegs (.buffer kind) dst)
      (valueWords placement (τ := .buffer kind) view)
    Source.LocalMeasuredExec control program heapLimit depth (lowerSlice layout dst buffer offset length)
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (lowerSlice layout dst buffer offset length)) entry received ∧
      HeapRep placement heapLimit heap received ∧ ValueFits w (τ := .buffer kind) view := by
  obtain ⟨execution, preserved, fits⟩ := lowerSlice_safe layout dst buffer offset length env entry hw
    matched represented bufferFits offsetFits lengthFits bounded sliced
    (program := program) (depth := depth)
  exact ⟨twoAssignments_localMeasured execution, preserved, fits⟩

end Ram.LanguageCompiler
