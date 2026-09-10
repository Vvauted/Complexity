/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Basic
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost
import Complexity.Computability.Ram.Source.Linking

/-!
# Lowering through typed source program embeddings

Signature-preserving source call renaming lowers to the existing RAM call renaming.
The lowered operations, local registers, parameter fields and result expressions are otherwise
unchanged. The actual inferred local frame and compiler-derived call overhead are therefore
preserved; no instruction prices or state-conversion assumptions are introduced.

Source linking remains independent of RAM. This connection layer accepts any total target
index renaming agreeing with the typed map on source functions. Its cost consequence hides
that unobservable choice outside the source table.
-/

namespace Ram.Stmt

/-- Renaming callees changes no register read, write or call operand. -/
@[simp] theorem regBound_renameCalls (statement : Stmt) (ρ : Nat → Nat) :
    (statement.renameCalls ρ).regBound = statement.regBound := by
  induction statement <;> simp_all only [renameCalls, regBound]

end Ram.Stmt

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem copyFields_renameCalls (dst : Reg) (expressions : List Expr) (ρ : Nat → Nat) :
    (copyFields dst expressions).renameCalls ρ = copyFields dst expressions := by
  induction expressions generalizing dst with
  | nil => rfl
  | cons expression rest ih =>
      cases rest with
      | nil => rfl
      | cons next rest => simp only [copyFields, Ram.Stmt.renameCalls, ih]

private theorem lowerPrim_renameCalls {Γ : List Ty} {τ : Ty} (layout : RegisterMap Γ)
    (dst : Reg) (value : Prim Γ τ) (ρ : Nat → Nat) :
    (lowerPrim layout dst value).renameCalls ρ = lowerPrim layout dst value := by
  cases τ <;> cases value <;>
    simp only [lowerPrim, Ram.Stmt.renameCalls, copyFields_renameCalls]

private theorem lowerAlloc_renameCalls {Γ : List Ty} {kind : CellTy}
    (layout : RegisterMap Γ) (next : Reg) (length : Atom Γ .nat)
    (initial : Atom Γ kind.toTy) (ρ : Nat → Nat) :
    (lowerAlloc layout next length initial).renameCalls ρ =
      lowerAlloc layout next length initial := by
  simp only [lowerAlloc, Source.Arena.Registers.allocate, Source.Arena.Registers.prepare,
    Source.Arena.Registers.fill, Source.Arena.Registers.fillBody, Ram.Stmt.renameCalls]

private theorem lowerStmtCore_callOfEq {signatures : List Signature}
    {Γ : List Ty} {result : Ty} (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (fn : Fin signatures.length) {signature : Signature} (same : signatures[fn] = signature)
    (args : Args Γ signature.params)
    (continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result) :
    lowerStmtCore layout next resultSlot flag
      (Complexity.Language.Stmt.callOfEq fn same args continuation) =
      .seq (.call (valueRegs signature.result next) fn.val (argsExprs layout args))
        (lowerStmtCore (RegisterMap.extend layout signature.result next)
          (next + fieldCount signature.result) resultSlot flag continuation) := by
  cases same
  rfl

/-- Lowering a typed call renaming gives exactly the existing RAM call renaming.
All layouts and emitted non-call operations remain the same. -/
theorem lowerStmtCore_renameCalls {source target : List Signature}
    (map : SignatureMap source target) (ρ : Nat → Nat)
    (agrees : ∀ fn : Fin source.length, ρ fn.val = (map.toFun fn).val)
    {Γ : List Ty} {result : Ty} (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (statement : Complexity.Language.Stmt source Γ result) :
    lowerStmtCore layout next resultSlot flag (statement.renameCalls map) =
      (lowerStmtCore layout next resultSlot flag statement).renameCalls ρ := by
  induction statement generalizing next resultSlot flag <;>
    simp_all only [Complexity.Language.Stmt.renameCalls, lowerStmtCore_callOfEq,
      lowerStmtCore, Ram.Stmt.renameCalls, lowerAssign, lowerPrim_renameCalls,
      lowerRead, lowerWrite, lowerSlice, lowerAlloc_renameCalls, lowerReturn, copyFields_renameCalls]

private theorem lowerBody_cast {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {signature : Signature} (same : signatures[fn] = signature) :
    lowerBody program fn =
      let resultSlot := contextSize signature.params
      let next := resultSlot + fieldCount signature.result
      let flag := returnFlag signature.result next resultSlot
      .seq (.assign flag (.const 0))
        (lowerStmtCore (parameterMap signature.params) (flag + 1) resultSlot flag
          (cast (congrArg
            (fun signature => Complexity.Language.Stmt signatures
              signature.params signature.result) same) (program.body fn))) := by
  cases same
  rfl

/-- An embedded source function lowers to the renamed original body, including its
return-flag initialization and all actual call operands. -/
theorem lowerBody_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (ρ : Nat → Nat)
    (agrees : ∀ fn : Fin source.length, ρ fn.val = (map.toFun fn).val)
    (fn : Fin source.length) :
    lowerBody targetProgram (map.toFun fn) = (lowerBody sourceProgram fn).renameCalls ρ := by
  rw [lowerBody_cast targetProgram (map.toFun fn) (map.signature_eq fn)]
  change Ram.Stmt.seq _ (lowerStmtCore _ _ _ _ (map.body targetProgram fn)) = _
  rw [embedded, lowerStmtCore_renameCalls map ρ agrees]
  rfl

/-- The complete lowered function is relocated by the existing RAM linker. Its
parameters, inferred local frame and ordered result expressions are unchanged. -/
theorem lowerFunc_renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (ρ : Nat → Nat)
    (agrees : ∀ fn : Fin source.length, ρ fn.val = (map.toFun fn).val)
    (fn : Fin source.length) :
    lowerFunc targetProgram (map.toFun fn) = (lowerFunc sourceProgram fn).renameCalls ρ := by
  simp only [lowerFunc, Func.renameCalls, lowerBody_renameCalls embedded ρ agrees fn,
    Ram.Stmt.regBound_renameCalls, map.signature_eq fn]

private def totalIndexMap {source target : List Signature} (map : SignatureMap source target)
    (index : Nat) : Nat :=
  if bound : index < source.length then (map.toFun ⟨index, bound⟩).val else index

private theorem totalIndexMap_agrees {source target : List Signature}
    (map : SignatureMap source target) (fn : Fin source.length) :
    totalIndexMap map fn.val = (map.toFun fn).val := by
  simp only [totalIndexMap, dif_pos fn.isLt]

/-- Source function-table embedding preserves the actual lowered parameter count. -/
theorem lowerFunc_params_embeds {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (lowerFunc targetProgram (map.toFun fn)).params = (lowerFunc sourceProgram fn).params := by
  rw [lowerFunc_renameCalls embedded (totalIndexMap map) (totalIndexMap_agrees map) fn]
  rfl

/-- Source function-table embedding preserves the actual inferred local frame. -/
theorem lowerFunc_locals_embeds {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (lowerFunc targetProgram (map.toFun fn)).locals = (lowerFunc sourceProgram fn).locals := by
  rw [lowerFunc_renameCalls embedded (totalIndexMap map) (totalIndexMap_agrees map) fn]
  rfl

/-- Source function-table embedding preserves the actual ordered return expressions. -/
theorem lowerFunc_results_embeds {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) :
    (lowerFunc targetProgram (map.toFun fn)).results = (lowerFunc sourceProgram fn).results := by
  rw [lowerFunc_renameCalls embedded (totalIndexMap map) (totalIndexMap_agrees map) fn]
  rfl

/-- An imported function keeps its compiler-derived call overhead for the same body count.
This follows from the actual parameter fields, return code and inferred local frame. -/
theorem callCost_embeds {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length) (steps : Nat) :
    callCost targetProgram (map.toFun fn) steps = callCost sourceProgram fn steps := by
  simp only [callCost, LocalCompiler.Function.callSteps_eq,
    lowerFunc_params_embeds embedded fn, lowerFunc_locals_embeds embedded fn,
    lowerFunc_results_embeds embedded fn]

end Ram.LanguageCompiler
