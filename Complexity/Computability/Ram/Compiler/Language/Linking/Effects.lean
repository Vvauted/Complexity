/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Effects
import Complexity.Language.Linking.Basic

/-!
# Read-only source effects through actual program embeddings

Whole-signature transport and call renaming preserve the existing
`NoHeapWrites` condition. A mapped callee uses its actual renamed source body;
the result neither assumes termination nor changes its instructions.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Changing only a statement's complete signature leaves its effects intact. -/
@[simp] theorem noHeapWrites_cast {signatures : List Signature}
    {first second : Signature} (same : first = second)
    (statement : Complexity.Language.Stmt signatures first.params first.result) :
    NoHeapWrites (cast (congrArg
      (fun signature => Complexity.Language.Stmt signatures signature.params signature.result)
      same) statement) ↔ NoHeapWrites statement := by
  cases same
  rfl

/-- A typed call has the same direct effects as its continuation. Its actual
callee's effects remain the separate program-wide premise. -/
@[simp] theorem noHeapWrites_callOfEq {signatures : List Signature} {Γ : List Ty}
    {result : Ty} (fn : Fin signatures.length) {signature : Signature}
    (same : signatures[fn] = signature) (args : Args Γ signature.params)
    (continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result) :
    NoHeapWrites (Complexity.Language.Stmt.callOfEq fn same args continuation) ↔
      NoHeapWrites continuation := by
  cases same
  rfl

/-- Renaming call targets preserves a statement's direct read-only effects. -/
theorem NoHeapWrites.renameCalls {source target : List Signature}
    {Γ : List Ty} {result : Ty} {statement : Complexity.Language.Stmt source Γ result}
    (readOnly : NoHeapWrites statement) (map : SignatureMap source target) :
    NoHeapWrites (statement.renameCalls map) := by
  revert readOnly
  induction statement <;>
    simp_all [Complexity.Language.Stmt.renameCalls, NoHeapWrites, noHeapWrites_callOfEq]

/-- The actual mapped body inherits the original callee's read-only property. -/
theorem noHeapWrites_mapped_body {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) (fn : Fin source.length)
    (readOnly : NoHeapWrites (sourceProgram.body fn)) :
    NoHeapWrites (targetProgram.body (map.toFun fn)) := by
  have observed : NoHeapWrites (map.body targetProgram fn) := by
    rw [embedded fn]
    exact readOnly.renameCalls map
  exact (noHeapWrites_cast (map.signature_eq fn)
    (targetProgram.body (map.toFun fn))).mp observed

end Ram.LanguageCompiler
