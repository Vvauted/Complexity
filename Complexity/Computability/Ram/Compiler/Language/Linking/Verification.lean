/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Linking.ExecutionCost

/-!
# Reusing function resource contracts through source imports

Actual-body embeddings preserve function realizability and uniform body-cost
bounds. The public rules transport only the argument predicates across the
signature equality. They retain the same word width and call-nesting capacity;
the final runner still requires code and stack capacity for the target program.

Correctness contracts live independently in `Language.Linking.Verification`.
No proposed instruction budget is used to obtain successful execution.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

private theorem functionRealizable_cast_iff {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w depth : Nat)
    (fn : Fin signatures.length) {signature : Signature}
    (same : signatures[fn] = signature) (pre : Env signature.params → Heap → Prop) :
    FunctionRealizable program w depth fn
        (cast (congrArg (fun signature => Env signature.params → Heap → Prop) same.symm) pre) ↔
      ∀ args heap, pre args heap → ∃ finish value,
        RealizedExec program w depth
          (cast (congrArg (fun signature => Complexity.Language.Stmt signatures
            signature.params signature.result) same) (program.body fn))
          ⟨args, heap⟩ finish (.returned value) := by
  cases same
  rfl

namespace FunctionRealizable

/-- Imported function bodies have exactly the original range and call-nesting
requirements, expressed using their signature-preserving argument transport. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {w depth : Nat}
    {fn : Fin source.length} {pre : Env source[fn].params → Heap → Prop} :
    FunctionRealizable targetProgram w depth (map.toFun fn)
        (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
          (map.signature_eq fn).symm) pre) ↔
      FunctionRealizable sourceProgram w depth fn pre := by
  rw [functionRealizable_cast_iff targetProgram w depth (map.toFun fn) (map.signature_eq fn)]
  change (∀ args heap, pre args heap → ∃ finish value,
    RealizedExec targetProgram w depth (map.body targetProgram fn)
      ⟨args, heap⟩ finish (.returned value)) ↔ _
  simp only [embedded fn, RealizedExec.renameCalls_iff embedded, FunctionRealizable]

/-- Reuse a library's realizability proof without reopening its loops or recursion. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {w depth : Nat}
    {fn : Fin source.length} {pre : Env source[fn].params → Heap → Prop}
    (realizable : FunctionRealizable sourceProgram w depth fn pre) :
    FunctionRealizable targetProgram w depth (map.toFun fn)
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
        (map.signature_eq fn).symm) pre) :=
  (renameCalls_iff embedded).mpr realizable

end FunctionRealizable

private theorem functionCostBound_cast_iff {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    {signature : Signature} (same : signatures[fn] = signature)
    (pre : Env signature.params → Heap → Prop) (bound : Env signature.params → Heap → Nat) :
    FunctionCostBound program fn
        (cast (congrArg (fun signature => Env signature.params → Heap → Prop) same.symm) pre)
        (cast (congrArg (fun signature => Env signature.params → Heap → Nat) same.symm) bound) ↔
      ∀ args heap, pre args heap → ∀ {w depth finish value}
        (execution : RealizedExec program w depth
          (cast (congrArg (fun signature => Complexity.Language.Stmt signatures
            signature.params signature.result) same) (program.body fn))
          ⟨args, heap⟩ finish (.returned value))
        {steps}, ExecutionCost execution steps → steps + 2 ≤ bound args heap := by
  cases same
  rfl

namespace FunctionCostBound

/-- Reuse the original body's uniform cost bound for every realized execution
of the imported function, retaining the actual compiler's function wrapper. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {pre : Env source[fn].params → Heap → Prop} {bound : Env source[fn].params → Heap → Nat}
    (bounded : FunctionCostBound sourceProgram fn pre bound) :
    FunctionCostBound targetProgram (map.toFun fn)
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
        (map.signature_eq fn).symm) pre)
      (cast (congrArg (fun signature => Env signature.params → Heap → Nat)
        (map.signature_eq fn).symm) bound) := by
  rw [functionCostBound_cast_iff targetProgram (map.toFun fn) (map.signature_eq fn)]
  change ∀ args heap, pre args heap → ∀ {w depth finish value}
    (execution : RealizedExec targetProgram w depth (map.body targetProgram fn)
      ⟨args, heap⟩ finish (.returned value))
    {steps}, ExecutionCost execution steps → steps + 2 ≤ bound args heap
  rw [embedded fn]
  intro args heap hpre w depth finish value execution steps cost
  exact bounded args heap hpre (execution.of_renameCalls embedded) (cost.of_renameCalls embedded)

/-- The uniform function bound is equivalent across the actual-body embedding;
linking does not discard any successful execution or change its body count. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {pre : Env source[fn].params → Heap → Prop} {bound : Env source[fn].params → Heap → Nat} :
    FunctionCostBound targetProgram (map.toFun fn)
        (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
          (map.signature_eq fn).symm) pre)
        (cast (congrArg (fun signature => Env signature.params → Heap → Nat)
          (map.signature_eq fn).symm) bound) ↔
      FunctionCostBound sourceProgram fn pre bound := by
  refine ⟨?_, renameCalls embedded⟩
  intro bounded
  rw [functionCostBound_cast_iff targetProgram (map.toFun fn) (map.signature_eq fn)] at bounded
  change (∀ args heap, pre args heap → ∀ {w depth finish value}
    (execution : RealizedExec targetProgram w depth (map.body targetProgram fn)
      ⟨args, heap⟩ finish (.returned value))
    {steps}, ExecutionCost execution steps → steps + 2 ≤ bound args heap) at bounded
  rw [embedded fn] at bounded
  intro args heap hpre w depth finish value execution steps cost
  exact bounded args heap hpre (execution.renameCalls embedded) (cost.renameCalls embedded)

end FunctionCostBound

end Ram.LanguageCompiler
