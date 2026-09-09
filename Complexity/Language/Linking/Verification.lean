/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Reflection

/-!
# Function correctness contracts through typed source embeddings

A function's existing mathematical precondition and postcondition transfer to
its actual linked body. Whole-signature transport handles the parameter and
result types together; callers do not reconstruct environments or repeat the
correctness and termination proof. Initial and final heaps remain unchanged in
the contract. No machine representation or resource budget occurs in this layer.
-/

namespace Complexity.Language

namespace FunctionTotal

private theorem cast_iff {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) {signature : Signature}
    (same : signatures[fn] = signature)
    (pre : Env signature.params → Heap → Prop)
    (post : Env signature.params → Heap → Value signature.result → Heap → Prop) :
    FunctionTotal program fn
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun signature =>
        Env signature.params → Heap → Value signature.result → Heap → Prop) same.symm) post) ↔
      ∀ args heap, pre args heap → ∃ finish value,
        Exec program
          (cast (congrArg (fun signature => Stmt signatures signature.params signature.result)
            same) (program.body fn))
          ⟨args, heap⟩ finish (.returned value) ∧ post args heap value finish.heap := by
  cases same
  rfl

/-- Reuse an existing mathematical function contract after linking its actual
body, with the same pre-state, returned value and final-heap relation. -/
theorem renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {pre : Env source[fn].params → Heap → Prop}
    {post : Env source[fn].params → Heap → Value source[fn].result → Heap → Prop}
    (specification : FunctionTotal sourceProgram fn pre post) :
    FunctionTotal targetProgram (map.toFun fn)
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
        (map.signature_eq fn).symm) pre)
      (cast (congrArg (fun signature =>
        Env signature.params → Heap → Value signature.result → Heap → Prop)
        (map.signature_eq fn).symm) post) := by
  apply (cast_iff targetProgram (map.toFun fn) (map.signature_eq fn) pre post).mpr
  intro args heap input
  obtain ⟨finish, value, execution, property⟩ := specification args heap input
  refine ⟨finish, value, ?_, property⟩
  change Exec targetProgram (map.body targetProgram fn) _ _ _
  rw [embedded fn]
  exact execution.renameCalls embedded

/-- Reflect a linked function's transported contract without separately
assuming that the original function terminates. -/
theorem of_renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {pre : Env source[fn].params → Heap → Prop}
    {post : Env source[fn].params → Heap → Value source[fn].result → Heap → Prop}
    (specification : FunctionTotal targetProgram (map.toFun fn)
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
        (map.signature_eq fn).symm) pre)
      (cast (congrArg (fun signature =>
        Env signature.params → Heap → Value signature.result → Heap → Prop)
        (map.signature_eq fn).symm) post)) :
    FunctionTotal sourceProgram fn pre post := by
  have transported :=
    (cast_iff targetProgram (map.toFun fn) (map.signature_eq fn) pre post).mp specification
  intro args heap input
  obtain ⟨finish, value, execution, property⟩ := transported args heap input
  refine ⟨finish, value, ?_, property⟩
  change Exec targetProgram (map.body targetProgram fn) _ _ _ at execution
  rw [embedded fn] at execution
  exact execution.of_renameCalls embedded

/-- Whole-signature transport makes the linked and original function contracts
equivalent, including their actual successful termination and heap effects. -/
theorem renameCalls_iff {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {pre : Env source[fn].params → Heap → Prop}
    {post : Env source[fn].params → Heap → Value source[fn].result → Heap → Prop} :
    FunctionTotal targetProgram (map.toFun fn)
      (cast (congrArg (fun signature => Env signature.params → Heap → Prop)
        (map.signature_eq fn).symm) pre)
      (cast (congrArg (fun signature =>
        Env signature.params → Heap → Value signature.result → Heap → Prop)
        (map.signature_eq fn).symm) post) ↔
      FunctionTotal sourceProgram fn pre post :=
  ⟨of_renameCalls embedded, renameCalls embedded⟩

end FunctionTotal

end Complexity.Language
