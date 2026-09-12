/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Map
import Complexity.Language.Linking.Extension
import Complexity.Language.Linking.Verification

/-!
# A callable buffer map retaining its actual scalar implementation

`Buffer.Map.program` adds one allocating map entry to an existing source program.
The original table is retained through `Program.extend`, including the original
callee's loops, recursion and internal calls. The added body calls the relocated
scalar entry; it does not inline that body or accept a native function as code.

The mathematical mapper appears only in `Contract` and the correctness theorem.
The latter reuses the generic traversal proof and the original callee contract,
returning native `Array.map` contents in fresh storage while preserving all old
contents observations. The initializer is an actual argument used by allocation;
it does not affect the completely overwritten result. Word ranges, capacity and
instruction bounds remain separate compilation obligations.
-/

namespace Complexity.Language.Buffer.Map

variable {signatures : List Signature} {inputKind outputKind : CellTy}

/-- The allocating map takes a source view and an output-cell initializer. -/
def mapSignature (inputKind outputKind : CellTy) : Signature :=
  ⟨[.buffer inputKind, outputKind.toTy], .buffer outputKind⟩

/-- Original functions follow the single newly added map entry. -/
def calleeMap (inputKind outputKind : CellTy) (signatures : List Signature) :
    SignatureMap signatures (mapSignature inputKind outputKind :: signatures) :=
  SignatureMap.appendRight [mapSignature inputKind outputKind] signatures

/-- The new callable map occupies the first function-table position. -/
def entry (inputKind outputKind : CellTy) (signatures : List Signature) :
    Fin (mapSignature inputKind outputKind :: signatures).length :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- The selected original scalar entry in the extended function table. -/
def calleeEntry (inputKind outputKind : CellTy) (fn : Fin signatures.length) :
    Fin (mapSignature inputKind outputKind :: signatures).length :=
  (calleeMap inputKind outputKind signatures).toFun fn

@[simp] theorem entry_signature :
    (mapSignature inputKind outputKind :: signatures)[entry inputKind outputKind signatures] =
      mapSignature inputKind outputKind := rfl

@[simp] theorem calleeEntry_val (fn : Fin signatures.length) :
    (calleeEntry inputKind outputKind fn).val = 1 + fn.val := rfl

/-- Relocation retains the selected mapper's complete parameter/result type. -/
theorem callee_signature {fn : Fin signatures.length}
    (same : signatures[fn] = signature inputKind outputKind) :
    (mapSignature inputKind outputKind :: signatures)[calleeEntry inputKind outputKind fn] =
      signature inputKind outputKind :=
  ((calleeMap inputKind outputKind signatures).signature_eq fn).trans same

private def addedBody (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    (index : Fin [mapSignature inputKind outputKind].length) :
    Stmt (mapSignature inputKind outputKind :: signatures)
      [mapSignature inputKind outputKind][index].params
      [mapSignature inputKind outputKind][index].result := by
  have indexEq : index = ⟨0, Nat.zero_lt_one⟩ := by
    apply Fin.ext
    exact Nat.lt_one_iff.mp index.isLt
  subst index
  exact body (calleeEntry inputKind outputKind fn) (callee_signature same)

/-- Add one actual allocating traversal, retaining every original implementation.
Only the function index and its checked signature select the runtime mapper. -/
def program (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind) :
    Program (mapSignature inputKind outputKind :: signatures) :=
  source.extend [mapSignature inputKind outputKind] (addedBody fn same)

/-- The map entry is exactly the shared allocating source body with a real call
to the relocated scalar function. -/
theorem program_body (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind) :
    (program source fn same).body (entry inputKind outputKind signatures) =
      body (calleeEntry inputKind outputKind fn) (callee_signature same) := by
  simpa only [SignatureMap.body, SignatureMap.appendLeft, addedBody, cast_eq] using
    source.extend_body [mapSignature inputKind outputKind] (addedBody fn same)
      ⟨0, Nat.zero_lt_one⟩

/-- Every original function retains its body and actual renamed call graph. -/
theorem program_embeds (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind) :
    source.Embeds (calleeMap inputKind outputKind signatures) (program source fn same) :=
  source.embeds_extend [mapSignature inputKind outputKind] (addedBody fn same)

/-- Reuse a scalar mapper contract through any actual source-table embedding.
The mathematical result and the relation on the two actual heaps are unchanged. -/
theorem Contract.renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target} {fn : Fin source.length}
    {same : source[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind}
    (callee : Contract sourceProgram fn same f)
    (embedded : sourceProgram.Embeds map targetProgram) :
    Contract targetProgram (map.toFun fn) ((map.signature_eq fn).trans same) f := by
  simpa only [Contract, cast_cast] using FunctionTotal.renameCalls embedded callee

private theorem invocationOfEq {source : Program signatures} {fn : Fin signatures.length}
    {selected : Signature} (same : signatures[fn] = selected)
    {pre : Env selected.params → Heap → Prop}
    {post : Env selected.params → Heap → Value selected.result → Heap → Prop}
    (callee : FunctionTotal source fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm) post))
    (args : Env selected.params) (heap : Heap) (input : pre args heap) :
    ∃ finish value,
      Exec source
        (cast (congrArg (fun s => Stmt signatures s.params s.result) same) (source.body fn))
        ⟨args, heap⟩ finish (.returned value) ∧ post args heap value finish.heap := by
  cases same
  exact callee args heap input

/-- Invoke the actual scalar body at an ordinary cell value. Signature transport
does not change its source execution, returned scalar or actual final heap. -/
theorem Contract.invocation {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract source fn same f)
    (value : CellValue inputKind) (heap : Heap) :
    ∃ finish returned,
      Exec source
        (cast (congrArg (fun s => Stmt signatures s.params s.result) same) (source.body fn))
        ⟨Env.cons (inputKind.toValue value) Env.empty, heap⟩ finish (.returned returned) ∧
      returned = outputKind.toValue (f value) ∧ PreservesContents heap finish.heap := by
  simpa only [signature, Env.head_cons, CellTy.ofValue_toValue] using
    invocationOfEq same callee (Env.cons (inputKind.toValue value) Env.empty) heap trivial

/-- The mapper contract describes any actual successful invocation, not only
the execution witness chosen by its termination proof. -/
theorem Contract.postcondition {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract source fn same f)
    {value : CellValue inputKind} {heap : Heap}
    {finish : State [inputKind.toTy]} {returned : Value outputKind.toTy}
    (execution : Exec source
      (cast (congrArg (fun s => Stmt signatures s.params s.result) same) (source.body fn))
      ⟨Env.cons (inputKind.toValue value) Env.empty, heap⟩ finish (.returned returned)) :
    returned = outputKind.toValue (f value) ∧ PreservesContents heap finish.heap := by
  obtain ⟨otherFinish, otherValue, invocation, property⟩ := callee.invocation value heap
  obtain ⟨rfl, sameControl⟩ := invocation.deterministic execution
  cases Control.returned.inj sameControl
  exact property

/-- The actual relocated mapper reuses the supplied original function contract. -/
theorem callee_contract (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract source fn same f) :
    Contract (program source fn same) (calleeEntry inputKind outputKind fn)
      (callee_signature same) f :=
  callee.renameCalls (program_embeds source fn same)

/-- The callable entry returns native mapped contents in fresh retained storage.
Its correctness follows from the generic map proof, without repeating a loop
invariant or the scalar implementation's termination proof. -/
theorem program_total {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract source fn same f)
    (input : Array (CellValue inputKind)) :
    FunctionTotal (program source fn same) (entry inputKind outputKind signatures)
      (fun args heap => args.head.Contents heap input)
      (fun _ heap target finish => target.Contents finish (input.map f) ∧
        target.object = heap.objects.size ∧ PreservesContents heap finish) := by
  apply FunctionTotal.of_wp
  refine (Env.forall_cons (τ := .buffer inputKind) (Γ := [outputKind.toTy]) _).mpr ?_
  intro sourceBuffer
  refine (Env.forall_cons (τ := outputKind.toTy) (Γ := []) _).mpr ?_
  intro initial
  refine (Env.forall_nil _).mpr ?_
  intro heap observed
  rw [program_body]
  simpa only [CellTy.toValue_ofValue] using
    body_total (callee_contract source fn same callee) sourceBuffer input
      (outputKind.ofValue initial) heap observed

end Complexity.Language.Buffer.Map
