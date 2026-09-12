/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Basic
import Complexity.Language.Linking.Extension
import Complexity.Language.Linking.Verification

/-!
# A callable list fold retaining its actual callback

`List.Fold.program` adds the shared list traversal to an existing source program.
The selected callback and every original function keep their implementations,
including recursive calls, through the existing typed program embedding.

The correctness contract relates the result to native `List.foldl`. The callback
may change the heap: the immutable list observation is preserved by source
execution, not by an additional whole-heap-unchanged callback assumption.
-/

namespace Complexity.Language.List.Fold

universe u

variable {signatures : List Signature} {accTy : Ty} {kind : CellTy}

/-- Original functions follow the single newly added fold entry. -/
def calleeMap (accTy : Ty) (kind : CellTy) (signatures : List Signature) :
    SignatureMap signatures (foldSignature accTy kind :: signatures) :=
  SignatureMap.appendRight [foldSignature accTy kind] signatures

/-- The new callable fold occupies the first function-table position. -/
def entry (accTy : Ty) (kind : CellTy) (signatures : List Signature) :
    Fin (foldSignature accTy kind :: signatures).length :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- The selected original callback in the extended function table. -/
def calleeEntry (accTy : Ty) (kind : CellTy) (fn : Fin signatures.length) :
    Fin (foldSignature accTy kind :: signatures).length :=
  (calleeMap accTy kind signatures).toFun fn

@[simp] theorem entry_signature :
    (foldSignature accTy kind :: signatures)[entry accTy kind signatures] =
      foldSignature accTy kind := rfl

@[simp] theorem calleeEntry_val (fn : Fin signatures.length) :
    (calleeEntry accTy kind fn).val = 1 + fn.val := rfl

/-- Relocation retains the selected callback's complete parameter/result type. -/
theorem callee_signature {fn : Fin signatures.length}
    (same : signatures[fn] = stepSignature accTy kind) :
    (foldSignature accTy kind :: signatures)[calleeEntry accTy kind fn] =
      stepSignature accTy kind :=
  ((calleeMap accTy kind signatures).signature_eq fn).trans same

private def addedBody (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind)
    (index : Fin [foldSignature accTy kind].length) :
    Stmt (foldSignature accTy kind :: signatures)
      [foldSignature accTy kind][index].params
      [foldSignature accTy kind][index].result := by
  have indexEq : index = ⟨0, Nat.zero_lt_one⟩ := by
    apply Fin.ext
    exact Nat.lt_one_iff.mp index.isLt
  subst index
  exact body (calleeEntry accTy kind fn) (callee_signature same)

/-- Add one actual traversal, retaining every original implementation. The
function index and its checked signature select the runtime callback. -/
def program (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    Program (foldSignature accTy kind :: signatures) :=
  source.extend [foldSignature accTy kind] (addedBody fn same)

/-- The fold entry is exactly the shared source traversal with a real call to
the relocated callback. -/
theorem program_body (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    (program source fn same).body (entry accTy kind signatures) =
      body (calleeEntry accTy kind fn) (callee_signature same) := by
  simpa only [SignatureMap.body, SignatureMap.appendLeft, addedBody, cast_eq] using
    source.extend_body [foldSignature accTy kind] (addedBody fn same)
      ⟨0, Nat.zero_lt_one⟩

/-- Every original function retains its body and actual renamed call graph. -/
theorem program_embeds (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    source.Embeds (calleeMap accTy kind signatures) (program source fn same) :=
  source.embeds_extend [foldSignature accTy kind] (addedBody fn same)

/-- The callback body observed at its declared step signature is the actual
renamed original body. Resource contracts may therefore use the same embedding. -/
theorem calleeBody_renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    (same : source[fn] = stepSignature accTy kind) :
    calleeBody targetProgram (map.toFun fn) ((map.signature_eq fn).trans same) =
      (calleeBody sourceProgram fn same).renameCalls map := by
  unfold calleeBody
  rw [Stmt.renameCalls_cast map same]
  simpa only [SignatureMap.body, cast_cast] using
    congrArg (fun statement : Stmt target source[fn].params source[fn].result =>
      cast (congrArg (fun signature => Stmt target signature.params signature.result)
        same) statement) (embedded fn)

/-- Reuse the complete represented callback contract through an actual
source-table embedding, with the same mathematical domain and heap effects. -/
theorem Contract.renameCalls {α : Type u} {R : Representation α accTy}
    {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target} {fn : Fin source.length}
    {same : source[fn] = stepSignature accTy kind}
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (callee : Contract sourceProgram fn same R step domain)
    (embedded : sourceProgram.Embeds map targetProgram) :
    Contract targetProgram (map.toFun fn) ((map.signature_eq fn).trans same)
      R step domain := by
  simpa only [Contract, cast_cast] using
    RepresentedFunction.Refines.renameCalls embedded callee

/-- The actual relocated callback reuses its original function contract. -/
theorem callee_contract {α : Type u} {R : Representation α accTy}
    (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind)
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (callee : Contract source fn same R step domain) :
    Contract (program source fn same) (calleeEntry accTy kind fn)
      (callee_signature same) R step domain :=
  callee.renameCalls (program_embeds source fn same)

/-- The callable entry returns native folded contents. The original list stays
observable in the actual final heap even when callbacks allocate or mutate
other source objects. -/
theorem program_total {α : Type u} {R : Representation α accTy}
    {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (callee : Contract source fn same R step domain)
    (initial : α) (values : List (CellValue kind))
    (allowed : Admissible step domain initial values) :
    FunctionTotal (program source fn same) (entry accTy kind signatures)
      (fun args heap => R.Rel initial args.head heap ∧
        (Representation.list kind).Rel values args.tail.head heap)
      (fun args heap result finish => R.Rel (values.foldl step initial) result finish ∧
        (Representation.list kind).Rel values args.tail.head finish ∧
        heap.ShapeExtends finish) := by
  apply FunctionTotal.of_wp
  refine (Env.forall_cons (τ := accTy) (Γ := [.option (.node kind)]) _).mpr ?_
  intro accumulator
  refine (Env.forall_cons (τ := .option (.node kind)) (Γ := []) _).mpr ?_
  intro root
  refine (Env.forall_nil _).mpr ?_
  rintro heap ⟨accObserved, listObserved⟩
  rw [program_body]
  exact body_total (callee_contract source fn same callee)
    initial values accumulator root heap allowed accObserved listObserved

/-- Mathematical accumulator/list arguments and an observed accumulator result. -/
def representation {α : Type u} (R : Representation α accTy) (kind : CellTy) :
    FunctionRepresentation (α × List (CellValue kind)) (fun _ => α)
      (foldSignature accTy kind) :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons R (ArgumentRepresentation.single (Representation.list kind)))
    (fun _ => R)

/-- The same callable source program refines ordinary `List.foldl`. Only the
callback's mathematical domain is required along the actual fold prefixes. -/
theorem program_refines {α : Type u} {R : Representation α accTy}
    {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (callee : Contract source fn same R step domain) :
    RepresentedFunction.Refines (program source fn same) (entry accTy kind signatures)
      (representation R kind) (fun input => Admissible step domain input.1 input.2)
      (fun input => input.2.foldl step input.1) := by
  intro input allowed
  apply (program_total callee input.1 input.2 allowed).consequence
    (fun _ _ observed => observed)
  intro args heap result finish _ property
  exact property.1

end Complexity.Language.List.Fold
