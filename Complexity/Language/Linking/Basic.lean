/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic

/-!
# Typed source function-table embeddings

`SignatureMap` preserves each selected function's complete signature. `Stmt.renameCalls`
changes only function references, retaining the source statement's locals, result type and
operations. `Program.Embeds` requires the target table to contain the renamed source bodies;
it does not replace them with host functions or assumed specifications.

Dependent transport is confined to constructing calls and observing a mapped function body.
The execution and contract transfer theorems live in the semantic linking modules.
-/

namespace Complexity.Language

/-- A function-table map preserving the parameter types and result type of each call. -/
structure SignatureMap (source target : List Signature) where
  toFun : Fin source.length → Fin target.length
  signature_eq (fn : Fin source.length) : target[toFun fn] = source[fn]

namespace SignatureMap

/-- Keep every function in the same signature table. -/
def refl (signatures : List Signature) : SignatureMap signatures signatures where
  toFun := id
  signature_eq _ := rfl

/-- Compose signature-preserving function-table maps. -/
def trans {source middle target : List Signature}
    (first : SignatureMap source middle) (second : SignatureMap middle target) :
    SignatureMap source target where
  toFun fn := second.toFun (first.toFun fn)
  signature_eq fn := (second.signature_eq (first.toFun fn)).trans (first.signature_eq fn)

/-- Include the left signature table in an appended table. -/
def appendLeft (left right : List Signature) : SignatureMap left (left ++ right) where
  toFun fn :=
    (fn.castAdd right.length).cast (List.length_append (as := left) (bs := right)).symm
  signature_eq fn := by
    change (left ++ right)[fn.val] = left[fn.val]
    exact List.getElem_append_left fn.isLt

/-- Include the right signature table in an appended table. -/
def appendRight (left right : List Signature) : SignatureMap right (left ++ right) where
  toFun fn :=
    (fn.natAdd left.length).cast (List.length_append (as := left) (bs := right)).symm
  signature_eq fn := by
    change (left ++ right)[left.length + fn.val] = right[fn.val]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]

end SignatureMap

namespace Stmt

/-- Construct a call using a proved equality of complete signatures. The equality only
transports the call operands and result-binding type; it changes no executable operation. -/
def callOfEq {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (fn : Fin signatures.length) {signature : Signature}
    (same : signatures[fn] = signature) (args : Args Γ signature.params)
    (continuation : Stmt signatures (signature.result :: Γ) result) :
    Stmt signatures Γ result :=
  .call fn
    (cast (congrArg (fun signature => Args Γ signature.params) same.symm) args)
    (cast (congrArg
      (fun signature => Stmt signatures (signature.result :: Γ) result) same.symm)
      continuation)

/-- Rename function references without changing local bindings, heap operations or control flow. -/
def renameCalls {source target : List Signature} (map : SignatureMap source target) :
    {Γ : List Ty} → {result : Ty} → Stmt source Γ result → Stmt target Γ result
  | _, _, .skip => .skip
  | _, _, .assign target value => .assign target value
  | _, _, .letPrim value continuation => .letPrim value (continuation.renameCalls map)
  | _, _, .read buffer index continuation => .read buffer index (continuation.renameCalls map)
  | _, _, .write buffer index value => .write buffer index value
  | _, _, .slice buffer offset length continuation =>
      .slice buffer offset length (continuation.renameCalls map)
  | _, _, .call fn args continuation =>
      callOfEq (map.toFun fn) (map.signature_eq fn) args (continuation.renameCalls map)
  | _, _, .seq first second => .seq (first.renameCalls map) (second.renameCalls map)
  | _, _, .ite condition yes no => .ite condition (yes.renameCalls map) (no.renameCalls map)
  | _, _, .while guard body => .while (guard.renameCalls map) (body.renameCalls map)
  | _, _, .ret value => .ret value

/-- Renaming a transported call composes its existing signature equality with the map. -/
theorem renameCalls_callOfEq {source target : List Signature}
    (map : SignatureMap source target) {Γ : List Ty} {result : Ty}
    (fn : Fin source.length) {signature : Signature} (same : source[fn] = signature)
    (args : Args Γ signature.params)
    (continuation : Stmt source (signature.result :: Γ) result) :
    (callOfEq fn same args continuation).renameCalls map =
      callOfEq (map.toFun fn) ((map.signature_eq fn).trans same) args
        (continuation.renameCalls map) := by
  cases same
  rfl

/-- The identity table map preserves the original statement. -/
@[simp] theorem renameCalls_refl {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (statement : Stmt signatures Γ result) :
    statement.renameCalls (SignatureMap.refl signatures) = statement := by
  induction statement <;> simp_all [renameCalls, SignatureMap.refl, callOfEq]

/-- Successive table renamings are a single composed renaming. -/
theorem renameCalls_trans {source middle target : List Signature}
    (first : SignatureMap source middle) (second : SignatureMap middle target)
    {Γ : List Ty} {result : Ty} (statement : Stmt source Γ result) :
    (statement.renameCalls first).renameCalls second =
      statement.renameCalls (first.trans second) := by
  induction statement <;>
    simp_all only [renameCalls, renameCalls_callOfEq, SignatureMap.trans]

/-- Renaming commutes with transport of the whole parameter/result signature. -/
theorem renameCalls_cast {source target : List Signature} (map : SignatureMap source target)
    {first second : Signature} (same : first = second)
    (statement : Stmt source first.params first.result) :
    (cast (congrArg (fun signature => Stmt source signature.params signature.result) same)
      statement).renameCalls map =
      cast (congrArg (fun signature => Stmt target signature.params signature.result) same)
        (statement.renameCalls map) := by
  cases same
  rfl

end Stmt

namespace SignatureMap

/-- Observe a mapped target body at its original complete source signature. -/
def body {source target : List Signature} (map : SignatureMap source target)
    (program : Program target) (fn : Fin source.length) :
    Stmt target source[fn].params source[fn].result :=
  cast (congrArg (fun signature => Stmt target signature.params signature.result)
    (map.signature_eq fn)) (program.body (map.toFun fn))

/-- Body transport along a composed table map is successive signature transport. -/
theorem body_trans {source middle target : List Signature}
    (first : SignatureMap source middle) (second : SignatureMap middle target)
    (program : Program target) (fn : Fin source.length) :
    (first.trans second).body program fn =
      cast (congrArg (fun signature => Stmt target signature.params signature.result)
        (first.signature_eq fn)) (second.body program (first.toFun fn)) := by
  simp only [body, trans, cast_cast]

end SignatureMap

/-- The target table contains the actual renamed bodies of the source program. -/
def Program.Embeds {source target : List Signature} (sourceProgram : Program source)
    (map : SignatureMap source target) (targetProgram : Program target) : Prop :=
  ∀ fn, map.body targetProgram fn = (sourceProgram.body fn).renameCalls map

namespace Program.Embeds

/-- Every program embeds into its own table without changing calls. -/
theorem refl {signatures : List Signature} (program : Program signatures) :
    program.Embeds (SignatureMap.refl signatures) program := by
  intro fn
  rw [Stmt.renameCalls_refl]
  rfl

/-- Compose actual function-body embeddings through an intermediate program. -/
theorem trans {source middle target : List Signature}
    {sourceProgram : Program source} {middleProgram : Program middle}
    {targetProgram : Program target} {first : SignatureMap source middle}
    {second : SignatureMap middle target}
    (left : sourceProgram.Embeds first middleProgram)
    (right : middleProgram.Embeds second targetProgram) :
    sourceProgram.Embeds (first.trans second) targetProgram := by
  intro fn
  rw [SignatureMap.body_trans, right]
  rw [← Stmt.renameCalls_cast second (first.signature_eq fn)]
  change (first.body middleProgram fn).renameCalls second = _
  rw [left, Stmt.renameCalls_trans]

end Program.Embeds

namespace Program

/-- Combine two closed source tables, renaming every body's internal calls into the
combined table. No entry function is executed, and neither table acquires new call edges. -/
def link {left right : List Signature} (leftProgram : Program left)
    (rightProgram : Program right) : Program (left ++ right) where
  body fn := by
    refine Fin.addCases
      (motive := fun index : Fin (left.length + right.length) =>
        Stmt (left ++ right)
          (left ++ right)[index.cast (List.length_append (as := left) (bs := right)).symm].params
          (left ++ right)[index.cast (List.length_append (as := left) (bs := right)).symm].result)
      ?_ ?_ (fn.cast (List.length_append (as := left) (bs := right)))
    · intro index
      exact cast (congrArg
        (fun signature => Stmt (left ++ right) signature.params signature.result)
        ((SignatureMap.appendLeft left right).signature_eq index).symm)
        ((leftProgram.body index).renameCalls (SignatureMap.appendLeft left right))
    · intro index
      exact cast (congrArg
        (fun signature => Stmt (left ++ right) signature.params signature.result)
        ((SignatureMap.appendRight left right).signature_eq index).symm)
        ((rightProgram.body index).renameCalls (SignatureMap.appendRight left right))

/-- Linking retains every actual left-hand function body with its calls renamed. -/
theorem embeds_link_left {left right : List Signature} (leftProgram : Program left)
    (rightProgram : Program right) :
    leftProgram.Embeds (SignatureMap.appendLeft left right) (leftProgram.link rightProgram) := by
  intro fn
  simp [SignatureMap.body, link, SignatureMap.appendLeft]

/-- Linking retains every actual right-hand function body with its calls renamed. -/
theorem embeds_link_right {left right : List Signature} (leftProgram : Program left)
    (rightProgram : Program right) :
    rightProgram.Embeds (SignatureMap.appendRight left right) (leftProgram.link rightProgram) := by
  intro fn
  dsimp only [SignatureMap.body, link, SignatureMap.appendRight]
  change cast _ (Fin.addCases
    (motive := fun index : Fin (left.length + right.length) =>
      Stmt (left ++ right)
        (left ++ right)[index.cast (List.length_append (as := left) (bs := right)).symm].params
        (left ++ right)[index.cast (List.length_append (as := left) (bs := right)).symm].result)
    _ _ (Fin.natAdd left.length fn)) = _
  rw [Fin.addCases_right]
  simp only [cast_cast, cast_eq]

end Program

end Complexity.Language
