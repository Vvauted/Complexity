/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Array

/-!
# Optional arrays through presence and payload columns

An optional element has an explicit presence flag and a payload. An absent
element uses the specified canonical default payload; `none` and `some default`
remain different because their flags differ. Both columns observe the same
array, so no element is dropped and scalar column lengths agree.

This is a mathematical storage view, not a free executable encoding or decoder.
Constructing, reading and updating these columns require actual source operations
and their own costs. The scalar `Representation.option` is unchanged. The view
permits aliases; writes need additional separation or alias-update proofs.
-/

namespace Complexity.Language.Representation

universe u

variable {α : Type u} {τ : Ty}

/-- Canonical column fields. Absence still has a physical default payload. -/
def optionEmbedding (default : α) : Option α ↪ Bool × α where
  toFun value := (value.isSome, value.getD default)
  inj' := by
    intro left right same
    cases left <;> cases right <;> simp_all

@[simp] theorem optionEmbedding_none (default : α) :
    optionEmbedding default none = (false, default) := rfl

@[simp] theorem optionEmbedding_some (default value : α) :
    optionEmbedding default (some value) = (true, value) := rfl

@[simp] theorem optionEmbedding_fst (default : α) (value : Option α) :
    (optionEmbedding default value).1 = value.isSome := rfl

@[simp] theorem optionEmbedding_snd (default : α) (value : Option α) :
    (optionEmbedding default value).2 = value.getD default := rfl

/-- The mathematical branch implemented by an actual optional-element reader. -/
def optionUnpack (fields : Bool × α) : Option α :=
  if fields.1 then some fields.2 else none

@[simp] theorem optionUnpack_false (value : α) :
    optionUnpack (false, value) = none := rfl

@[simp] theorem optionUnpack_true (value : α) :
    optionUnpack (true, value) = some value := rfl

@[simp] theorem optionUnpack_optionEmbedding (default : α) (value : Option α) :
    optionUnpack (optionEmbedding default value) = value := by
  cases value <;> rfl

/-- Packing after unpacking normalizes the absent payload; it is not an
inverse on arbitrary pairs with a false flag and noncanonical payload. -/
theorem optionEmbedding_optionUnpack (default : α) (fields : Bool × α) :
    optionEmbedding default (optionUnpack fields) =
      (fields.1, if fields.1 then fields.2 else default) := by
  rcases fields with ⟨flag, value⟩
  cases flag <;> rfl

/-- Packing an actual option uses the represented default only in the absent
branch; a present payload retains its existing observation. -/
theorem optionEmbedding_rel {payload : Representation α τ} {default : α}
    {rawDefault : Value τ} {value : Option α} {actual : Option (Value τ)} {heap : Heap}
    (defaultObserved : payload.Rel default rawDefault heap)
    (observed : payload.option.Rel value actual heap) :
    (bool.prod payload).Rel (optionEmbedding default value)
      (optionEmbedding rawDefault actual) heap := by
  cases value with
  | none =>
      cases actual with
      | none => exact ⟨rfl, defaultObserved⟩
      | some raw => exact False.elim observed
  | some value =>
      cases actual with
      | none => exact False.elim observed
      | some raw => exact ⟨rfl, observed⟩

/-- The actual optional return is observed by the existing scalar option
relation after branching on its actual flag. No absent payload is exposed. -/
theorem optionUnpack_rel {payload : Representation α τ} {default : α}
    {value : Option α} {fields : Bool × Value τ} {heap : Heap}
    (observed : (bool.prod payload).Rel (optionEmbedding default value) fields heap) :
    payload.option.Rel value (optionUnpack fields) heap := by
  cases value with
  | none =>
      have flag : false = fields.1 := observed.1
      simp [optionUnpack, ← flag]
  | some value =>
      have flag : true = fields.1 := observed.1
      simpa [optionUnpack, ← flag] using observed.2

/-- Presence and payload columns compose at the same actual heap. The payload
representation may itself use multiple scalar columns, as for integer arrays. -/
def arrayOption (default : α) (payload : Representation (Array α) τ) :
    Representation (Array (Option α)) (.prod (.buffer .bool) τ) :=
  (arrayProd (array .bool) payload).comap (optionEmbedding default).arrayMap

@[simp] theorem arrayOption_rel (default : α) (payload : Representation (Array α) τ)
    (values : Array (Option α)) (columns : Buffer .bool × Value τ) (heap : Heap) :
    (arrayOption default payload).Rel values columns heap ↔
      (arrayProd (array .bool) payload).Rel
        (values.map (optionEmbedding default)) columns heap := Iff.rfl

/-- Each absent element retains the default payload at its original index. -/
theorem arrayOption_rel_columns (default : α) (payload : Representation (Array α) τ)
    (values : Array (Option α)) (columns : Buffer .bool × Value τ) (heap : Heap) :
    (arrayOption default payload).Rel values columns heap ↔
      (array .bool).Rel (values.map Option.isSome) columns.1 heap ∧
      payload.Rel (values.map (fun value => value.getD default)) columns.2 heap := by
  simp only [arrayOption_rel, arrayProd_rel, Array.map_map, Function.comp_def,
    optionEmbedding_fst, optionEmbedding_snd]

/-- The presence column records the complete extent, including an empty array. -/
theorem arrayOption_size {default : α} {payload : Representation (Array α) τ}
    {values : Array (Option α)} {columns : Buffer .bool × Value τ} {heap : Heap}
    (observed : (arrayOption default payload).Rel values columns heap) :
    values.size = columns.1.length := by
  have flags := (arrayOption_rel_columns default payload values columns heap).mp observed
  simpa only [Array.size_map] using flags.1.size_eq

/-- A scalar payload has exactly the same number of cells as the presence
column. Unequal lengths cannot denote a silently truncated optional array. -/
theorem arrayOption_lengths {kind : CellTy} {default : CellValue kind}
    {values : Array (Option (CellValue kind))}
    {columns : Buffer .bool × Buffer kind} {heap : Heap}
    (observed : (arrayOption default (array kind)).Rel values columns heap) :
    columns.1.length = values.size ∧ columns.2.length = values.size := by
  have lengths := arrayProd_lengths observed
  simpa only [Function.Embedding.arrayMap, Function.Embedding.coeFn_mk,
    Array.size_map] using lengths

/-- Preserve optional-array observations using explicit frames for both
columns. Heap shape alone is not a mutable-contents preservation argument. -/
theorem Preserves.arrayOption {default : α} {payload : Representation (Array α) τ}
    {initial finish : Heap} (flags : (array .bool).Preserves initial finish)
    (values : payload.Preserves initial finish) :
    (arrayOption default payload).Preserves initial finish :=
  Preserves.comap (optionEmbedding default).arrayMap (Preserves.arrayProd flags values)

end Complexity.Language.Representation
