/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Computability.Ram.Word
import Init.Data.List.OfFn

/-!
# Fields of source values

Each source type has a fixed number of actual word fields. Encoding enumerates
those fields in order using `List.ofFn`; Unit has no field or dummy word.
The encoding alone does not assert that mathematical fields fit a word.
Register layouts and their exact representation use the same field indices.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The number of actual words used by a source value. -/
@[simp] def fieldCount : Ty → Nat
  | .nat | .bool => 1
  | .unit => 0

/-- The unsigned scalar observation. Unit's zero is not an encoded field. -/
def valueToNat : {τ : Ty} → Value τ → Nat
  | .nat, n => n
  | .bool, b => if b then 1 else 0
  | .unit, _ => 0

/-- The mathematical value of an actual representation field. -/
def valueField : {τ : Ty} → Value τ → Fin (fieldCount τ) → Nat
  | .nat, value, _ => value
  | .bool, value, _ => if value then 1 else 0
  | .unit, _, i => Fin.elim0 i

@[simp] theorem valueField_nat (value : Nat) (i : Fin (fieldCount .nat)) :
    valueField (τ := .nat) value i = value := rfl

@[simp] theorem valueField_bool (value : Bool) (i : Fin (fieldCount .bool)) :
    valueField (τ := .bool) value i = (if value then 1 else 0) := rfl

/-- Encode every actual field, in its declared order. -/
def valueWords (w : Nat) {τ : Ty} (value : Value τ) : List (Word w) :=
  List.ofFn fun i => BitVec.ofNat w (valueField value i)

@[simp] theorem valueWords_length (w : Nat) {τ : Ty} (value : Value τ) :
    (valueWords w value).length = fieldCount τ := List.length_ofFn

/-- Field lookup observes an actual list entry, never an out-of-range default. -/
@[simp] theorem valueWords_getElem (w : Nat) {τ : Ty} (value : Value τ)
    (i : Fin (fieldCount τ)) :
    (valueWords w value)[i.val]'(by simp) =
      BitVec.ofNat w (valueField value i) := List.getElem_ofFn _

@[simp] theorem valueWords_getElem? (w : Nat) {τ : Ty} (value : Value τ)
    (i : Fin (fieldCount τ)) :
    (valueWords w value)[i.val]? = some (BitVec.ofNat w (valueField value i)) := by
  simp only [valueWords, List.getElem?_ofFn, dif_pos i.isLt]

@[simp] theorem valueWords_nat (w : Nat) (value : Nat) :
    valueWords w (τ := .nat) value = [BitVec.ofNat w value] := by
  simp only [valueWords, fieldCount, List.ofFn_succ, List.ofFn_zero, valueField_nat]

@[simp] theorem valueWords_bool (w : Nat) (value : Bool) :
    valueWords w (τ := .bool) value = [BitVec.ofNat w (if value then 1 else 0)] := by
  simp only [valueWords, fieldCount, List.ofFn_succ, List.ofFn_zero, valueField_bool]

@[simp] theorem valueWords_unit (w : Nat) (value : Unit) :
    valueWords w (τ := .unit) value = [] := List.ofFn_zero

end Ram.LanguageCompiler
