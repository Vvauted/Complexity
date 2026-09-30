/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Preservation
import Init.Data.Array.Zip

/-!
# Arrays with product elements

An array of pairs can use two column representations at the same heap. Both
columns observe projections of the same array, so their lengths agree; unequal
columns cannot silently denote a truncated zip. This composition also applies
to nested products once their component arrays have representations.

The view describes storage, not a free conversion or an executable array
operation. It permits aliases. Writes need additional frame/separation facts;
ordinary heap-shape extension alone does not preserve mutable contents.
-/

namespace Complexity.Language.Representation

universe u v

variable {α : Type u} {β : Type v} {τ σ : Ty}

/-- Splitting the fields loses no element or length information. This is a
mathematical view, not an in-program preprocessing operation. -/
def arrayUnzip : Array (α × β) ↪ Array α × Array β where
  toFun xs := (xs.map Prod.fst, xs.map Prod.snd)
  inj' := by
    intro xs ys same
    have first := congrArg Prod.fst same
    have second := congrArg Prod.snd same
    exact (Array.zip_of_prod first second).trans
      (by simpa only [Array.fst_unzip, Array.snd_unzip] using Array.zip_unzip ys)

/-- Compose two actual column observations into an ordinary array of pairs.
Both fields use the current heap; no ownership or separation is inferred. -/
def arrayProd (left : Representation (Array α) τ) (right : Representation (Array β) σ) :
    Representation (Array (α × β)) (.prod τ σ) :=
  (left.prod right).comap arrayUnzip

@[simp] theorem arrayProd_rel (left : Representation (Array α) τ)
    (right : Representation (Array β) σ) (xs : Array (α × β))
    (value : Value (.prod τ σ)) (heap : Heap) :
    (arrayProd left right).Rel xs value heap ↔
      left.Rel (xs.map Prod.fst) value.1 heap ∧
        right.Rel (xs.map Prod.snd) value.2 heap := Iff.rfl

/-- Product arrays retain their observations exactly when both supplied
component frames do; the components may share storage. -/
theorem Preserves.arrayProd {left : Representation (Array α) τ}
    {right : Representation (Array β) σ} {initial finish : Heap}
    (first : left.Preserves initial finish) (second : right.Preserves initial finish) :
    (arrayProd left right).Preserves initial finish :=
  Preserves.comap arrayUnzip (Preserves.prod first second)

/-- Two scalar columns representing one array have the same observed extent,
including when the array is empty or the views have nonzero offsets. -/
theorem arrayProd_lengths {left right : CellTy}
    {xs : Array (CellValue left × CellValue right)}
    {value : Buffer left × Buffer right} {heap : Heap}
    (observed : (arrayProd (array left) (array right)).Rel xs value heap) :
    value.1.length = xs.size ∧ value.2.length = xs.size := by
  exact ⟨by simpa [arrayUnzip] using observed.1.size_eq.symm,
    by simpa [arrayUnzip] using observed.2.size_eq.symm⟩

end Complexity.Language.Representation
