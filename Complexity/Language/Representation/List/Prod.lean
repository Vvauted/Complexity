/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Preservation
import Init.Data.List.Zip

/-!
# Linked lists with product elements

Two linked field sequences observe the projections of the same mathematical
list. Their lengths therefore agree; unequal chains cannot denote a truncated
zip. For scalar fields each cons allocates two real immutable nodes, retaining
the supplied shared tails. The view itself performs no runtime conversion.
-/

namespace Complexity.Language.Representation

universe u v

variable {α : Type u} {β : Type v} {τ σ : Ty}

/-- Splitting a list's fields loses neither elements nor their order.
This is a mathematical view, not an in-program preprocessing operation. -/
def listUnzip : List (α × β) ↪ List α × List β where
  toFun xs := (xs.map Prod.fst, xs.map Prod.snd)
  inj' := by
    intro xs ys same
    exact (List.zip_of_prod (congrArg Prod.fst same) (congrArg Prod.snd same)).trans
      (by simpa only [List.unzip_fst, List.unzip_snd] using List.zip_unzip ys)

/-- Observe both field chains at the same heap. Sharing is permitted. -/
def listProd (left : Representation (List α) τ) (right : Representation (List β) σ) :
    Representation (List (α × β)) (.prod τ σ) :=
  (left.prod right).comap listUnzip

@[simp] theorem listProd_rel (left : Representation (List α) τ)
    (right : Representation (List β) σ) (xs : List (α × β))
    (value : Value (.prod τ σ)) (heap : Heap) :
    (listProd left right).Rel xs value heap ↔
      left.Rel (xs.map Prod.fst) value.1 heap ∧
        right.Rel (xs.map Prod.snd) value.2 heap := Iff.rfl

/-- Both supplied frames preserve the product-list observation. -/
theorem Preserves.listProd {left : Representation (List α) τ}
    {right : Representation (List β) σ} {initial finish : Heap}
    (first : left.Preserves initial finish) (second : right.Preserves initial finish) :
    (listProd left right).Preserves initial finish :=
  Preserves.comap listUnzip (Preserves.prod first second)

/-- Empty scalar-field chains require no allocation. -/
theorem listProd_nil (left right : CellTy) (heap : Heap) :
    (listProd (list left) (list right)).Rel [] (none, none) heap :=
  ⟨.nil, .nil⟩

/-- Two actual node allocations construct one mathematical pair cons.
The first chain survives the second allocation, and both old tails are shared. -/
theorem listProd_cons {left right : CellTy} (head : CellValue left × CellValue right)
    {values : List (CellValue left × CellValue right)}
    {tail : Option (NodeRef left) × Option (NodeRef right)} {heap : Heap}
    (observed : (listProd (list left) (list right)).Rel values tail heap) :
    let first := heap.cons head.1 tail.1
    let second := first.2.cons head.2 tail.2
    (listProd (list left) (list right)).Rel (head :: values)
      (some first.1, some second.1) second.2 := by
  exact ⟨(Heap.cons_contents head.1 observed.1).mono
      ((heap.cons head.1 tail.1).2.shapeExtends_cons head.2 tail.2),
    Heap.cons_contents head.2
      (observed.2.mono (heap.shapeExtends_cons head.1 tail.1))⟩

end Complexity.Language.Representation
