/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Space.Basic

/-!
# Changing the size parameter of a verified RAM space bound

The fixed code, legal domain and exact machine-space observation are unchanged.
The old size must still tend to infinity along the new size filter; otherwise
an eventual old-size bound need not transfer.
-/

namespace Ram.UniformSpaceBigO

variable {Input : Type} {code : Code}
variable {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
variable {size newSize : Input → Nat} {post : ∀ w, Input → State w → Prop}
variable {growth newGrowth : Nat → Nat}

theorem reparam (h : UniformSpaceBigO code encode admissible size post growth)
    (hsize : Filter.Tendsto (fun i : LegalInput admissible => size i.val.2)
      (inputSizeFilter admissible newSize) Filter.atTop)
    (hgrowth : Asymptotics.IsBigO (inputSizeFilter admissible newSize)
      (fun i => (growth (size i.val.2) : ℝ))
      (fun i => (newGrowth (newSize i.val.2) : ℝ))) :
    UniformSpaceBigO code encode admissible newSize post newGrowth := by
  obtain ⟨steps, runs, hbound⟩ := h
  exact ⟨steps, runs, (hbound.mono hsize.le_comap).trans hgrowth⟩

theorem reparam_of_comp {changeSize : Nat → Nat}
    (h : UniformSpaceBigO code encode admissible (changeSize ∘ newSize) post growth)
    (hsize : Filter.Tendsto changeSize Filter.atTop Filter.atTop)
    (hgrowth : Asymptotics.IsBigO Filter.atTop
      (fun n => (growth (changeSize n) : ℝ)) (fun n => (newGrowth n : ℝ))) :
    UniformSpaceBigO code encode admissible newSize post newGrowth :=
  h.reparam (hsize.comp Filter.tendsto_comap)
    (hgrowth.comp_tendsto Filter.tendsto_comap)

end Ram.UniformSpaceBigO
